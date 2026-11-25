import LojitaCtx.Posix.Kernel
import LojitaCtx.Io.FsLib
import Lojita.Store.TreeCAS.Image

open LojitaCtx.Posix LojitaCtx.Io Lojita.Store.TreeCAS
namespace TwinGates

-- An explicit native errno keeps its identity even when its numeric code is known.
#guard Errno.EPERM != .other 1
#guard Errno.EWOULDBLOCK == .EAGAIN
#guard Errno.other 512 == .other 512 && Errno.other 512 != .other 513

private abbrev Gate := StateT Machine IO
private def b (s : String) := s.toUTF8.data.toList
private def check (ok : Bool) (label : String) : Gate Unit :=
  unless ok do throw <| IO.userError label

private def step (op : SysOp) : Gate (Ret op.Result) := do
  let (r,m) := stepSyscall (← get) canonicalSlice op
  set m
  return r

private def ok (op : SysOp) : Gate op.Result := do
  match ← step op with
  | .ok v => return v
  | .err e => throw <| IO.userError s!"{repr op} returned {repr e}"
  | .wouldBlock _ => throw <| IO.userError s!"{repr op} blocked"

private def error (op : SysOp) (expected : Errno) : Gate Unit := do
  match ← step op with
  | .err actual => check (actual == expected) s!"{repr op}: expected {repr expected}, got {repr actual}"
  | _ => throw <| IO.userError s!"{repr op} did not return {repr expected}"

private def runUser {Δ : List Cap} {A : Type} (p : PosixProg Δ A) : Gate A := do
  let (out,m) := runPrefix (p.observe 128) (← get) (List.replicate 128 canonicalSlice)
  set m
  match out with
  | .done a => return a
  | .suspended => throw <| IO.userError "unexpected suspended user program"

private def create (path : String) : Gate Fd :=
  ok (.openat none (b path) {access := .readWrite, create := true} 420)

private def read (fd count : Nat) : Gate Bytes := ok (.read fd count)
private def write (fd : Fd) (bytes : Bytes) : Gate Nat := ok (.write fd bytes)
private def offset (fd : Fd) : Gate Nat := ok (.lseek fd 0 .cur)

private def halfLine : Gate Unit := do
  let (r,w) ← ok (.pipe2 true false)
  check ((← write w (b "abc")) == 3) "initial fragment"
  let (first,reader) ← runUser (Δ := [.fdIoCap]) (readLine (by simp) {fd := r,chunkSize := 2})
  check (first == .err .EAGAIN && reader.pending == b "abc") "half-open readLine lost its fragment"
  check ((← write w (b "def\n")) == 4) "second fragment"
  let (second,reader) ← runUser (Δ := [.fdIoCap]) (readLine (by simp) reader)
  check (second == .ok (some (b "abcdef\n")) && reader.pending.isEmpty) "resumed readLine"
  discard <| ok (.close w)
  let (eof,_) ← runUser (Δ := [.fdIoCap]) (readLine (by simp) reader)
  check (eof == .ok none) "last writer close should deliver EOF"

private def links : Gate Unit := do
  discard <| ok (.mkdirat none (b "sub") 493)
  discard <| ok (.mkdirat none (b "sub/dir") 493)
  let root ← create "target"
  let localFd ← create "sub/target"
  discard <| ok (.write root (b "root"))
  discard <| ok (.write localFd (b "local"))
  discard <| ok (.symlinkat (b "../target") none (b "sub/dir/lnk"))
  let fd ← ok (.openat none (b "/sub/dir/lnk") {} 0)
  let bytes ← read fd 16
  let rootInfo ← ok (.fstat root)
  let localInfo ← ok (.fstat localFd)
  let followed ← ok (.fstat fd)
  check (bytes == b "local" && followed.ino == localInfo.ino && followed.ino != rootInfo.ino) "relative symlink parent"
  discard <| ok (.symlinkat (b "second") none (b "first"))
  discard <| ok (.symlinkat (b "first") none (b "second"))
  error (.openat none (b "first") {} 0) .ELOOP

private def mkdirs : Gate Unit := do
  error (.mkdirat none (b "a/b") 493) .ENOENT
  error (.fstatat none (b "a") true) .ENOENT
  discard <| ok (.mkdirat none (b "a") 493)
  error (.mkdirat none (b "a") 493) .EEXIST
  let r ← runUser (Δ := [.fsPathCap]) (FsLib.mkdirP (by simp) (b "a/b/c"))
  check (r == .ok ()) "mkdirP existing directory"
  check ((← ok (.fstatat none (b "a/b/c") true)).kind == .directory) "mkdirP result"
  discard <| create "a/file"
  let r ← runUser (Δ := [.fsPathCap]) (FsLib.mkdirP (by simp) (b "a/file/x"))
  check (r == .err .ENOTDIR) "mkdirP swallowed existing regular file"

private def unlinked : Gate Unit := do
  let count := (← get).kernel.vfs.nodes.size
  let fd ← create "tmp.dat"
  let ino := (← ok (.fstat fd)).ino
  discard <| ok (.write fd (b "ok"))
  discard <| ok (.unlinkat none (b "tmp.dat") false)
  error (.openat none (b "tmp.dat") {} 0) .ENOENT
  check ((← ok (.fstat fd)).nlink == 0) "unlinked fd link count"
  discard <| ok (.lseek fd 0 .set)
  check ((← read fd 2) == b "ok") "unlinked file lost data"
  discard <| ok (.close fd)
  let table := (← get).kernel.vfs.nodes
  check (!table.contains ino && table.size == count) "last close leaked nameless inode"
  error (.read fd 1) .EBADF

private def offsets : Gate Unit := do
  let fd ← create "shared"
  discard <| ok (.write fd (b "abc"))
  discard <| ok (.lseek fd 0 .set)
  let alias ← ok (.dup2 fd 8)
  let other ← ok (.openat none (b "shared") {} 0)
  check ((← read fd 1) == b "a") "first read"
  check ((← offset alias) == 1 && (← offset other) == 0) "open and dup offsets"
  discard <| ok (.write alias (b "X"))
  check ((← read other 3) == b "aXc") "independent open must observe shared data"
  check ((← offset fd) == 2) "aliased write offset"
  let .ok rows := freezeVfsToTree (← get).kernel.vfs | throw <| IO.userError "freeze writable tree"
  let .ok ro := mountTreeToVfs (Std.TreeMap.ofList rows) true | throw <| IO.userError "mount readonly tree"
  set (({} : Machine).setVfs ro)
  error (.openat none (b "shared") {access := .writeOnly} 0) .EROFS
  error (.openat none (b "shared") {trunc := true} 0) .EROFS
  error (.openat none (b "new") {create := true} 420) .EROFS
  error (.mkdirat none (b "new") 493) .EROFS
  error (.unlinkat none (b "shared") false) .EROFS
  error (.symlinkat (b "shared") none (b "alias")) .EROFS
  error (.renameat none (b "shared") none (b "moved")) .EROFS
  let readonly ← ok (.openat none (b "shared") {} 0)
  check ((← read readonly 3) == b "aXc") "readonly bytes changed"

private def pageBoundary : Gate Unit := do
  let (r,w) ← ok (.pipe2 true false)
  let m ← get
  let .ok (_,d) := m.lookup w | throw <| IO.userError "missing write end"
  let .pipe id _ := d.target | throw <| IO.userError "expected pipe"
  let some pipe := m.kernel.pipes[id]? | throw <| IO.userError "missing pipe"
  set (m.setPipe id {pipe with cap := 4096})
  let full := List.replicate 4096 (65 : UInt8)
  check ((← write w (66::full)) == 4096) "a large nonblocking write must return its partial count"
  discard <| read r 1
  error (.write w [65]) .EAGAIN
  let masks : List Nat ← ok (.ppoll [⟨w,4⟩] (some 0) false)
  check (masks == [0]) "partially consumed page still occupies its slot"
  discard <| read r 4096
  let masks : List Nat ← ok (.ppoll [⟨w,4⟩] (some 0) false)
  check (masks == [4]) "drained slot becomes writable"
  check ((← write w (full.drop 1)) == 4095) "fresh tail"
  error (.write w [65,66]) .EAGAIN
  check ((← write w [65]) == 1) "one byte fits at the end of a partial page"

private def kernelWrite (m : Machine) (sl : StepSlice) (fd : Fd) (bs : Bytes) : Ret Nat × Machine :=
  stepSyscall m sl (.write fd bs)

private def shortWriteAll : Gate Unit := do
  let (_,w) ← ok (.pipe2 false false)
  discard <| write w [9,8]
  let m ← get
  let .ok (_,d) := m.lookup w | throw <| IO.userError "writer description"
  let .pipe id true := d.target | throw <| IO.userError "writer target"
  let input := (List.range 4099).map Nat.toUInt8
  let writer : BufWriter := {fd := w, remaining := input, written := 5}
  let intr : StepSlice := {intrBefore := true}
  let two : StepSlice := {maxBytes := 2}
  let three : StepSlice := {maxBytes := 3}
  let finish : StepSlice := {maxBytes := 1}
  let (.err .EINTR, retry) := kernelWrite m intr w input | throw <| IO.userError "expected EINTR"
  let (.ok 2, first) := kernelWrite retry two w input | throw <| IO.userError "expected first short write"
  let (.ok 3, _) := kernelWrite first three w (input.drop 2) | throw <| IO.userError "expected second short write"
  let p := writeAll (Δ := [.fdIoCap]) (by simp) writer
  let (.done (.ok (),final),z) := runPrefix (p.observe 4) m [intr,two,three,finish]
    | throw <| IO.userError "writeAll did not finish on four kernel slices"
  let some stream := z.kernel.pipes[id]? | throw <| IO.userError "completed writer lost pipe"
  check (final.written == 4104 && final.remaining.isEmpty && stream.pendingBytes == [9,8] ++ input)
    "writeAll duplicated or lost bytes during retry/short writes"
  set z

private def fileRead : Gate Unit := do
  let fd ← create "stationary"
  discard <| ok (.write fd (b "content"))
  discard <| ok (.close fd)
  let start ← get
  let success ← runUser (Δ := [.fsPathCap,.fdIoCap])
    (FsLib.readFileAll (by simp) (by simp) (b "stationary") 1)
  check (success == .ok (b "content") && (← get).fds.toList == start.fds.toList) "readFileAll acquired fd cleanup"
  set {start with proc := {start.proc with limit := 0}}
  let failure ← runUser (Δ := [.fsPathCap,.fdIoCap])
    (FsLib.readFileAll (by simp) (by simp) (b "stationary") 1)
  check (failure == .err .EMFILE && (← get).fds.isEmpty) "readFileAll exhausted fd acquisition"

/-- Compare the public constructor representation with the stock string formatter. -/
private def checkForeignCapRepr : IO Unit := do
  let checkTag := fun (tag : String) (prec width : Nat) => do
    let fields := Std.Format.text "LojitaCtx.Posix.Cap.foreignCap" ++ Std.Format.line ++ reprArg tag
    let ref := Repr.addAppParen (fields.nest (if prec ≥ 1024 then 1 else 2)).group prec
    unless (reprPrec (Cap.foreignCap tag) prec).pretty width == ref.pretty width do
      throw <| IO.userError "foreignCap repr differs from the standard Lean string representation"
  let ascii := String.ofList ((List.range 128).map Char.ofNat)
  for tag in ["", ascii, "quoted \"é\"\\界\n😀", "LojitaCtx.Posix.Cap.foreignCap"] do
    for prec in [0, 1023, 1024, 1025] do
      for width in [8, 40, 120] do checkTag tag prec width
  checkTag (String.join (List.replicate 25000 "a界\n😀")) 1024 80

def test : IO Unit := do
  checkForeignCapRepr
  for (label,gate) in [("half-open line",halfLine),("relative symlink and ELOOP",links),
                       ("mkdirat and mkdirP",mkdirs),("unlink while open",unlinked),
                       ("shared offsets and readonly tree",offsets),("stationary file and EMFILE",fileRead),
                       ("Linux page occupancy and atomic writes",pageBoundary),
                       ("kernel writeAll across EINTR and short writes",shortWriteAll)] do
    discard <| gate.run {}
    IO.println s!"Twin gate passed: {label}"
end TwinGates

def main := TwinGates.test
