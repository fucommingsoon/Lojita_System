import LojitaCtx.Posix.Errno

namespace LojitaCtx.Posix

abbrev Bytes := List UInt8
abbrev Fd := Nat
abbrev OfdId := Nat
abbrev InodeId := Nat
abbrev PipeId := Nat
abbrev PtyId := Nat
abbrev SockId := Nat
abbrev FileMode := Nat

inductive WaitFor where
  | readable | writable
  deriving Repr, Inhabited

def WaitFor.ctorIdx : WaitFor → Nat
  | .readable => 0
  | .writable => 1

deriving instance DecidableEq for WaitFor

inductive Ret (α : Type) where
  | ok (value : α)
  | err (reason : Errno)
  | wouldBlock (event : WaitFor)
  deriving Repr, Inhabited

def Ret.ctorIdx {α : Type} : Ret α → Nat
  | .ok _ => 0
  | .err _ => 1
  | .wouldBlock _ => 2

deriving instance DecidableEq for Ret

structure StepSlice where
  maxBytes : Nat := 65536
  intrBefore : Bool := false
  deriving Repr, DecidableEq, Inhabited

def canonicalSlice : StepSlice := {}

inductive Access where
  | readOnly | writeOnly | readWrite
  deriving Repr, Inhabited

def Access.ctorIdx : Access → Nat
  | .readOnly => 0
  | .writeOnly => 1
  | .readWrite => 2

deriving instance DecidableEq for Access

structure OpenFlags where
  access : Access := .readOnly
  create : Bool := false
  excl : Bool := false
  trunc : Bool := false
  append : Bool := false
  directory : Bool := false
  nofollow : Bool := false
  nonblock : Bool := false
  cloexec : Bool := false
  deriving Repr, DecidableEq, Inhabited

inductive FileKind where
  | regular | directory | symlink | fifo | tty | socket
  deriving Repr, Inhabited

def FileKind.ctorIdx : FileKind → Nat
  | .regular => 0
  | .directory => 1
  | .symlink => 2
  | .fifo => 3
  | .tty => 4
  | .socket => 5

deriving instance DecidableEq for FileKind

structure StatObs where
  ino : InodeId
  kind : FileKind
  mode : FileMode
  nlink : Nat
  size : Nat
  deriving Repr, DecidableEq, Inhabited

inductive Cap where
  | fdIoCap | fsPathCap | ttyCap | netCap | clockCap | envCap | foreignCap (tag : String)

section

/-- Append one character in Lean string-literal syntax. The ASCII escapes
    are decided from code points, so the remaining characters pass through. -/
private def appendQuoted (acc : String) (c : Char) : String :=
  match c.toNat with
  | 9 => acc ++ "\\t"
  | 10 => acc ++ "\\n"
  | 34 => acc ++ "\\\""
  | 92 => acc ++ "\\\\"
  | n =>
    if n ≤ 31 || n == 127 then
      acc ++ String.ofList ['\\', 'x', (n / 16).digitChar, (n % 16).digitChar]
    else acc.push c

-- Use the same character iterator as String.quote and keep the instance local to Cap.
private local instance : Repr String where
  reprPrec s _ := .text (String.Internal.foldl appendQuoted "\"" s ++ "\"")

deriving instance Repr for Cap

end

def Cap.ctorIdx : Cap → Nat
  | .fdIoCap => 0
  | .fsPathCap => 1
  | .ttyCap => 2
  | .netCap => 3
  | .clockCap => 4
  | .envCap => 5
  | .foreignCap _ => 6

deriving instance DecidableEq for Cap

def CoreCaps : List Cap := [.fdIoCap, .fsPathCap, .ttyCap, .netCap, .clockCap, .envCap]

theorem foreign_excluded (tag : String) : Cap.foreignCap tag ∉ CoreCaps := by
  simp [CoreCaps]

end LojitaCtx.Posix
