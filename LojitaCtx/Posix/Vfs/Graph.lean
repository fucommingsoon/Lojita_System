import Std.Data.TreeMap
import LojitaCtx.Posix.Vfs.FileBytes

namespace LojitaCtx.Posix

abbrev Seg := Bytes
abbrev Entries := Std.TreeMap Seg InodeId

inductive InodePayload where
  | reg (data : ByteArray)
  | dir (parent : InodeId) (entries : Entries)
  | symlink (target : Bytes)
  | pipe (id : PipeId)
  | pty (id : PtyId)
  | sock (id : SockId)
  deriving Inhabited

def InodePayload.ctorIdx : InodePayload → Nat
  | .reg _ => 0 | .dir .. => 1 | .symlink _ => 2 | .pipe _ => 3 | .pty _ => 4 | .sock _ => 5

structure Inode where
  payload : InodePayload
  mode : FileMode := 420
  nlink : Nat := 1
  openRefs : Nat := 0
  roLayer : Bool := false
  deriving Inhabited

structure InodeTable where
  nodes : Std.TreeMap InodeId Inode := {}
  nextId : Nat := 2
  deriving Inhabited

def InodeTable.empty : InodeTable :=
  { nodes := ({} : Std.TreeMap Nat Inode).insert 1 {payload := .dir 1 {}, mode := 493, nlink := 2} }

def InodeTable.node (t : InodeTable) (id : InodeId) : Except Errno Inode :=
  t.nodes[id]?.elim (.error .ENOENT) .ok

def InodeTable.put (t : InodeTable) (id : InodeId) (n : Inode) : InodeTable :=
  { t with nodes := t.nodes.insert id n }

def InodeTable.release (t : InodeTable) (id : InodeId) (n : Inode) : InodeTable :=
  if n.openRefs = 0 ∧ n.nlink = 0 then {t with nodes := t.nodes.erase id} else t.put id n

def InodeTable.setOpenRefs (t : InodeTable) (id count : Nat) : InodeTable :=
  match t.nodes[id]? with
  | none => t
  | some n => t.release id {n with openRefs := count}

def InodeTable.directory (t : InodeTable) (id : InodeId) : Except Errno (InodeId × Entries) := do
  let .dir parent entries := (← t.node id).payload | throw .ENOTDIR
  return (parent, entries)

def InodePayload.kind : InodePayload → FileKind
  | .reg _ => .regular | .dir .. => .directory | .symlink _ => .symlink
  | .pipe _ => .fifo | .pty _ => .tty | .sock _ => .socket

def inodeStat (t : InodeTable) (id : InodeId) : Except Errno StatObs := do
  let n ← t.node id
  let size := match n.payload with | .reg b => b.size | .symlink b => b.length | _ => 0
  return ⟨id, n.payload.kind, n.mode, n.nlink, size⟩

def inodeRead (t : InodeTable) (id off count : Nat) : Except Errno Bytes := do
  match (← t.node id).payload with
  | .reg b => return fileRange b off count
  | .dir .. => throw .EISDIR
  | _ => throw .EINVAL

def inodeWrite (t : InodeTable) (id off : Nat) (bs : Bytes) : Except Errno InodeTable := do
  let n ← t.node id
  if n.roLayer then throw .EROFS
  let .reg b := n.payload | throw .EINVAL
  if bs.isEmpty then return t
  return t.put id { n with payload := .reg (replaceBytes b off bs) }

def validSeg (s : Seg) : Bool :=
  !s.isEmpty && s.length ≤ 255 && s != [46] && s != [46,46] &&
    !s.contains 0 && !s.contains 47

end LojitaCtx.Posix
