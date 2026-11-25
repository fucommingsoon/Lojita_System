namespace LojitaCtx.Posix

inductive Errno where
  | ENOENT | EINTR | EIO | EBADF | EAGAIN | EACCES | EEXIST | EXDEV
  | ENOTDIR | EISDIR | EINVAL | EMFILE | ENOSPC | ESPIPE | EROFS
  | EPIPE | ENAMETOOLONG | ENOTEMPTY | ELOOP | ECONNREFUSED | ETIMEDOUT
  | EPERM | ENOTTY | ENXIO | ERANGE | EOPNOTSUPP | ENOTCONN | EISCONN | ENOTSOCK | other (number : Nat)
  deriving Repr, Inhabited

def Errno.ctorIdx : Errno → Nat
  | .ENOENT => 0
  | .EINTR => 1
  | .EIO => 2
  | .EBADF => 3
  | .EAGAIN => 4
  | .EACCES => 5
  | .EEXIST => 6
  | .EXDEV => 7
  | .ENOTDIR => 8
  | .EISDIR => 9
  | .EINVAL => 10
  | .EMFILE => 11
  | .ENOSPC => 12
  | .ESPIPE => 13
  | .EROFS => 14
  | .EPIPE => 15
  | .ENAMETOOLONG => 16
  | .ENOTEMPTY => 17
  | .ELOOP => 18
  | .ECONNREFUSED => 19
  | .ETIMEDOUT => 20
  | .EPERM => 21
  | .ENOTTY => 22
  | .ENXIO => 23
  | .ERANGE => 24
  | .EOPNOTSUPP => 25
  | .ENOTCONN => 26 | .EISCONN => 27 | .ENOTSOCK => 28 | .other _ => 29

def Errno.code : Errno → Nat
  | .EPERM => 1 | .ENOENT => 2 | .EINTR => 4 | .EIO => 5 | .ENXIO => 6
  | .EBADF => 9 | .EAGAIN => 11 | .EACCES => 13 | .EEXIST => 17 | .EXDEV => 18
  | .ENOTDIR => 20 | .EISDIR => 21 | .EINVAL => 22 | .EMFILE => 24 | .ENOTTY => 25
  | .ENOSPC => 28 | .ESPIPE => 29 | .EROFS => 30 | .EPIPE => 32 | .ERANGE => 34
  | .ENAMETOOLONG => 36 | .ENOTEMPTY => 39 | .ELOOP => 40 | .EOPNOTSUPP => 95
  | .ENOTSOCK => 88 | .ENOTCONN => 107 | .EISCONN => 106
  | .ETIMEDOUT => 110 | .ECONNREFUSED => 111
  | .other n => n

def Errno.decode : Nat → Errno
  | 1 => .EPERM
  | 2 => .ENOENT
  | 4 => .EINTR
  | 5 => .EIO
  | 6 => .ENXIO
  | 9 => .EBADF
  | 11 => .EAGAIN
  | 13 => .EACCES
  | 17 => .EEXIST
  | 18 => .EXDEV
  | 20 => .ENOTDIR
  | 21 => .EISDIR
  | 22 => .EINVAL
  | 24 => .EMFILE
  | 25 => .ENOTTY
  | 28 => .ENOSPC
  | 29 => .ESPIPE
  | 30 => .EROFS
  | 32 => .EPIPE
  | 34 => .ERANGE
  | 36 => .ENAMETOOLONG
  | 39 => .ENOTEMPTY
  | 40 => .ELOOP
  | 95 => .EOPNOTSUPP
  | 88 => .ENOTSOCK
  | 107 => .ENOTCONN
  | 106 => .EISCONN
  | 110 => .ETIMEDOUT
  | 111 => .ECONNREFUSED
  | n => .other n

-- Preserve the distinction between a named errno and an explicit .other of the same number.
private def Errno.key (e : Errno) : Bool × Nat :=
  match e with
  | .other n => (true, n)
  | _ => (false, e.code)

private def Errno.ofKey (k : Bool × Nat) : Errno :=
  if k.1 then .other k.2 else .decode k.2

private theorem Errno.ofKey_key (e : Errno) : ofKey e.key = e := by cases e <;> rfl

instance : DecidableEq Errno := fun a b =>
  decidable_of_iff (a.key = b.key)
    ⟨fun h => by simpa only [Errno.ofKey_key] using congrArg Errno.ofKey h, congrArg Errno.key⟩

abbrev Errno.EWOULDBLOCK := Errno.EAGAIN

end LojitaCtx.Posix
