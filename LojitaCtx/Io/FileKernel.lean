import LojitaCtx.Posix.Kernel
import LojitaCtx.Io.Confluence

namespace LojitaCtx.Io.FsLib
open LojitaCtx.Posix

def FreshFd (m : Machine) (fd : Fd) (n : Machine) : Prop :=
  m.fds[fd]? = none ∧ ∃ e, n.fds = m.fds.insert fd e

private theorem allocate_fresh (m n : Machine) (target : KernelTarget) (flags : OpenFlags)
    (fd : Fd) (h : m.allocate target flags = .ok (fd,n)) : FreshFd m fd n := by
  cases hf : (List.range (min m.proc.limit (m.fds.size+1))).find? (!m.fds.contains ·) with
  | none => simp [Machine.allocate, hf] at h
  | some k =>
    simp [Machine.allocate, hf] at h
    obtain ⟨rfl,rfl⟩ := h
    have notMem := List.find?_some hf
    rw [Std.TreeMap.contains_eq_isSome_getElem?] at notMem
    have miss : m.fds[fd]? = none := by cases hx : m.fds[fd]? <;> simp_all
    exact ⟨miss, _, rfl⟩

theorem open_fresh {m n : Machine} {fd : Fd} {path : Bytes} {sl : StepSlice}
    (h : stepSyscall m sl (.openat none path {} 0) = (.ok fd,n)) : FreshFd m fd n := by
  unfold stepSyscall at h
  simp only [dispatchSyscall, openPath] at h
  by_cases space : m.fds.size ≥ m.proc.limit
  · simp [Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw, space] at h
  · cases hd : m.dirStart none path with
    | error e => simp [Bind.bind, Except.bind, space, hd] at h
    | ok start =>
      cases hv : vfsOpenat m.kernel.vfs m.proc.root start path {} 0 with
      | error e => simp [Bind.bind, Except.bind, space, hd, hv] at h
      | ok result =>
        obtain ⟨ino,table⟩ := result
        cases ha : (m.setVfs table).allocate (.inode ino) {} with
        | error e => simp [Bind.bind, Except.bind, space, hd, hv, ha] at h
        | ok result =>
          obtain ⟨k,next⟩ := result
          cases hl : fdLinks next.proc next.kernel.ofds <;> simp [Bind.bind, Except.bind, Pure.pure, Except.pure, space, hd, hv, ha, hl] at h
          obtain ⟨rfl,rfl⟩ := h
          exact allocate_fresh (m.setVfs table) next (.inode ino) {} _ ha

theorem close_fds {m n : Machine} {fd : Fd} {sl : StepSlice}
    (h : stepSyscall m sl (.close fd) = (.ok (),n)) : n.fds = m.fds.erase fd := by
  let next := m.setFds (m.fds.erase fd)
  cases hd : m.lookup fd with
  | error e =>
    have raw : dispatchSyscall m sl (.close fd) = .error e := by
      simp [dispatchSyscall, hd, discard, Functor.mapConst, Bind.bind, Except.bind, Except.map]
    simp [stepSyscall,raw] at h
  | ok pair =>
    have raw : dispatchSyscall m sl (.close fd) = .ok (.ok (),next) := by
      simp [dispatchSyscall, hd, discard, Functor.mapConst, Bind.bind, Except.bind, Except.map, Pure.pure, Except.pure, next]
    cases hl : fdLinks next.proc next.kernel.ofds <;> simp [stepSyscall,raw,hl] at h
    subst n
    rfl

/-- Conditions observable at the start of a read on a stationary regular file. -/
structure AtRegular (m : Machine) (fd : Fd) (ino : InodeId) (bytes : ByteArray) (off : Nat) : Prop where
  live : ∃ id d node, m.lookup fd = .ok (id,d) ∧ d.target = .inode ino ∧
    d.flags.access ≠ .writeOnly ∧ d.offset = off ∧ m.kernel.vfs.node ino = .ok node ∧ node.payload = .reg bytes

theorem inode_chunk {m : Machine} {fd ino off size} {bytes : ByteArray}
    (file : AtRegular m fd ino bytes off) {sl : StepSlice} {out : Bytes} {next : Machine}
    (h : stepSyscall m sl (.read fd (max 1 size)) = (.ok out,next)) :
    out = (bytes.data.toList.drop off).take (min (max 1 size) (max 1 sl.maxBytes)) ∧
    next.fds = m.fds := by
  obtain ⟨id,d,node,look,target,access,offset,hn,hp⟩ := file.live
  let count := min (max 1 size) (max 1 sl.maxBytes)
  let chunk := fileRange bytes off count
  let nxt := m.advance id d (off+chunk.length) false
  cases hi : sl.intrBefore
  · have hd : dispatchSyscall m sl (.read fd (max 1 size)) = .ok (.ok chunk, nxt) := by
      simp [Bind.bind, Except.bind, Pure.pure, Except.pure, dispatchSyscall, fdRead, look, access, target, hi, offset, count, nxt, chunk, inodeRead, hn, hp] <;> rfl
    cases hl : fdLinks nxt.proc nxt.kernel.ofds <;> simp [stepSyscall,hd,hl] at h
    obtain ⟨hval,rfl⟩ := h
    have same : chunk = out := by first | exact hval | exact Ret.ok.inj hval
    rw [← same]
    exact ⟨by simp [chunk,count], rfl⟩
  · have positive : 0 < max 1 size := by omega
    have hd : dispatchSyscall m sl (.read fd (max 1 size)) = .error .EINTR := by
      simp [Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw, dispatchSyscall, fdRead, look, access, target, hi, positive] <;> rfl
    simp [stepSyscall, hd] at h

end LojitaCtx.Io.FsLib
