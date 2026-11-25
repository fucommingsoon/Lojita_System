import LojitaCtx.Posix.Kernel.Independent

namespace LojitaCtx.Posix

open Std.DTreeMap.Internal in
/-- Bound a lookup by the rightmost key, following the same branch as maxKey?. -/
private theorem lookup_le_rightmost {α : Type} (t : Impl Nat (fun _ => α))
    (ordered : t.Ordered) (k : Nat) (found : t.contains k = true) :
    k ≤ t.maxKey?.getD 0 := by
  induction t generalizing k with
  | leaf => cases found
  | inner sz key value left right _ ih =>
    have location : k ≤ key ∨ right.contains k = true := by
      by_cases le : k ≤ key
      · exact Or.inl le
      · have gt := Nat.compare_eq_gt.mpr (Nat.lt_of_not_ge le)
        exact Or.inr (by simpa [Impl.contains,gt] using found)
    cases right with
    | leaf =>
      obtain le | missing := location
      · simpa only [Impl.maxKey?,Option.getD_some] using le
      · cases missing
    | inner n rk rv l r =>
      rw [Impl.maxKey?]
      obtain le | present := location
      · have lt : key < rk := Nat.compare_eq_lt.mp (ordered.compare_right
          (show ⟨rk,rv⟩ ∈ (Impl.inner n rk rv l r).toListModel by simp [Impl.toListModel]))
        exact Nat.le_trans le (Nat.le_trans (Nat.le_of_lt lt) (ih ordered.right rk (by simp [Impl.contains])))
      · exact ih ordered.right k present

private theorem fresh_ne {α : Type} (t : Table α) {k : Nat} (hk : k ∈ t) :
    tableFresh t ≠ k :=
  Nat.ne_of_gt (Nat.lt_succ_of_le (lookup_le_rightmost t.inner.inner t.inner.wf.ordered k hk))

private theorem allocates {m n : Machine} {f : OpenFlags} {target : KernelTarget} {fd : Nat}
    (h : m.allocate target f = .ok (fd,n)) :
    Holds n fd (tableFresh m.kernel.ofds) ∧
    ∀ old i, Holds m old i → Holds n old i := by
  cases hf : (List.range (min m.proc.limit (m.fds.size+1))).find? (!m.fds.contains ·) with
  | none => simp [Machine.allocate,hf] at h
  | some fd' =>
    simp [Machine.allocate,hf] at h
    obtain ⟨rfl,rfl⟩ := h
    refine ⟨⟨⟨tableFresh m.kernel.ofds,f.cloexec⟩, ?_, rfl⟩, ?_⟩
    · simp [Machine.fds,Machine.setFds,Machine.setDesc]
    · intro old i held
      obtain ⟨e,he,hi⟩ := held
      have miss := List.find?_some hf
      have neq : fd ≠ old := by
        intro eq
        subst old
        simp [Std.TreeMap.contains_eq_isSome_getElem?,he] at miss
      exact ⟨e,by simpa [Machine.fds,Machine.setFds,Machine.setDesc,Std.TreeMap.getElem?_insert,neq] using he,hi⟩

/-- Every successful path open gets a new description even if the inode is
    already held, and preserves every formerly held descriptor binding. -/
theorem open_new_description {m n : Machine} {sl : StepSlice} {fd mode : Nat}
    {dir : DirFd} {path : Bytes} {f : OpenFlags}
    (h : stepSyscall m sl (.openat dir path f mode) = (.ok fd,n)) :
    ∃ id, Holds n fd id ∧ (∀ old ∈ m.kernel.ofds, id ≠ old) ∧
      ∀ other j, Holds m other j → Holds n other j := by
  simp only [stepSyscall,dispatchSyscall,openPath] at h
  by_cases space : m.fds.size ≥ m.proc.limit
  · simp [space,Bind.bind,Except.bind,throw,throwThe,MonadExceptOf.throw] at h
  · cases hd : m.dirStart dir path with
    | error e => simp [space,hd,Bind.bind,Except.bind] at h
    | ok start =>
      cases hv : vfsOpenat m.kernel.vfs m.proc.root start path f (mode &&& (511-m.proc.umask)) with
      | error e => simp [space,hd,hv,Bind.bind,Except.bind] at h
      | ok pair =>
        obtain ⟨ino,table⟩ := pair
        cases ha : (m.setVfs table).allocate (.inode ino) f with
        | error e => simp [space,hd,hv,ha,Bind.bind,Except.bind] at h
        | ok result =>
          obtain ⟨k,next⟩ := result
          cases hl : fdLinks next.proc next.kernel.ofds <;>
            simp [space,hd,hv,ha,hl,Bind.bind,Except.bind,Pure.pure,Except.pure] at h
          cases h
          obtain ⟨fresh,preserved⟩ := allocates ha
          exact ⟨_,fresh,fun _ hk => fresh_ne _ hk,preserved⟩

end LojitaCtx.Posix
