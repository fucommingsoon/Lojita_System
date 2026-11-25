import LojitaCtx.Posix.Kernel.Offsets

namespace LojitaCtx.Posix

/-- Reading the replaced span returns exactly the bytes supplied. -/
theorem read_replaced (before : ByteArray) (off : Nat) (bs : Bytes) :
    fileRange (replaceBytes before off bs) off bs.length = bs := by
  let pre := before.data.toList.take off ++ List.replicate (off-before.size) (0 : UInt8)
  have n : before.data.toList.length = before.size := rfl
  have preLen : pre.length = off := by
    simp only [pre,List.length_append,List.length_take,List.length_replicate,n]
    rw [Nat.add_comm,Nat.sub_add_min_cancel]
  rw [fileRange_eq,replaceBytes_contents]
  change ((pre ++ bs ++ _).drop off).take bs.length = bs
  rw [List.append_assoc,← preLen,List.drop_left,List.take_left]

theorem written_inode {t next : InodeTable} {ino off : Nat} {old : Inode} {before : ByteArray}
    {bs : Bytes} (reg : t.node ino = .ok old) (kind : old.payload = .reg before)
    (written : inodeWrite t ino off bs = .ok next) (nonempty : bs ≠ []) :
    ∃ node, next.nodes[ino]? = some node ∧ node.payload = .reg (replaceBytes before off bs) ∧ node.nlink = old.nlink := by
  by_cases ro : old.roLayer
  · simp [inodeWrite,reg,ro,Bind.bind,Except.bind,throw,throwThe,MonadExceptOf.throw] at written
  · have hbs : bs.isEmpty = false := List.isEmpty_eq_false_iff.mpr nonempty
    simp [inodeWrite,reg,kind,ro,hbs,Bind.bind,Except.bind,Pure.pure,Except.pure] at written
    subst next
    exact ⟨{old with payload := .reg (replaceBytes before off bs)},by simp [InodeTable.put,ro],rfl,rfl⟩

/-- Normalizing the descriptor counts does not change the payload of a linked inode. -/
theorem account_linked_payload {m : Machine} {node : Inode} {ino : Nat}
    (hn : m.kernel.vfs.nodes[ino]? = some node) (linked : node.nlink ≠ 0) :
    ∃ after, m.account.kernel.vfs.node ino = .ok after ∧ after.payload = node.payload := by
  let count := targetCount (liveOfds m.proc m.kernel.ofds) (.inode ino)
  refine ⟨{node with openRefs := count}, ?_,rfl⟩
  simp [Machine.account,liveInodes,InodeTable.node,Std.TreeMap.getElem?_filterMap',hn,linked,count]

end LojitaCtx.Posix
