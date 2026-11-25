import LojitaCtx.Posix.Kernel.WriteView

namespace LojitaCtx.Posix

private theorem links_setDesc {m : Machine} (h : fdLinks m.proc m.kernel.ofds)
    (id : Nat) (d : OpenFileDesc) : fdLinks (m.setDesc id d).proc (m.setDesc id d).kernel.ofds := by
  apply List.all_eq_true.mpr
  intro pair mem
  have orig := List.all_eq_true.mp h pair mem
  by_cases eq : id = pair.2.ofd <;> simp_all [Machine.setDesc,fdLinks]

private theorem links_account {m : Machine} (h : fdLinks m.proc m.kernel.ofds) :
    fdLinks m.account.proc m.account.kernel.ofds := by
  apply List.all_eq_true.mpr
  intro pair mem
  exact (account_WF m h).fdLive _ _ (Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp mem)

private theorem actual_read {n : Machine} {fd id ino off : Nat} {d : OpenFileDesc}
    (look : n.lookup fd = .ok (id,d)) (reg : d.target = .inode ino)
    (access : d.flags.access ≠ .writeOnly) (offset : d.offset = off)
    (backed : fdLinks n.proc n.kernel.ofds) (bs : Bytes) (sl : StepSlice)
    (awake : sl.intrBefore = false) (fits : bs.length ≤ max 1 sl.maxBytes)
    (data : inodeRead n.kernel.vfs ino off bs.length = .ok bs) :
    (stepSyscall n sl (.read fd bs.length)).1 = .ok bs := by
  let next := n.setDesc id {d with offset := off+bs.length}
  have raw : dispatchSyscall n sl (.read fd bs.length) = .ok (.ok bs,next) := by
    simp [dispatchSyscall,fdRead,look,reg,access,awake,offset,Nat.min_eq_left fits,data,
      Bind.bind,Except.bind,Pure.pure,Except.pure,Machine.advance,next] <;> rfl
  have hl := links_setDesc backed id {d with offset := off+bs.length}
  simp [stepSyscall,raw,show fdLinks next.proc next.kernel.ofds from hl]

private theorem account_lookup {m : Machine} {fd id : Nat} {d : OpenFileDesc}
    (holds : Holds m fd id) (found : m.kernel.ofds[id]? = some d) :
    m.account.lookup fd = .ok (id,{d with refcnt := fdCount m.proc id}) := by
  obtain ⟨e,he,rfl⟩ := holds
  have mem := Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr he
  have count : 0 < fdCount m.proc e.ofd := List.countP_pos_iff.mpr ⟨(fd,e),mem,by simp⟩
  apply Holds.lookup (show Holds m.account fd e.ofd from ⟨e,he,rfl⟩)
  simp [Machine.account,liveOfds,found,Nat.ne_of_gt count]

/-- A write at the common position of *different* descriptions advances just
    the writer. The subsequent read on the other fd sees exactly the newly
    committed bytes, including when the write filled a hole past EOF. -/
theorem independent_write_read {m n : Machine} {a b i j ino : Nat} {writer reader : OpenFileDesc}
    (src : Holds m a i) (dst : Holds m b j) (distinct : i ≠ j)
    (w : m.kernel.ofds[i]? = some writer) (r : m.kernel.ofds[j]? = some reader)
    (wreg : writer.target = .inode ino) (rreg : reader.target = .inode ino)
    (writable : writer.flags.access ≠ .readOnly) (readable : reader.flags.access ≠ .writeOnly)
    (appendOff : writer.flags.append = false) (offset : reader.offset = writer.offset)
    {old : Inode} {before : ByteArray} (node : m.kernel.vfs.node ino = .ok old)
    (regular : old.payload = .reg before) (linked : old.nlink ≠ 0)
    (data : Bytes) (nonempty : data ≠ []) (sl rd : StepSlice)
    (awake : sl.intrBefore = false) (rdAwake : rd.intrBefore = false)
    (fits : (data.take (max 1 sl.maxBytes)).length ≤ max 1 rd.maxBytes)
    (success : stepSyscall m sl (.write a data) = (.ok (data.take (max 1 sl.maxBytes)).length,n)) :
    let bs := data.take (max 1 sl.maxBytes)
    (stepSyscall n rd (.lseek b 0 .cur)).1 = .ok reader.offset ∧
    (stepSyscall n rd (.read b bs.length)).1 = .ok bs := by
  let bs := data.take (max 1 sl.maxBytes)
  have hbs : bs ≠ [] := by
    cases data <;> simp_all [bs, List.take_eq_nil_iff]
  let look := src.lookup w
  cases written : inodeWrite m.kernel.vfs ino writer.offset bs with
  | error e =>
    have raw : dispatchSyscall m sl (.write a data) = .error e := by
      simp [dispatchSyscall,fdWrite,look,wreg,writable,awake,appendOff,Bind.bind,Except.bind,Pure.pure,Except.pure,bs] at written ⊢
      rw [written]
      rfl
    simp [stepSyscall,raw] at success
  | ok table =>
    let next := (m.setVfs table).setDesc i {writer with offset := writer.offset+bs.length}
    have raw : dispatchSyscall m sl (.write a data) = .ok (.ok bs.length,next) := by
      simp [dispatchSyscall,fdWrite,look,wreg,writable,awake,appendOff,Bind.bind,Except.bind,Pure.pure,Except.pure,
        Machine.advance,next,bs] at written ⊢
      rw [written]
      rfl
    cases h : fdLinks next.proc next.kernel.ofds <;> simp [stepSyscall,raw,h,bs] at success
    subst n
    have previous : next.kernel.ofds[j]? = some reader := by
      simpa [next,Machine.setVfs,Machine.setDesc,Std.TreeMap.getElem?_insert,distinct] using r
    have held : Holds next b j := dst
    have seen := account_lookup held previous
    obtain ⟨changed,existsNode,content,links⟩ := written_inode node regular written hbs
    obtain ⟨final,readableNode,unchanged⟩ := account_linked_payload (m := next) existsNode (by rwa [links])
    have bytes : inodeRead next.account.kernel.vfs ino reader.offset bs.length = .ok bs := by
      simp only [inodeRead,readableNode,Bind.bind,Except.bind,unchanged,content,offset,
        read_replaced,Pure.pure,Except.pure]
    exact ⟨seek_cur seen rreg (links_account h) rd,
      actual_read seen rreg readable rfl (links_account h) bs rd rdAwake fits bytes⟩

end LojitaCtx.Posix
