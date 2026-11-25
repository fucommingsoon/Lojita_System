module
prelude
public import Init.Data
public import Init.Tactics
public section

namespace Packing

@[noinline] def viaArray {α : Type u} (xs : List α) : Array α :=
  xs.foldl Array.push (Array.emptyWithCapacity 0)

@[noinline] def viaBytes (xs : Array UInt8) : ByteArray :=
  xs.toList.foldl ByteArray.push (ByteArray.emptyWithCapacity 0)

@[noinline] def viaByte (b : BitVec 8) : UInt8 := UInt8.ofNat b.toNat

private theorem foldBytes (xs : List UInt8) (acc : ByteArray) :
    (xs.foldl ByteArray.push acc).data = xs.foldl Array.push acc.data := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih => simpa only [List.foldl_cons, ByteArray.data_push] using ih (acc.push x)

@[csimp] theorem mk_wrap : ByteArray.mk = viaBytes := by
  funext xs
  apply ByteArray.ext
  unfold viaBytes
  rw [foldBytes, List.foldl_push_eq_append']
  cases xs
  simp [ByteArray.emptyWithCapacity]
  rfl

@[csimp] theorem byte_wrap : UInt8.ofBitVec = viaByte := by
  funext b
  apply UInt8.toBitVec_inj.mp
  simp [viaByte, UInt8.ofNat]

@[csimp] theorem array_wrap : @Array.mk = @viaArray := by
  funext α xs
  rw [viaArray, List.foldl_push_eq_append']
  simp [Array.emptyWithCapacity]

end Packing
