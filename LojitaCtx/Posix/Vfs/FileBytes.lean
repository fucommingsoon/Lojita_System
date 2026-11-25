import LojitaCtx.Posix.Types
import Init.Data.ByteArray.Bootstrap

namespace LojitaCtx.Posix

/-- Traverse the requested part of a packed file without unpacking the rest of it. -/
@[specialize] private def foldCount {α : Type} (step : α → UInt8 → α) (src : ByteArray)
    (off : Nat) (acc : α) : (n : Nat) → n ≤ src.size - off → α
  | 0, _ => acc
  | n+1, bound =>
    have valid : off < src.size := Nat.lt_of_sub_pos (Nat.lt_of_lt_of_le (Nat.succ_pos _) bound)
    have remaining : n ≤ src.size - (off+1) := by
      rw [← Nat.sub_sub]
      exact Nat.sub_le_sub_right bound 1
    foldCount step src (off+1) (step acc (src.get off valid)) n remaining

@[inline] private def foldRange {α : Type} (step : α → UInt8 → α) (src : ByteArray)
    (off count : Nat) (acc : α) : α :=
  foldCount step src off acc (min count (src.size-off)) (Nat.min_le_right ..)

private theorem foldCount_eq {α : Type} (step : α → UInt8 → α) (src : ByteArray)
    (off : Nat) (acc : α) (n : Nat) (bound : n ≤ src.size - off) :
    foldCount step src off acc n bound = ((src.data.toList.drop off).take n).foldl step acc := by
  induction n generalizing off acc with
  | zero => rfl
  | succ n ih =>
    have atByte : off < src.data.toList.length :=
      Nat.lt_of_sub_pos (Nat.lt_of_lt_of_le (Nat.succ_pos _) bound)
    rw [foldCount, ih, List.drop_eq_getElem_cons atByte]
    rfl

private theorem foldRange_eq {α : Type} (step : α → UInt8 → α) (src : ByteArray)
    (off count : Nat) (acc : α) :
    foldRange step src off count acc = ((src.data.toList.drop off).take count).foldl step acc := by
  have len : (src.data.toList.drop off).length = src.size-off := List.length_drop
  rw [foldRange,foldCount_eq]
  by_cases within : count ≤ src.size - off
  · rw [Nat.min_eq_left within]
  · have covers := Nat.le_of_not_le within
    rw [Nat.min_eq_right covers,← len,List.take_length,List.take_of_length_le (len ▸ covers)]

def fileRange (src : ByteArray) (off count : Nat) : Bytes :=
  (foldRange (fun acc byte => byte :: acc) src off count []).reverse

@[simp] theorem fileRange_eq (src : ByteArray) (off count : Nat) :
    fileRange src off count = (src.data.toList.drop off).take count := by
  simp only [fileRange,foldRange_eq,List.foldl_flip_cons_eq_append',List.append_nil,List.reverse_reverse]

private def zeroFill (out : ByteArray) : Nat → ByteArray
  | 0 => out
  | n+1 => zeroFill (out.push 0) n

private theorem zeroFill_eq (out : ByteArray) (n : Nat) :
    (zeroFill out n).data.toList = out.data.toList ++ List.replicate n 0 := by
  induction n generalizing out with
  | zero => simp [zeroFill]
  | succ n ih => simp [zeroFill,ih,ByteArray.data_push,List.replicate_succ,List.append_assoc]

private theorem foldPush_eq (xs : Bytes) (out : ByteArray) :
    (xs.foldl ByteArray.push out).data.toList = out.data.toList ++ xs := by
  induction xs generalizing out with
  | nil => simp
  | cons x xs ih => simp [List.foldl_cons,ih,ByteArray.data_push,List.append_assoc]

/-- Replace a span, retaining the existing packed prefix on append and filling any gap with zeros. -/
def replaceBytes (before : ByteArray) (off : Nat) (bs : Bytes) : ByteArray :=
  let pre := if before.size ≤ off then before else
    foldRange ByteArray.push before 0 off (ByteArray.emptyWithCapacity (max before.size (off+bs.length)))
  let out := bs.foldl ByteArray.push (zeroFill pre (off-before.size))
  foldRange ByteArray.push before (off+bs.length) before.size out

theorem replaceBytes_contents (before : ByteArray) (off : Nat) (bs : Bytes) :
    (replaceBytes before off bs).data.toList =
      before.data.toList.take off ++ List.replicate (off-before.size) 0 ++ bs ++
        before.data.toList.drop (off+bs.length) := by
  have n : before.data.toList.length = before.size := rfl
  have suffix : (before.data.toList.drop (off+bs.length)).length ≤ before.size := by
    simp [n]
  rw [replaceBytes,foldRange_eq,foldPush_eq,foldPush_eq,zeroFill_eq,List.take_of_length_le suffix]
  by_cases append : before.size ≤ off
  · rw [ite_eq_left append,List.take_of_length_le (n ▸ append)]
  · rw [ite_eq_right append,foldRange_eq,foldPush_eq]
    rfl

end LojitaCtx.Posix
