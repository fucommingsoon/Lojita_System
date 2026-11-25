module
prelude
public import Init.Data
public import Init.Tactics
public section

namespace G1Arithmetic

/-- Twice the larger operand bounds the sum. Three bounded subtractions
    compute the sum without counting up one successor per input unit. -/
@[noinline] def add (a b : @& Nat) : Nat :=
  let top := (max a b) <<< 1
  top - ((top - a) - b)

theorem add_eq (a b : Nat) : add a b = a + b := by
  have bound := Nat.add_le_add (Nat.le_max_left a b) (Nat.le_max_right a b)
  simpa only [add, Nat.shiftLeft_eq, Nat.pow_one, Nat.mul_two, Nat.sub_sub] using
    Nat.sub_sub_self bound

private def mulLoop (a n acc : Nat) : Nat :=
  if h : n = 0 then acc
  else mulLoop (a <<< 1) (n / 2) (if n % 2 = 0 then acc else add acc a)
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero (by assumption)) (by decide)

private theorem mulLoop_eq (a n acc : Nat) : mulLoop a n acc = acc + a * n := by
  rw [mulLoop]
  split
  · rename_i h; simp [h]
  · rename_i hn
    rw [mulLoop_eq, Nat.shiftLeft_eq, Nat.pow_one, Nat.mul_two]
    have bits := Nat.mod_add_div n 2
    split
    · rename_i hz
      conv => rhs; rw [← bits]
      simp [hz, Nat.two_mul, Nat.mul_add, Nat.add_mul]
    · rename_i hz
      have one : n % 2 = 1 := (Nat.mod_two_eq_zero_or_one n).resolve_left hz
      conv => rhs; rw [← bits]
      simp [one, add_eq, Nat.mul_add, Nat.two_mul, Nat.add_mul, Nat.add_assoc]
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero (by assumption)) (by decide)

@[noinline] def mul (a b : @& Nat) : Nat := mulLoop a b 0

theorem mul_eq (a b : Nat) : mul a b = a * b := by simp [mul, mulLoop_eq]

private def powLoop (a n acc : Nat) : Nat :=
  if h : n = 0 then acc
  else if n = 1 then mul acc a
  else powLoop (mul a a) (n / 2) (if n % 2 = 0 then acc else mul acc a)
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero (by assumption)) (by decide)

private theorem powLoop_eq (a n acc : Nat) : powLoop a n acc = acc * a ^ n := by
  rw [powLoop]
  split
  · rename_i h; simp [h]
  · rename_i hn
    split
    · rename_i h; simp [h, mul_eq]
    · rw [powLoop_eq]
      have bits := Nat.mod_add_div n 2
      split
      · rename_i hz
        conv => rhs; rw [← bits]
        simp [hz, mul_eq, Nat.pow_mul, Nat.pow_two]
      · rename_i hz
        have one : n % 2 = 1 := (Nat.mod_two_eq_zero_or_one n).resolve_left hz
        conv => rhs; rw [← bits]
        simp [one, mul_eq, Nat.pow_add, Nat.pow_mul, Nat.pow_two, Nat.mul_assoc]
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero (by assumption)) (by decide)

@[noinline] def pow (a b : @& Nat) : Nat := powLoop a b 1

theorem pow_eq (a b : Nat) : pow a b = a ^ b := by simp [pow, powLoop_eq]

@[csimp] theorem lowerAdd : Nat.add = add := funext fun a => funext fun b => (add_eq a b).symm
@[csimp] theorem lowerMul : Nat.mul = mul := funext fun a => funext fun b => (mul_eq a b).symm
@[csimp] theorem lowerPow : Nat.pow = pow := funext fun a => funext fun b => (pow_eq a b).symm

end G1Arithmetic
