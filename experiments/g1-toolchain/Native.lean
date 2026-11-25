import Init

namespace G1Probe

inductive Payload where
  | reg (data : ByteArray)

@[noinline, export g1_array] def asArray (xs : List UInt8) : Array UInt8 := Array.mk xs
@[noinline, export g1_bytes] def asBytes (xs : Array UInt8) : ByteArray := ByteArray.mk xs
@[noinline, export g1_byte] def asByte (v : BitVec 8) : UInt8 := UInt8.ofBitVec v
@[noinline, export g1_payload] def pack (xs : List UInt8) : Payload :=
  .reg (asBytes (asArray xs))

@[noinline, export g1_add] def add (a b : Nat) : Nat := Nat.add a b
@[noinline, export g1_mul] def mul (a b : Nat) : Nat := Nat.mul a b
@[noinline, export g1_pow] def pow (a b : Nat) : Nat := Nat.pow a b
@[noinline, export g1_arithmetic] def arithmetic (a b : Nat) : Nat :=
  Nat.add (Nat.mul a b) (Nat.pow a b)

example (x : BitVec 8) : (UInt8.ofBitVec x).toBitVec = x := rfl
example (xs : List UInt8) : (Array.mk xs).toList = xs := rfl
example (xs : Array UInt8) : (ByteArray.mk xs).data = xs := rfl

example : Bool.ctorIdx false = 0 := rfl
example : Bool.ctorIdx true = 1 := rfl

@[export g1_bool_tag] def boolTag (value : Bool) : Nat := Bool.ctorIdx value
@[export g1_option_tag] def optionTag (value : Option Nat) : Nat := Option.ctorIdx value
@[export g1_list_tag] def listTag (value : List Nat) : Nat := List.ctorIdx value
@[export g1_except_tag] def exceptTag (value : Except Nat Nat) : Nat := Except.ctorIdx value

end G1Probe
