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

end G1Probe
