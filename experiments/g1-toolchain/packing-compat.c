#include <lean/lean.h>

/* Stock Init.Data.Range.Polymorphic.SInt stores this boxed constructor in a
   closure. The stock wrapper takes one owned BitVec and returns a boxed UInt8.
   Packing.viaByte's generated boxed entry has precisely that ownership and
   result ABI, including the decrement of the owned input. */
extern lean_obj_res l_Packing_viaByte___boxed(lean_obj_arg);
LEAN_EXPORT lean_obj_res l_UInt8_ofBitVec___boxed(lean_obj_arg value) {
    return l_Packing_viaByte___boxed(value);
}
