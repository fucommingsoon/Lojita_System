#include <lean/lean.h>
#include <stdio.h>

extern lean_obj_res l_UInt8_ofBitVec___boxed(lean_obj_arg);

int main(void) {
    unsigned passed = 0;
    for (unsigned byte = 0; byte < 256; ++byte) {
        lean_object *result = l_UInt8_ofBitVec___boxed(lean_box(byte));
        passed += lean_is_scalar(result) && lean_unbox(result) == byte;
        lean_dec(result);
    }
    printf("UInt8.ofBitVec boxed release ABI=%u/256\n", passed);
    return passed != 256;
}
