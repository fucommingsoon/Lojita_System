#include <lean/lean.h>
#include <string.h>

extern lean_object *g1_add(lean_object *, lean_object *);
extern lean_object *g1_mul(lean_object *, lean_object *);
extern lean_object *g1_pow(lean_object *, lean_object *);

/* Operands are owned at the exported g1_* entry points. */
int main(int argc, char **argv) {
    if (argc != 5) return 2;
    lean_object *a = lean_cstr_to_nat(argv[2]);
    lean_object *b = lean_cstr_to_nat(argv[3]);
    lean_object *expected = lean_cstr_to_nat(argv[4]);
    lean_object *result;
    if (strcmp(argv[1], "add") == 0) result = g1_add(a, b);
    else if (strcmp(argv[1], "mul") == 0) result = g1_mul(a, b);
    else if (strcmp(argv[1], "pow") == 0) result = g1_pow(a, b);
    else return 2;
    int ok = lean_nat_dec_eq(result, expected);
    lean_dec(result);
    lean_dec(expected);
    return ok ? 0 : 1;
}
