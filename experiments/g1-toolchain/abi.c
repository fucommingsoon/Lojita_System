#include <lean/lean.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

extern lean_object *g1_array(lean_object *);
extern lean_object *g1_bytes(lean_object *);
extern uint8_t g1_byte(lean_object *);
extern lean_object *g1_payload(lean_object *);
extern lean_object *g1_add(lean_object *, lean_object *);
extern lean_object *g1_mul(lean_object *, lean_object *);
extern lean_object *g1_pow(lean_object *, lean_object *);
extern lean_object *g1_arithmetic(lean_object *, lean_object *);

extern lean_object *g1_bool_tag(uint8_t);
extern lean_object *g1_option_tag(lean_object *);
extern lean_object *g1_list_tag(lean_object *);
extern lean_object *g1_except_tag(lean_object *);

static uint8_t value(size_t i, size_t n) { return (uint8_t)(i * 37 + n); }

static lean_object *list_input(size_t n) {
    lean_object *xs = lean_box(0);
    for (size_t i = n; i > 0; --i) {
        lean_object *cell = lean_alloc_ctor(1, 2, 0);
        lean_ctor_set(cell, 0, lean_box(value(i - 1, n)));
        lean_ctor_set(cell, 1, xs);
        xs = cell;
    }
    return xs;
}

static int packed_matches(lean_object *x, size_t n) {
    if (lean_is_scalar(x) || !lean_is_sarray(x) || lean_sarray_elem_size(x) != 1 ||
        lean_sarray_size(x) != n) return 0;
    for (size_t i = 0; i < n; ++i)
        if (lean_byte_array_uget(x, i) != value(i, n)) return 0;
    return 1;
}

static int array_matches(lean_object *x, size_t n) {
    if (lean_is_scalar(x) || !lean_is_array(x) || lean_array_size(x) != n) return 0;
    for (size_t i = 0; i < n; ++i)
        if (lean_unbox(lean_array_get_core(x, i)) != value(i, n)) return 0;
    return 1;
}

static int check_abi(void) {
    unsigned bytes = 0, arrays = 0, packed = 0, payloads = 0;
    for (unsigned i = 0; i < 256; ++i) bytes += g1_byte(lean_box(i)) == i;
    for (size_t n = 0; n <= 256; ++n) {
        lean_object *array = g1_array(list_input(n));
        arrays += array_matches(array, n);
        lean_dec(array);

        lean_object *input = lean_alloc_array(n, n);
        for (size_t i = 0; i < n; ++i)
            lean_array_set_core(input, i, lean_box(value(i, n)));
        lean_object *result = g1_bytes(input);
        packed += packed_matches(result, n);
        lean_dec(result);

        lean_object *payload = g1_payload(list_input(n));
        payloads += packed_matches(payload, n);
        lean_dec(payload);
    }
    printf("UInt8=%u/256 Array=%u/257 ByteArray=%u/257 Payload=%u/257\n",
           bytes, arrays, packed, payloads);
    return !(bytes == 256 && arrays == 257 && packed == 257 && payloads == 257);
}

static int small_matches(lean_object *got, size_t expected) {
    int ok = lean_is_scalar(got) && lean_unbox(got) == expected;
    lean_dec(got);
    return ok;
}

#ifdef G1_PURE_TAGS
extern lean_object *l_Bool_ctorIdx(uint8_t);
extern lean_object *l_Bool_ctorIdx___boxed(lean_object *);
#endif

/* Use both scalar and heap payloads so payload values cannot serve as discriminants. */
static int check_tags(void) {
    unsigned passed = 0;
    for (unsigned tag = 0; tag < 2; ++tag) {
        passed += small_matches(g1_bool_tag((uint8_t)tag), tag);
        for (unsigned big = 0; big < 2; ++big) {
            lean_object *payload = big ? lean_cstr_to_nat("18446744073709551616") : lean_box(0);
            lean_object *opt = lean_box(0);
            lean_object *list = lean_box(0);
            if (tag) {
                opt = lean_alloc_ctor(1, 1, 0);
                list = lean_alloc_ctor(1, 2, 0);
                lean_inc(payload);
                lean_ctor_set(opt, 0, payload);
                lean_inc(payload);
                lean_ctor_set(list, 0, payload);
                lean_ctor_set(list, 1, lean_box(0));
            }
            lean_object *result = lean_alloc_ctor(tag, 1, 0);
            lean_ctor_set(result, 0, payload);
            passed += small_matches(g1_option_tag(opt), tag);
            passed += small_matches(g1_list_tag(list), tag);
            passed += small_matches(g1_except_tag(result), tag);
        }
    }
    printf("constructor tags=%u/14\n", passed);
#ifdef G1_PURE_TAGS
    unsigned native = 0;
    for (uint8_t i = 0; i < 2; ++i) {
        native += small_matches(l_Bool_ctorIdx(i), i);
        native += small_matches(l_Bool_ctorIdx___boxed(lean_box(i)), i);
    }
    printf("Bool scalar/boxed=%u/4\n", native);
    if (native != 4) return 1;
#endif
    return passed != 14;
}

static int big_add_matches(const char *a, unsigned b, const char *expected) {
    lean_object *x = lean_cstr_to_nat(a);
    lean_object *want = lean_cstr_to_nat(expected);
    lean_object *got = g1_add(x, lean_box(b));
    int ok = lean_nat_dec_eq(got, want);
    lean_dec(want); lean_dec(got);
    return ok;
}

static int check_arithmetic(void) {
    unsigned passed = 0;
    for (unsigned a = 0; a <= 24; ++a) {
        for (unsigned b = 0; b <= 24; ++b) {
            passed += small_matches(g1_add(lean_box(a), lean_box(b)), a + b);
            passed += small_matches(g1_mul(lean_box(a), lean_box(b)), a * b);
        }
    }
    for (unsigned a = 0; a <= 7; ++a) {
        unsigned power = 1;
        for (unsigned b = 0; b <= 4; ++b) {
            passed += small_matches(g1_pow(lean_box(a), lean_box(b)), power);
            passed += small_matches(g1_arithmetic(lean_box(a), lean_box(b)), a * b + power);
            power *= a;
        }
    }
    passed += big_add_matches("9223372036854775807", 1, "9223372036854775808");
    passed += big_add_matches("9223372036854775808", 2, "9223372036854775810");
    passed += big_add_matches("123456789012345678901234567890123456789000", 42,
                              "123456789012345678901234567890123456789042");
    printf("arithmetic=%u/1333\n", passed);
    return passed != 1333;
}

int main(int argc, char **argv) {
    if (argc == 2 && strcmp(argv[1], "tags") == 0) return check_tags();
    if (argc == 2 && strcmp(argv[1], "abi") == 0) return check_abi();
    if (argc == 2 && strcmp(argv[1], "arithmetic") == 0) return check_arithmetic();
    return 2;
}
