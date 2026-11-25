"""Keep Prelude's borrowed ABI and forward its three arithmetic symbols to checked Lean code."""
import re
import sys
from pathlib import Path

original, replacement, destination = map(Path, sys.argv[1:])
source = original.read_text()
fast = replacement.read_text()

# A new closed object would require this module's initialization before Prelude can call it.
if 'lean_obj_once(' in fast or 'lean_mark_persistent(' in fast:
    raise SystemExit('the bounded arithmetic definitions require a new initializer')
runtime = set(re.findall(r'\b(lean_\w+)\s*\(', fast))
allowed = {
    'lean_box', 'lean_dec', 'lean_dec_ref', 'lean_inc', 'lean_unsigned_to_nat',
    'lean_initialize_runtime_module', 'lean_io_result_is_error', 'lean_io_result_mk_ok',
    'lean_nat_dec_eq', 'lean_nat_dec_le', 'lean_nat_mod', 'lean_nat_shiftl',
    'lean_nat_shiftr', 'lean_nat_sub',
}
if runtime != allowed or re.search(r'\b(?:l_Nat_(?:add|mul|pow)|__gmp\w+)\s*\(', fast):
    raise SystemExit(f'unexpected arithmetic runtime calls: {sorted(runtime ^ allowed)}')

def body(code, name):
    pattern = rf'^LEAN_EXPORT lean_object\* {name}\(lean_object\* (\w+), lean_object\* (\w+)\)\{{\n'
    matches = list(re.finditer(pattern, code, re.M))
    if len(matches) != 1:
        raise SystemExit(f'expected one definition for {name}')
    match = matches[0]
    end, depth = match.end(), 1
    while depth and end < len(code):
        char = code[end]
        depth += (char == '{') - (char == '}')
        end += 1
    if depth:
        raise SystemExit(f'incomplete definition of {name}')
    return match, end

def check_borrowed(code, name):
    match, end = body(code, name + '___boxed')
    a, b = match.groups()
    text = code[match.end():end]
    call = re.search(rf'(\w+) = {name}\({a}, {b}\);', text)
    if (not call or f'return {call[1]};' not in text or
            any(text.count(f'lean_dec({x});') != 1 for x in (a, b))):
        raise SystemExit(f'expected two borrowed arguments and an owned result at {name}')

for op in ('add', 'mul', 'pow'):
    src, dst = 'l_Nat_' + op, 'l_G1Arithmetic_' + op
    check_borrowed(source, src)
    check_borrowed(fast, dst)
    proto = f'LEAN_EXPORT lean_object* {src}(lean_object*, lean_object*);'
    if source.count(proto) != 1 or fast.count(proto.replace(src, dst)) != 1:
        raise SystemExit(f'changed prototype for {src} -> {dst}')
    source = source.replace(proto, proto + '\n' + proto.replace(src, dst))
    match, end = body(source, src)
    a, b = match.groups()
    source = source[:match.end()] + f'return {dst}({a}, {b});\n}}' + source[end:]
    print(f'legacy ABI: {src} -> {dst}; borrowed Nat, borrowed Nat -> owned Nat')
destination.write_text(source)
