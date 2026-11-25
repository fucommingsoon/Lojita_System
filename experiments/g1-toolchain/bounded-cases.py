"""Compare large dynamic Nat arguments to Python integers, including tagged/boxed crossings."""
import subprocess
import sys

sys.set_int_max_str_digits(0)
cases = [
    ("add", 1, 10**9), ("add", 10**2000 - 1, 1), ("add", 1 << 4096, 1 << 4097),
    ("mul", 0, 1 << 2048), ("mul", 10**100 + 7, 10**224 - 1),
    ("mul", (1 << 2048) - 1, (1 << 3072) + 1), ("pow", 0, 0),
    ("pow", 1, (1 << 128) - 1), ("pow", 2, 16384), ("pow", 5, 2047),
    ("pow", 10**9 + 7, 129),
]
for name, a, b in cases:
    expected = {"add": int.__add__, "mul": int.__mul__, "pow": int.__pow__}[name](a, b)
    subprocess.run([sys.argv[1], name, str(a), str(b), str(expected)], check=True, timeout=8)
print(f"large arithmetic={len(cases)}/{len(cases)}")
