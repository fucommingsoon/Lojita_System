#!/usr/bin/env bash
# A diagnostic for the full mixed library. Exit nonzero if even one normal launch fails.
set -euo pipefail
[[ $# == 2 ]] || { echo "usage: $0 BOUNDED_ARTIFACTS NEW_DIRECTORY" >&2; exit 2; }
here=$(cd "$(dirname "$0")" && pwd)
repo=$(git -C "$here" rev-parse --show-toplevel)
src=$(cd "$1" && pwd)
mkdir -- "$2"
out=$(cd "$2" && pwd)
cd "$out"
ulimit -c 0
cp -a "$src/prefix" .
prefix=$out/prefix
[[ $("$prefix/bin/lean" --print-prefix) == "$prefix" ]]
# libInit.a and system support can be symlinks to the official release.
# Replace the archive entry with a local copy before running ar.
cp -L "$prefix/lib/lean/libInit.a" libInit.private.a
mv -f libInit.private.a "$prefix/lib/lean/libInit.a"
mkdir archive project
cp "$src/Prelude.lowered.o" archive/Prelude.c.o.export
cp "$src/Arithmetic.o" archive/G1Arithmetic.c.o.export
cp "$src/Init/G1Packing.o" archive/G1Packing.c.o.export
"$prefix/bin/leanc" -O2 -DNDEBUG -c "$src/Init.c" -o archive/Init.c.o.export
# Stock importers use the boxed symbol even though the new constructor has a csimp rule.
# The stock wrapper consumes its argument via lean_uint8_of_nat_mk. Packing.viaByte's
# boxed wrapper consumes the argument with lean_dec and boxes the returned UInt8.
"$prefix/bin/leanc" -O2 -DNDEBUG -c "$here/packing-compat.c" -o archive/packing-compat.o
ar rcs "$prefix/lib/lean/libInit.a" archive/*.o.export archive/packing-compat.o
git -C "$repo" archive HEAD | tar -x -C project
cd project
export LEAN_SYSROOT="$prefix" PATH="$prefix/bin:$PATH"
lake build > "$out/project-build.log" 2>&1
cat /proc/sys/kernel/randomize_va_space
python3 -u - <<'PY' | tee "$out/verify.log"
import subprocess, sys
passed = 0
for i in range(12):
    try:
        run = subprocess.run([".lake/build/bin/lojita", "verify-self"],
                             capture_output=True, text=True, timeout=30)
        exact = run.stdout.strip() == "ok: resident kernel, proof and closed-world import boundary"
        passed += int(run.returncode == 0 and exact)
        print(i + 1, run.returncode, run.stdout.strip(), run.stderr.strip())
    except subprocess.TimeoutExpired:
        print(i + 1, "timeout")
print(f"verify-self={passed}/12")
sys.exit(passed != 12)
PY
