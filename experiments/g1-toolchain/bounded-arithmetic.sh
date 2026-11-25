#!/usr/bin/env bash
# Apply to the "adapted" or "pure-tags" directory produced by run.sh.
set -euo pipefail
[[ $# == 2 ]] || { echo "usage: $0 PREPARED_VARIANT NEW_DIRECTORY" >&2; exit 2; }
here=$(cd "$(dirname "$0")" && pwd)
source_dir=$(cd "$1" && pwd)
mkdir -- "$2"
out=$(cd "$2" && pwd)
release=$(lean --print-prefix)
[[ $("$release/bin/lean" --githash) == 611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9 ]]
cd "$out"
cp -a "$source_dir/prefix" "$source_dir/Init" .
cp "$source_dir/Init.lean" .
prefix=$out/prefix
[[ $("$prefix/bin/lean" --print-prefix) == "$prefix" ]]
cp "$here/Native.lean" .
"$prefix/bin/lean" -R . -c Before.c Native.lean
cp "$here/Arithmetic.lean" Init/G1Arithmetic.lean
"$prefix/bin/lean" -R . -o "$prefix/lib/lean/Init/G1Arithmetic.olean" -c Arithmetic.c Init/G1Arithmetic.lean
echo 'public import Init.G1Arithmetic' >> Init.lean
"$prefix/bin/lean" -R . -o "$prefix/lib/lean/Init.olean" -c Init.c Init.lean
"$prefix/bin/lean" -R . -o Native.olean -c After.c Native.lean
"$release/bin/lean" --run "$here/Audit.lean" "$prefix/lib/lean" "$out" | tee audit.log
[[ $(grep -c '^bounded lowering:' audit.log) == 3 ]]
grep -Eq '^payload: .*forbidden=0 ' audit.log
python3 "$here/lower-arithmetic.py" Init/Prelude.c Arithmetic.c Prelude.lowered.c
ccflags=(-O2 -DNDEBUG -ffunction-sections -fdata-sections -I"$release/include")
objects=()
for unit in Arithmetic Prelude.lowered Init/G1Packing; do
  "$prefix/bin/leanc" -O2 -DNDEBUG -c "$unit.c" -o "$unit.o"
  objects+=("$unit.o")
done
for stage in Before After; do
  if [[ $stage == Before ]]; then stem=l_Nat_; else stem=l_G1Arithmetic_; fi
  for op in add mul pow; do grep -Eq "= ${stem}${op}\\(" "$stage.c"; done
  "$prefix/bin/leanc" -O2 -DNDEBUG -c "$stage.c" -o "$stage.o"
  for check in abi arithmetic-large; do
    cc "${ccflags[@]}" "$here/$check.c" "$stage.o" "${objects[@]}" \
      -Wl,--gc-sections -L"$release/lib/lean" -Wl,-rpath,"$release/lib/lean" -lleanshared -o "$stage-$check"
  done
  "./$stage-abi" arithmetic
  "./$stage-abi" abi
  "./$stage-abi" tags
  python3 "$here/bounded-cases.py" "./$stage-arithmetic-large"
done
