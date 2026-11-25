#!/usr/bin/env bash
set -euo pipefail
unset LEAN_PATH LEAN_SYSROOT
ulimit -c 0
here=$(cd "$(dirname "$0")" && pwd)
repo=$(git -C "$here" rev-parse --show-toplevel)
release=$(lean --print-prefix)
upstream=611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9
base=9225b46e02ca913a3f6a020c7ee5ece8ed2efe57
[[ $("$release/bin/lean" --githash) == "$upstream" ]]
expected=4e328f8f9ab8c511907489e361c418d0d0ea31759d33863f166536c4f827133e
[[ $(sha256sum "$release/src/lean/Init/Prelude.lean" | cut -d' ' -f1) == "$expected" ]]
if [[ $# == 0 ]]; then work=$(mktemp -d); else
  [[ $# == 1 ]]; mkdir -- "$1"; work=$(cd "$1" && pwd)
fi
echo "Artifacts: $work"

compile_module() {
  local module=$1 lib="$prefix/lib/lean"
  "$prefix/bin/lean" -R . -o "$lib/$module.olean" -c "$module.c" "$module.lean"
}

check_project() {
  local project="$dir/project" log="$dir/project-g1.log" code=0
  mkdir "$project"
  git -C "$repo" archive "$base" | tar -x -C "$project"
  (cd "$project" && PATH="$prefix/bin:$PATH" LEAN_SYSROOT="$prefix" ./test-g1-purity-and-size.sh) >"$log" 2>&1 || code=$?
  echo "project G1 exit=$code"
  grep -E 'G1 audited|G1 strict purity failed at' "$log"
  local violations=95 externs=77
  if [[ $variant == official ]]; then violations=101; externs=83; fi
  [[ $code == 1 ]]
  grep -Fq "G1 strict purity failed at $violations constants [(axiom, 1), (extern, $externs), (unsafe, 17)]" "$log"
}

for variant in official stripped adapted; do
  dir="$work/$variant"
  mkdir -p "$dir/Init"; cd "$dir"
  prefix=$release
  cp "$release/src/lean/Init/Prelude.lean" Init/
  objects=()
  if [[ $variant == official ]]; then
    "$release/bin/lean" -R . -o Init/Prelude.olean -c Init/Prelude.c Init/Prelude.lean
  else
    prefix="$dir/prefix"
    python3 "$here/sysroot.py" "$release" "$prefix"
    patch -s --fuzz=0 -p1 < "$here/prelude.patch"
    if [[ $variant == adapted ]]; then patch -s --fuzz=0 -p1 < "$here/successor.patch"; fi
    compile_module Init/Prelude
    if [[ $variant == adapted ]]; then
      cp "$here/Packing.lean" Init/G1Packing.lean
      compile_module Init/G1Packing
      cp "$release/src/lean/Init.lean" Init.lean
      echo 'public import Init.G1Packing' >> Init.lean
      compile_module Init
      objects+=(Init/G1Packing.c)
    fi
  fi
  cp "$here/Native.lean" .
  "$prefix/bin/lean" -o Native.olean -c Native.c Native.lean
  # Keep the auditor on the release toolchain, even for the deliberately broken control.
  "$release/bin/lean" --run "$here/Audit.lean" "$prefix/lib/lean" "$dir" >audit.log
  echo "--- $variant ---"; cat audit.log
  if [[ $variant == official ]]; then grep -q 'reachable=63, forbidden=6 ' audit.log
  else grep -q 'reachable=63, forbidden=0 ' audit.log; fi
  if [[ $variant == adapted ]]; then
    grep -q 'replacement bodies: reachable=292, forbidden=17 .*Nat.abiSucc' audit.log
    grep -q 'replacement bodies:.*ByteArray.push' audit.log
  fi
  objects+=(Init/Prelude.c Native.c)
  cflags=(-O1 -ffunction-sections -fdata-sections -I"$release/include")
  for source in "${objects[@]}"; do cc "${cflags[@]}" -c "$source" -o "${source%.c}.o"; done
  cc "${cflags[@]}" -Wall -Wextra -Werror "$here/abi.c" "${objects[@]/%.c/.o}" \
    -Wl,--gc-sections,-Map,check.map -L"$release/lib/lean" -Wl,-rpath,"$release/lib/lean" -lleanshared -o check
  if [[ $variant != official ]]; then
    nm --defined-only check >defined-symbols.txt
    for name in add mul pow; do grep -q " T l_Nat_$name$" defined-symbols.txt; done
  fi
  abi=0; arithmetic=0
  ./check abi >abi.log || abi=$?
  timeout 3s ./check arithmetic >arithmetic.log || arithmetic=$?
  cat abi.log arithmetic.log
  echo "native ABI exit=$abi, arithmetic exit=$arithmetic"
  if [[ $variant == stripped ]]; then
    [[ $abi == 1 && $arithmetic == 124 ]]
  else
    [[ $abi == 0 && $arithmetic == 0 ]]
  fi
  check_project
done
