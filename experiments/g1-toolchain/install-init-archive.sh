#!/usr/bin/env bash
set -euo pipefail
# install-init-archive.sh STAGE OFFICIAL_RELEASE [--packing]
# STAGE is a sysroot.py overlay with generated Init/Prelude.c. For the
# arithmetic/packing experiment, also include the generated import root and
# Packing definitions, plus the boxed symbol used by prebuilt release modules.
[[ $# == 2 || ( $# == 3 && $3 == --packing ) ]]
here=$(cd "$(dirname "$0")" && pwd)
stage=$(cd "$1" && pwd -P)
release=$(cd "$2" && pwd -P)
prefix="$stage/prefix"
lib="$prefix/lib/lean"
[[ -d "$lib" && ! "$lib" -ef "$release/lib/lean" ]]
work=$(mktemp -d "$stage/archive.XXXXXXXX")
trap 'rm -rf "$work"' EXIT
members=()
add_object() {
  local source=$1 name=$2
  "$prefix/bin/leanc" -O2 -ffunction-sections -fdata-sections -fPIC \
    -c "$source" -o "$work/$name"
  members+=("$work/$name")
}
add_object "$stage/Init/Prelude.c" Prelude.c.o.export
if [[ $# == 3 ]]; then
  add_object "$stage/Init/G1Packing.c" G1Packing.c.o.export
  add_object "$stage/Init.c" Init.c.o.export
  add_object "$here/packing-compat.c" packing-compat.o
  cc -O1 -Wall -Wextra -Werror -I"$prefix/include" "$here/test-packing-compat.c" \
    "$work/packing-compat.o" "$work/G1Packing.c.o.export" -Wl,--gc-sections \
    -L"$lib" -Wl,-rpath,"$lib" -lleanshared -o "$work/check-compat"
  "$work/check-compat"
fi
# Never update the official archive through the overlay's original symlink.
cp --reflink=auto "$release/lib/lean/libInit.a" "$work/libInit.a"
"$prefix/bin/llvm-ar" rcs "$work/libInit.a" "${members[@]}"
mv -Tf "$work/libInit.a" "$lib/libInit.a"
