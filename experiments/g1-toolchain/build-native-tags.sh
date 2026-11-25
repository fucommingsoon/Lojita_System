#!/usr/bin/env bash
set -euo pipefail
unset LEAN_PATH LEAN_SYSROOT
ulimit -c 0
here=$(cd "$(dirname "$0")" && pwd)
repo=$(git -C "$here" rev-parse --show-toplevel)
release=$(lean --print-prefix)
[[ $("$release/bin/lean" --githash) == 611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9 ]]
if (( $# == 0 )); then
  stage=$(mktemp -d)
else
  [[ $# == 1 ]]
  mkdir -- "$1"
  stage=$(cd "$1" && pwd)
fi
echo "Artifacts: $stage"
prefix="$stage/prefix"
python3 "$here/sysroot.py" "$release" "$prefix"
cd "$stage"
mkdir Init project
cp "$release/src/lean/Init/Prelude.lean" Init/
echo '4e328f8f9ab8c511907489e361c418d0d0ea31759d33863f166536c4f827133e  Init/Prelude.lean' | sha256sum --check
patch --fuzz=0 -p1 < "$here/tags.patch"
"$prefix/bin/lean" -R . -o "$prefix/lib/lean/Init/Prelude.olean" -c Init/Prelude.c Init/Prelude.lean
"$here/install-init-archive.sh" "$stage" "$release"
git -C "$repo" archive HEAD | tar -x -C project
cd project
export PATH="$prefix/bin:$PATH" LEAN_SYSROOT="$prefix"
lake build >"$stage/build.log" 2>&1
timeout 30s ./.lake/build/bin/lojita verify-self | tee "$stage/verify-self.log"
