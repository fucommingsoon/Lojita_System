"""Create an overlay with private outputs and the pinned release's other artifacts."""
from pathlib import Path
import shutil
import sys

release, overlay = map(Path, sys.argv[1:])
overlay.mkdir()
private_dirs = {"bin", "lib", "lib/lean", "lib/lean/Init"}

def mirror(directory):
    for item in directory.iterdir():
        relative = item.relative_to(release)
        target = overlay / relative
        if relative.as_posix() in private_dirs:
            target.mkdir()
            mirror(item)
        elif relative.parent.as_posix() == "lib/lean/Init" and item.name.startswith("Prelude."):
            continue
        elif relative.parent.as_posix() == "lib/lean" and item.name.startswith("Init."):
            # The repaired variant also rebuilds the import root; never write through to the release.
            shutil.copy2(item, target)
        elif relative.parent.as_posix() == "bin" and item.name in {"lean", "lake", "leanc", "leanir"}:
            shutil.copy2(item, target)
        else:
            target.symlink_to(item, target_is_directory=item.is_dir())

mirror(release)
