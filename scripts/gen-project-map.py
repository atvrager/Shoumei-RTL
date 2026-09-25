#!/usr/bin/env python3
"""gen-project-map.py - Forwarder to native Lean generator for docs/project-map.md.

Replaced by `Shoumei.Codegen.ProjectMap` in Lean 4 (`lake exe generate_all --project-map`).
"""
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def main() -> int:
    import shutil

    if not shutil.which("lake"):
        print(
            "gen-project-map: lake not found in PATH; Lean 4 toolchain is required",
            file=sys.stderr,
        )
        return 1

    cmd = ["lake", "--no-ansi", "exe", "generate_all", "--project-map"]
    i = 1
    while i < len(sys.argv):
        arg = sys.argv[i]
        if arg.startswith("--out="):
            cmd.append(arg)
        elif arg == "--out" and i + 1 < len(sys.argv):
            cmd.append(f"--out={sys.argv[i + 1]}")
            i += 1
        i += 1
    return subprocess.run(cmd, cwd=ROOT).returncode


if __name__ == "__main__":
    sys.exit(main())
