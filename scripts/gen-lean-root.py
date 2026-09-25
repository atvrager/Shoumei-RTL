#!/usr/bin/env python3
"""gen-lean-root.py - Forwarder to native Lean generator for lean/Shoumei/All.lean.

Replaced by `Shoumei.Codegen.LeanRoot` in Lean 4 (`lake exe generate_all --gen-lean-root`).
"""
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def main() -> int:
    flag = "--check-lean-root" if "--check" in sys.argv else "--gen-lean-root"
    cmd = ["lake", "--no-ansi", "exe", "generate_all", flag]
    return subprocess.run(cmd, cwd=ROOT).returncode


if __name__ == "__main__":
    sys.exit(main())
