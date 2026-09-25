#!/usr/bin/env python3
"""lint-structural.py - Forwarder to native Lean structural linter (DC NXT LINT-3x).

Replaced by `Shoumei.Verification.StructuralLint` in Lean 4 (`lake exe generate_all --lint-structural`).
"""
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def main() -> int:
    sv_dir = sys.argv[1] if len(sys.argv) > 1 else "output/sv-from-lean"
    cmd = ["lake", "--no-ansi", "exe", "generate_all", "--lint-structural", f"--sv-dir={sv_dir}"]
    return subprocess.run(cmd, cwd=ROOT).returncode


if __name__ == "__main__":
    sys.exit(main())