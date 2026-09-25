#!/usr/bin/env python3
"""gen-benchmark-visual.py - Forwarder to native Lean benchmark report generator.

Replaced by `Shoumei.Codegen.BenchmarkVisual` in Lean 4 (`lake exe generate_all --benchmarks`).
"""
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def main() -> int:
    cmd = ["lake", "--no-ansi", "exe", "generate_all", "--benchmarks"]
    return subprocess.run(cmd, cwd=ROOT).returncode


if __name__ == "__main__":
    sys.exit(main())
