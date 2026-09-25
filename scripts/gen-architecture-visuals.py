#!/usr/bin/env python3
"""gen-architecture-visuals.py - Forwarder to native Lean architecture visualizer.

Replaced by `Shoumei.Codegen.ArchitectureVisuals` in Lean 4 (AYAYA vector SVG suite).
Zero matplotlib, zero raster PNGs, byte-identical deterministic vector output.
"""
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def main() -> int:
    cmd = ["lake", "--no-ansi", "exe", "generate_all", "--visuals"]
    return subprocess.run(cmd, cwd=ROOT).returncode


if __name__ == "__main__":
    sys.exit(main())