#!/usr/bin/env python3
"""test-soc-visual.py - verify soc-diagram.html memory hierarchy descriptions."""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SOC_HTML = ROOT / "output" / "architecture-visuals" / "soc-diagram.html"

FORBIDDEN_PHRASES = [
    "256B Direct Mapped",
    "256B 2-Way",
    "512B 2-Way",
    "Non-blocking Multi-Level",
    "Miss Queue",
    "write-through L1D",
    "256-bit line-refill",
]

REQUIRED_PHRASES = [
    "8 KB",
    "16 KB",
    "32 KB",
    "Tree-PLRU",
    "write-back",
    "512-bit",
    "64B",
]


def main() -> int:
    cmd = ["lake", "--no-ansi", "exe", "generate_all", "--soc-diagram"]
    res = subprocess.run(cmd, capture_output=True, text=True, cwd=str(ROOT))
    if res.returncode != 0:
        print(f"Error running generate_all --soc-diagram:\n{res.stderr}", file=sys.stderr)
        return 1

    content = SOC_HTML.read_text(encoding="utf-8")

    failures: list[str] = []
    for phrase in FORBIDDEN_PHRASES:
        if phrase in content:
            failures.append(f"Found forbidden obsolete phrase: '{phrase}'")

    for phrase in REQUIRED_PHRASES:
        if phrase.lower() not in content.lower():
            failures.append(f"Missing required phrase: '{phrase}'")

    if failures:
        print("FAIL: soc-diagram.html has incorrect memory hierarchy words:", file=sys.stderr)
        for f in failures:
            print(f"  - {f}", file=sys.stderr)
        return 1

    print("PASS: soc-diagram.html memory hierarchy verified.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
