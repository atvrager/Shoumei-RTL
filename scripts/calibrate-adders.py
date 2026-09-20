#!/usr/bin/env python3
"""calibrate-adders.py - measure real adder area/delay per PDK

Synthesizes every wrapper in output/adder-matrix (see GenerateAdderMatrix.lean)
with the PDK flows and records, per (module, pdk):

  area  - "Chip area for top module" from the Yosys area report (um^2)
  delay - ABC's reported critical delay of the mapped adder, in ps

Writes output/adder-cost-table.json and, with --refit, prints suggested
cellArea/cellDelay seeds for Shoumei.Components.Cost.

The selector never reads this file; it exists to keep the analytic constants
honest.  A run whose fitted constants differ from Cost.lean by more than ~25%
is the signal to update the seeds.

Usage: scripts/calibrate-adders.py [--refit] [--limit N] [module ...]
"""

from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MATRIX = ROOT / "output/adder-matrix"
OUT = ROOT / "output/adder-cost-table.json"

# PDK -> (synth script, clock period in ns).  ABC reports its critical delay
# in ps for both platforms, so no unit conversion is applied.
PDKS = {
    "asap7": ("physical/run-yosys-asap7.sh", "1.0"),
    "gf180": ("physical/run-yosys-gf180.sh", "15.625"),
}

AREA_RE = re.compile(r"Chip area for top module '[^']*':\s*([0-9.]+)")
DELAY_RE = re.compile(r"Delay\s*=\s*([0-9.]+)\s*ps")


def read_manifest() -> list[tuple[str, dict[str, float]]]:
    """module -> {asap7_area, asap7_delay, gf180_area, gf180_delay}."""
    out = []
    for line in (MATRIX / "manifest.txt").read_text().splitlines():
        parts = line.split(",")
        if len(parts) < 7:
            continue
        module, _width, _cin, a_a, a_d, g_a, g_d = parts[:7]
        out.append((module, {
            "asap7_area": float(a_a), "asap7_delay": float(a_d),
            "gf180_area": float(g_a), "gf180_delay": float(g_d),
        }))
    return out


def measure(module: str, pdk: str) -> dict[str, float] | None:
    script, period = PDKS[pdk]
    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        rtl = tmp_path / "rtl"
        rtl.mkdir()
        for suffix in ("", "_synth"):
            shutil.copy(MATRIX / f"{module}{suffix}.sv", rtl)

        out_dir = tmp_path / "out"
        env = {
            "RTL_DIR": str(rtl),
            "SYNTH_WRAPPER": str(rtl / f"{module}_synth.sv"),
            "OUTPUT_DIR": str(out_dir),
            "DESIGN_NAME": f"{module}_synth",
        }
        proc = subprocess.run(
            [str(ROOT / script), f"{module}_synth", period],
            cwd=ROOT, env={**__import__("os").environ, **env},
            capture_output=True, text=True,
        )
        if proc.returncode != 0:
            print(f"  FAIL {module} [{pdk}]", file=sys.stderr)
            return None

        log = (out_dir / "synth.log").read_text(errors="replace")
        area_report = out_dir / "reports/area.rpt"
        area_match = AREA_RE.search(area_report.read_text()) if area_report.exists() else None
        delays = [float(m) for m in DELAY_RE.findall(log)]
        if area_match is None or not delays:
            print(f"  FAIL {module} [{pdk}]: no area/delay in report", file=sys.stderr)
            return None
        return {"area": float(area_match.group(1)), "delay": max(delays)}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--refit", action="store_true",
                    help="print suggested Cost.lean constants")
    ap.add_argument("--limit", type=int, default=0)
    ap.add_argument("modules", nargs="*")
    args = ap.parse_args()

    manifest = read_manifest()
    estimates = dict(manifest)
    modules = args.modules or [m for m, _ in manifest]
    if args.limit:
        modules = modules[: args.limit]

    table: dict[str, dict[str, dict[str, float]]] = {}
    for pdk in PDKS:
        for module in modules:
            result = measure(module, pdk)
            if result is not None:
                table.setdefault(module, {})[pdk] = result
        done = sum(1 for m in table if pdk in table[m])
        print(f"{pdk}: measured {done}/{len(modules)}")

    OUT.write_text(json.dumps(table, indent=2, sort_keys=True) + "\n")
    print(f"wrote {OUT}")

    if args.refit:
        for pdk in PDKS:
            area_ratios, delay_ratios = [], []
            for module, per_pdk in table.items():
                est = estimates.get(module)
                if est is None or pdk not in per_pdk:
                    continue
                if est[f"{pdk}_area"] > 0:
                    area_ratios.append(per_pdk[pdk]["area"] / est[f"{pdk}_area"])
                if est[f"{pdk}_delay"] > 0:
                    delay_ratios.append(per_pdk[pdk]["delay"] / est[f"{pdk}_delay"])
            if not delay_ratios:
                continue
            med = lambda xs: sorted(xs)[len(xs) // 2]  # noqa: E731
            print(f"-- {pdk}: scale cellArea by {med(area_ratios):.2f}x, "
                  f"cellDelay by {med(delay_ratios):.2f}x "
                  f"({len(delay_ratios)} adders)")
            print("   (Cost.lean seeds assume 1.0x; a factor outside 0.75-1.25 is a"
                  " signal to update them)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
