#!/usr/bin/env python3
"""bench_regression.py - gate instruction IPC against the checked-in baseline.

Compares a fresh output/bench/bench-metrics.csv (name,peak_ipc_milli,
dependent_ipc_milli, produced by `make -C testbench run-benchmarks` via
run-suite.sh --bench-csv) against verification/bench-baseline.csv and fails
on any throughput regression beyond tolerance.

Why this exists: the per-ELF "PASS add.elf (cycles, retired, IPC)" log line
reports *whole-program* IPC (both measured regions plus setup/IO), while
benchmarks.html publishes *peak* (throughput-region) IPC. Comparing those two
numbers looks like a regression when none occurred (2026-09-24: 1.933 peak vs
1.578 whole-program for identical RTL). This gate compares like with like.

A regression is a drop of more than --tolerance (relative) AND more than
--min-milli (absolute, guards quantization noise on tiny values such as
CSR at 6 milli) on either peak or dependent IPC. Improvements and new
instructions are reported but never fail.

The simulator is deterministic, so any failure is a real RTL or benchmark
program change: affirm it by re-running with --update-baseline (merges only
the rows present in --metrics, so a PR subset run updates just its subset)
and committing the baseline in the same PR.

Usage:
  python3 scripts/bench_regression.py --metrics output/bench/bench-metrics.csv
  python3 scripts/bench_regression.py --metrics /tmp/subset.csv --only add,mul,ld
  python3 scripts/bench_regression.py --metrics output/bench/bench-metrics.csv \\
      --baseline verification/bench-baseline.csv --update-baseline
"""

from __future__ import annotations

import argparse
import csv
import os
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_METRICS = REPO_ROOT / "output" / "bench" / "bench-metrics.csv"
DEFAULT_BASELINE = REPO_ROOT / "verification" / "bench-baseline.csv"

# Fast PR-side subset: one benchmark per execution path (ALU dual-issue,
# multiplier, FPU, load, store, branch, jump). Each runs in seconds; the full
# suite (~196 ELFs) stays on the main-branch benchmarks job.
DEFAULT_SUBSET = ["add", "mul", "fadd_s", "fmul_s", "ld", "sd", "beq", "jal"]


def parse_milli(s: str | None) -> int | None:
    if s is None:
        return None
    s = s.strip()
    if s in ("", "-"):
        return None
    try:
        return int(s)
    except ValueError:
        return None


def load_csv(path: Path) -> dict[str, tuple[int | None, int | None]]:
    rows: dict[str, tuple[int | None, int | None]] = {}
    with path.open() as f:
        for row in csv.DictReader(l for l in f if not l.startswith("#")):
            name = (row.get("name") or "").strip()
            if not name or name == "name":
                continue
            peak = parse_milli(row.get("peak_ipc_milli") or row.get("throughput_ipc_milli"))
            dep = parse_milli(row.get("dependent_ipc_milli") or row.get("latency_ipc_milli"))
            # Legacy pre-IPC schema stored CPI x1000 (see gen-benchmark-visual.py).
            if peak is None:
                peak = cpi_to_ipc(row.get("throughput_cpi_milli"))
            if dep is None:
                dep = cpi_to_ipc(row.get("latency_cpi_milli"))
            rows[name] = (peak, dep)
    return rows


def cpi_to_ipc(s: str | None) -> int | None:
    cpi = parse_milli(s)
    if cpi is None or cpi <= 0:
        return None
    return 1000000 // cpi


def check(
    current: dict[str, tuple[int | None, int | None]],
    baseline: dict[str, tuple[int | None, int | None]],
    only: list[str] | None,
    tolerance: float,
    min_milli: int,
) -> tuple[list[str], list[str], list[str], list[str]]:
    """Return (regressions, missing, added, improvements) as markdown rows."""
    regressions: list[str] = []
    missing: list[str] = []
    added: list[str] = []
    improvements: list[str] = []

    names = only if only else sorted(set(baseline) | set(current))
    for name in names:
        if name not in baseline:
            if name in current:
                added.append(f"| {name} | new instruction, no baseline | - | - |")
            continue
        if name not in current:
            missing.append(name)
            continue
        for col, label in ((0, "peak"), (1, "dependent")):
            base, cur = baseline[name][col], current[name][col]
            if base is None or cur is None:
                continue
            if cur < base * (1.0 - tolerance) and (base - cur) >= min_milli:
                regressions.append(
                    f"| {name} | {label} | {base / 1000:.3f} | {cur / 1000:.3f} "
                    f"| {(cur - base) / base * 100:+.1f}% |"
                )
            elif cur > base and (cur - base) >= min_milli:
                improvements.append(f"| {name} | {label} | {base / 1000:.3f} | {cur / 1000:.3f} |")
    return regressions, missing, added, improvements


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description="Gate benchmark IPC against the baseline.")
    ap.add_argument("--metrics", type=Path, default=DEFAULT_METRICS)
    ap.add_argument("--baseline", type=Path, default=DEFAULT_BASELINE)
    ap.add_argument("--tolerance", type=float, default=0.05,
                    help="Relative drop allowed before flagging (default 0.05).")
    ap.add_argument("--min-milli", type=int, default=10,
                    help="Absolute drop (ipc*1000) required to flag (default 10).")
    ap.add_argument("--only", default="",
                    help="Comma-separated subset of benchmark names to check.")
    ap.add_argument("--update-baseline", action="store_true",
                    help="Merge --metrics rows into --baseline and exit 0.")
    ap.add_argument("--report", type=Path, default=None,
                    help="Write a markdown report to this path.")
    args = ap.parse_args(argv)

    if not args.metrics.exists():
        print(f"bench_regression: metrics file not found: {args.metrics}", file=sys.stderr)
        return 2
    if not args.baseline.exists():
        print(f"bench_regression: baseline file not found: {args.baseline}", file=sys.stderr)
        return 2

    current = load_csv(args.metrics)
    only = [n.strip() for n in args.only.split(",") if n.strip()] or None

    if args.update_baseline:
        merged = load_csv(args.baseline)
        merged.update(current if only is None else {n: current[n] for n in only if n in current})
        header = [l for l in args.baseline.read_text().splitlines() if l.startswith("#")]
        with args.baseline.open("w") as f:
            f.write("\n".join(header) + "\n")
            f.write("name,peak_ipc_milli,dependent_ipc_milli\n")
            for name in sorted(merged):
                peak, dep = merged[name]
                f.write(f"{name},{peak if peak is not None else '-'},"
                        f"{dep if dep is not None else '-'}\n")
        print(f"bench_regression: baseline updated ({len(merged)} rows): {args.baseline}")
        return 0

    baseline = load_csv(args.baseline)
    regressions, missing, added, improvements = check(
        current, baseline, only, args.tolerance, args.min_milli)

    lines = ["## Benchmark regression check",
             f"metrics: `{args.metrics}` baseline: `{args.baseline}`",
             f"tolerance: {args.tolerance * 100:.0f}% + {args.min_milli} milli floor",
             ""]
    if regressions:
        lines += ["### Regressions (FAIL)",
                  "| instr | region | baseline IPC | current IPC | delta |",
                  "|---|---|---|---|---|"] + regressions + [""]
    if missing:
        lines += ["### Missing from run (FAIL)", ", ".join(sorted(missing)), ""]
    if improvements:
        lines += ["### Improvements (info)",
                  "| instr | region | baseline IPC | current IPC |",
                  "|---|---|---|---|"] + improvements + [""]
    if added:
        lines += ["### New instructions, no baseline (info)",
                  "| instr | note | - | - |",
                  "|---|---|---|---|"] + added + [""]
    if not regressions and not missing:
        scope = f"{len(only)}-instr subset" if only else f"{len(current)} instrs"
        lines += [f"PASS: no regression over baseline ({scope})."]

    report = "\n".join(lines)
    print(report)
    if args.report:
        args.report.write_text(report + "\n")
    if summary := os.environ.get("GITHUB_STEP_SUMMARY"):
        with open(summary, "a") as f:
            f.write(report + "\n")

    if regressions or missing:
        print(f"bench_regression: FAIL ({len(regressions)} regressions, "
              f"{len(missing)} missing)", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
