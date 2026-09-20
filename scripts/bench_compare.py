#!/usr/bin/env python3
"""bench_compare.py - merge RTL + LeanSim benchmark CSVs.

Consumes:
  --rtl      output/bench/bench-results-rtl.csv    (per-ELF status/cycles/retired)
  --cpp      output/bench/bench-results-cppsim.csv (per-ELF status/cycles/retired)
  --programs output/bench/bench-programs.json      (spec manifest, in decoder order)
  --out      output/bench                          (also holds bench-metrics.csv,
                                                   the RTL per-bench CPI rows)

Emits:
  output/bench/bench-metrics.json    machine-readable merge
  output/cpp_sim/bench_metrics.h     C++ header for the generated LeanSim model
                                     (regenerate with `make run-benchmarks
                                     bench-cppsim bench-compare`)

The RTL throughput/latency CPI numbers (cpi_milli = CPI * 1000) come from the
bench-metrics.csv the runner exports; the LeanSim model has no equivalent
region instrumentation, so its whole-program CPI (cycles/retired * 1000) is
reported as `cppsim_throughput_cpi_milli` for model-fidelity comparison.

Exit status is always 0: cross-model CPI deltas are findings, not failures.
"""

from __future__ import annotations

import argparse
import csv
import json
import os
import sys
from pathlib import Path

MAX_CPI_MILLI = 65535  # uint16_t field in bench_metrics.h; clamp, never truncate


def parse_run_csv(path: Path) -> dict[str, dict]:
    """bench-results-*.csv: test,status,cycles,retired,ipc (test = ELF basename)."""
    rows: dict[str, dict] = {}
    if not path.exists():
        return rows
    with path.open() as f:
        for row in csv.DictReader(f):
            name = (row.get("test") or row.get("name") or "").rsplit(".", 1)[0]
            if not name:
                continue
            rows[name] = {
                "status": row.get("status", ""),
                "cycles": int(row.get("cycles") or 0),
                "retired": int(row.get("retired") or 0),
            }
    return rows


def parse_bench_csv(path: Path) -> dict[str, tuple[int | None, int | None]]:
    """bench-metrics.csv: name,throughput_cpi_milli,latency_cpi_milli."""
    rows: dict[str, tuple[int | None, int | None]] = {}
    if not path.exists():
        return rows
    with path.open() as f:
        for row in csv.DictReader(f):
            names = row.get("name", "").strip()
            if not names or names.startswith("name"):
                continue
            thr = _int_or_none(row.get("throughput_cpi_milli"))
            lat = _int_or_none(row.get("latency_cpi_milli"))
            rows[names] = (thr, lat)
    return rows


def _int_or_none(s: str | None) -> int | None:
    if s is None or s.strip() in ("", "-"):
        return None
    try:
        return int(s.strip())
    except ValueError:
        return None


def strip_march(name: str) -> str:
    """ELF basename -> spec name: fp_fadd_s -> fadd_s, amo_amoadd_w -> amoadd_w."""
    for prefix in ("fp_", "amo_", "zb_"):
        if name.startswith(prefix):
            return name[len(prefix):]
    return name


def unit_cpi_milli(cycles: int, retired: int) -> int | None:
    if cycles <= 0 or retired <= 0:
        return None
    return min((cycles * 1000) // retired, MAX_CPI_MILLI)


def emit_header(benchmarks: list[dict], out: Path) -> None:
    cpp_dir = out.parent / "cpp_sim"
    cpp_dir.mkdir(parents=True, exist_ok=True)
    lines = [
        "// Auto-generated from measured benchmark data. DO NOT EDIT.",
        "// Regenerate with: make run-benchmarks bench-cppsim bench-compare",
        "//",
        "// cpi_milli is cycles-per-instruction * 1000 (1000 == 1.0 CPI).",
        "// latency_cpi_milli is 0 for benchmarks without a dependency chain.",
        "#pragma once",
        "",
        "#include <cstdint>",
        "",
        "struct BenchMetric {",
        "    const char* name;",
        "    uint16_t cpi_milli;",
        "    uint16_t latency_cpi_milli;",
        "};",
        "",
        "static constexpr BenchMetric kBENCH_METRICS[] = {",
    ]
    for b in benchmarks:
        thr = b["throughput_cpi_milli"] or 0
        lat = b["latency_cpi_milli"] or 0
        lines.append(f'    {{"{b["name"]}", {thr}, {lat}}},')
    lines.append("};")
    lines.append("")
    (cpp_dir / "bench_metrics.h").write_text("\n".join(lines))


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--rtl", type=Path, required=True)
    ap.add_argument("--cpp", type=Path, default=None)
    ap.add_argument("--programs", type=Path, required=True)
    ap.add_argument("--out", type=Path, default=Path("output/bench"))
    args = ap.parse_args()

    programs = json.loads(args.programs.read_text())
    rtl_run = parse_run_csv(args.rtl)
    cpp_run = parse_run_csv(args.cpp) if args.cpp and args.cpp.exists() else {}
    rtl_metrics = parse_bench_csv(args.out / "bench-metrics.csv")

    cpu_name = "unknown"
    config_mk = args.out.parent / "config.mk"
    if config_mk.exists():
        for line in config_mk.read_text().splitlines():
            if line.startswith("CPU_NAME :="):
                cpu_name = line.split(":=", 1)[1].strip()

    benchmarks: list[dict] = []
    for p in programs:
        name = p["name"]
        kind = p.get("kind", "throughput")
        thr_milli, lat_milli = rtl_metrics.get(name, (None, None))
        key = f"{p.get('march', '')}{name}"
        rtl = rtl_run.get(key, {})
        cpp = cpp_run.get(key, {})
        cpp_thr = unit_cpi_milli(cpp.get("cycles", 0), cpp.get("retired", 0))
        benchmarks.append({
            "name": name,
            "kind": kind,
            "throughput_cpi_milli": thr_milli,
            "latency_cpi_milli": lat_milli,
            "rtl_cycles": rtl.get("cycles"),
            "rtl_retired": rtl.get("retired"),
            "cppsim_throughput_cpi_milli": cpp_thr,
            "cppsim_retired": cpp.get("retired"),
        })

    merged = {
        "config": {"cpu": cpu_name, "source": "rtl-verilator"},
        "benchmarks": benchmarks,
    }
    args.out.mkdir(parents=True, exist_ok=True)
    (args.out / "bench-metrics.json").write_text(json.dumps(merged, indent=2) + "\n")
    emit_header(benchmarks, args.out)

    # Informational delta table (no failures: model fidelity, not correctness).
    print(f"benchmark deltas vs LeanSim (cpu={cpu_name})")
    print(f"{'name':<18}{'rtl_thr':>9}{'rtl_lat':>9}{'cpp_thr':>9}{'delta':>9}")
    n_with_cpp = 0
    sum_delta = 0.0
    for b in benchmarks:
        thr = b["throughput_cpi_milli"]
        cpp = b["cppsim_throughput_cpi_milli"]
        delta = ""
        if thr is not None and cpp is not None:
            d = cpp - thr
            delta = f"{d:+d}"
            n_with_cpp += 1
            sum_delta += abs(d)
        print(f'{b["name"]:<18}{str(thr or "-"):>9}{str(b["latency_cpi_milli"] or "-"):>9}'
              f'{str(cpp or "-"):>9}{delta:>9}')
    if n_with_cpp:
        print(f"\nmean |delta| over {n_with_cpp} instrs: {sum_delta / n_with_cpp:.1f} cpi_milli")
    return 0


if __name__ == "__main__":
    sys.exit(main())