#!/usr/bin/env python3
"""extract-synth-stats.py - Extract and compare PPA metrics across Quad-Target matrix.

Targets:
  T1: CPU on GF180MCU (64 MHz)
  T2: CPU on ASAP7 7nm (1.0 GHz)
  T3: SoC on GF180MCU (64 MHz)
  T4: SoC on ASAP7 7nm (1.0 GHz)

Parses Yosys stat reports (`reports/area.rpt`) and outputs structured comparison
tables (ASCII, Markdown, or JSON) including peripheral delta overhead.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import asdict, dataclass
from pathlib import Path


@dataclass
class SynthMetrics:
    target_name: str
    platform: str
    design: str
    clock_freq_mhz: float
    num_cells: int = 0
    num_seq_cells: int = 0
    num_comb_cells: int = 0
    num_wires: int = 0
    num_wire_bits: int = 0
    chip_area_um2: float = 0.0
    seq_area_um2: float = 0.0
    comb_area_um2: float = 0.0
    report_found: bool = False


def parse_area_report(report_path: Path, target_name: str, platform: str, design: str, freq: float) -> SynthMetrics:
    metrics = SynthMetrics(target_name=target_name, platform=platform, design=design, clock_freq_mhz=freq)
    if not report_path.exists():
        return metrics

    metrics.report_found = True
    content = report_path.read_text()

    # Wires & wire bits
    m_wires = re.findall(r"^\s*(\d+)\s+-\s+wires", content, re.M)
    if m_wires:
        metrics.num_wires = int(m_wires[-1])
    else:
        m_w_alt = re.search(r"Number of wires:\s+(\d+)", content)
        if m_w_alt:
            metrics.num_wires = int(m_w_alt.group(1))

    m_bits = re.findall(r"^\s*(\d+)\s+-\s+wire bits", content, re.M)
    if m_bits:
        metrics.num_wire_bits = int(m_bits[-1])
    else:
        m_b_alt = re.search(r"Number of wire bits:\s+(\d+)", content)
        if m_b_alt:
            metrics.num_wire_bits = int(m_b_alt.group(1))

    # Total cells
    m_cells = re.findall(r"^\s*(\d+)\s+[0-9.eE+-]+\s+cells", content, re.M)
    if not m_cells:
        m_cells = re.findall(r"^\s*(\d+)\s+cells", content, re.M)
    if m_cells:
        metrics.num_cells = int(m_cells[-1])
    else:
        m_c_alt = re.search(r"Number of cells:\s+(\d+)", content)
        if m_c_alt:
            metrics.num_cells = int(m_c_alt.group(1))

    # Area (top module)
    m_area = re.findall(r"Chip area for (?:top )?module .*?:\s+([0-9.]+)", content)
    if m_area:
        metrics.chip_area_um2 = float(m_area[-1])

    m_seq_area = re.findall(r"of which (?:used for sequential elements:\s+|([0-9.]+)\s+is used for sequential elements)([0-9.]+)?", content)
    if m_seq_area:
        # group 0 or group 1
        last = m_seq_area[-1]
        val_str = last[0] if last[0] else last[1]
        if val_str:
            metrics.seq_area_um2 = float(val_str)
            metrics.comb_area_um2 = metrics.chip_area_um2 - metrics.seq_area_um2

    # Parse cell breakdown from the top-module section to count sequential cells
    top_section = content.split("Count including submodules")[-1] if "Count including submodules" in content else content
    cell_lines = re.findall(r"^\s*(\d+)\s+[0-9.eE+-]+\s+([a-zA-Z0-9_]+)\s*$", top_section, re.M)
    if not cell_lines:
        cell_lines = re.findall(r"^\s*(\d+)\s+([a-zA-Z0-9_]+)\s*$", top_section, re.M)
    seq_count = 0
    for item in cell_lines:
        count_str, cell_name = item[0], item[-1]
        name_lower = cell_name.lower()
        if any(k in name_lower for k in ("dff", "ffq", "flop", "latch", "seq")):
            seq_count += int(count_str)
    metrics.num_seq_cells = seq_count
    metrics.num_comb_cells = metrics.num_cells - seq_count

    return metrics


def format_delta(val_soc: float, val_cpu: float, is_pct: bool = True) -> str:
    if val_cpu <= 0 or val_soc <= 0:
        return "—"
    diff = val_soc - val_cpu
    pct = (diff / val_cpu) * 100.0
    if is_pct:
        return f"+{diff:.1f} ({pct:+.1f}%)" if diff >= 0 else f"{diff:.1f} ({pct:+.1f}%)"
    return f"+{int(diff)} ({pct:+.1f}%)" if diff >= 0 else f"{int(diff)} ({pct:+.1f}%)"


def generate_markdown_table(results: dict[str, SynthMetrics]) -> str:
    lines = [
        "## Shoumei Quad-Target Synthesis Comparison",
        "",
        "| Metric | GF180MCU CPU (T1) | GF180MCU SoC (T3) | GF180 Delta | ASAP7 CPU (T2) | ASAP7 SoC (T4) | ASAP7 Delta |",
        "| :--- | :--- | :--- | :--- | :--- | :--- | :--- |",
    ]

    t1 = results.get("T1")
    t2 = results.get("T2")
    t3 = results.get("T3")
    t4 = results.get("T4")

    def fmt_freq(t: SynthMetrics | None) -> str:
        if not t or not t.report_found:
            return "—"
        if t.clock_freq_mhz >= 1000.0:
            return f"{t.clock_freq_mhz / 1000.0:.1f} GHz"
        return f"{t.clock_freq_mhz:.0f} MHz"

    def cell(t: SynthMetrics | None, attr: str, fmt: str = "{}") -> str:
        if not t or not t.report_found:
            return "—"
        v = getattr(t, attr)
        return fmt.format(v)

    lines.append(
        f"| Clock Target | {fmt_freq(t1)} | {fmt_freq(t3)} | — | {fmt_freq(t2)} | {fmt_freq(t4)} | — |"
    )
    lines.append(
        f"| Total Cells | {cell(t1, 'num_cells', '{:,}')} | {cell(t3, 'num_cells', '{:,}')} | {format_delta(t3.num_cells if t3 else 0, t1.num_cells if t1 else 0, False)} | {cell(t2, 'num_cells', '{:,}')} | {cell(t4, 'num_cells', '{:,}')} | {format_delta(t4.num_cells if t4 else 0, t2.num_cells if t2 else 0, False)} |"
    )
    lines.append(
        f"| Sequential (FF) Cells | {cell(t1, 'num_seq_cells', '{:,}')} | {cell(t3, 'num_seq_cells', '{:,}')} | {format_delta(t3.num_seq_cells if t3 else 0, t1.num_seq_cells if t1 else 0, False)} | {cell(t2, 'num_seq_cells', '{:,}')} | {cell(t4, 'num_seq_cells', '{:,}')} | {format_delta(t4.num_seq_cells if t4 else 0, t2.num_seq_cells if t2 else 0, False)} |"
    )
    lines.append(
        f"| Combinational Cells | {cell(t1, 'num_comb_cells', '{:,}')} | {cell(t3, 'num_comb_cells', '{:,}')} | {format_delta(t3.num_comb_cells if t3 else 0, t1.num_comb_cells if t1 else 0, False)} | {cell(t2, 'num_comb_cells', '{:,}')} | {cell(t4, 'num_comb_cells', '{:,}')} | {format_delta(t4.num_comb_cells if t4 else 0, t2.num_comb_cells if t2 else 0, False)} |"
    )
    lines.append(
        f"| Chip Area (µm²) | {cell(t1, 'chip_area_um2', '{:,.1f}')} | {cell(t3, 'chip_area_um2', '{:,.1f}')} | {format_delta(t3.chip_area_um2 if t3 else 0, t1.chip_area_um2 if t1 else 0, True)} | {cell(t2, 'chip_area_um2', '{:,.1f}')} | {cell(t4, 'chip_area_um2', '{:,.1f}')} | {format_delta(t4.chip_area_um2 if t4 else 0, t2.chip_area_um2 if t2 else 0, True)} |"
    )
    lines.append(
        f"| Total Wires | {cell(t1, 'num_wires', '{:,}')} | {cell(t3, 'num_wires', '{:,}')} | {format_delta(t3.num_wires if t3 else 0, t1.num_wires if t1 else 0, False)} | {cell(t2, 'num_wires', '{:,}')} | {cell(t4, 'num_wires', '{:,}')} | {format_delta(t4.num_wires if t4 else 0, t2.num_wires if t2 else 0, False)} |"
    )
    lines.append("")
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(description="Extract synthesis statistics across quad-target matrix.")
    parser.add_argument("--json", action="store_true", help="Output JSON format")
    parser.add_argument("--markdown", action="store_true", help="Output Markdown table")
    parser.add_argument("--root", type=Path, default=Path("."), help="Project root directory")
    args = parser.parse_args()

    root = args.root.resolve()

    # Target directories
    targets = {
        "T1": (root / "syn_out_gf180_cpu" / "reports" / "area.rpt", "GF180MCU", "CachedCPU_RV64IMAFD_Zicsr_Zifencei_Microcoded_synth", 64.0),
        "T2": (root / "syn_out_asap7_cpu" / "reports" / "area.rpt", "ASAP7", "CachedCPU_RV64IMAFD_Zicsr_Zifencei_Microcoded_synth", 1000.0),
        "T3": (root / "syn_out_gf180_soc" / "reports" / "area.rpt", "GF180MCU", "Shoumei_SoC_synth", 64.0),
        "T4": (root / "syn_out_asap7_soc" / "reports" / "area.rpt", "ASAP7", "Shoumei_SoC_synth", 1000.0),
    }

    # Fallback to default directory names if specific ones do not exist
    if not (root / "syn_out_gf180_cpu" / "reports" / "area.rpt").exists() and (root / "syn_out_gf180" / "reports" / "area.rpt").exists():
        targets["T1"] = (root / "syn_out_gf180" / "reports" / "area.rpt", "GF180MCU", "CPU_synth", 64.0)

    if not (root / "syn_out_asap7_cpu" / "reports" / "area.rpt").exists() and (root / "syn_out_asap7" / "reports" / "area.rpt").exists():
        targets["T2"] = (root / "syn_out_asap7" / "reports" / "area.rpt", "ASAP7", "CPU_synth", 1000.0)

    results: dict[str, SynthMetrics] = {}
    for tid, (path, platform, design, freq) in targets.items():
        results[tid] = parse_area_report(path, tid, platform, design, freq)

    if args.json:
        data = {k: asdict(v) for k, v in results.items()}
        print(json.dumps(data, indent=2))
        return 0

    if args.markdown:
        print(generate_markdown_table(results))
        return 0

    # Default human-readable text
    print("=" * 70)
    print("  Shoumei Quad-Target Physical Synthesis Metrics")
    print("=" * 70)
    for tid in ("T1", "T2", "T3", "T4"):
        m = results[tid]
        status = "FOUND" if m.report_found else "NOT RUN YET"
        freq_str = f"{m.clock_freq_mhz / 1000.0:.1f} GHz" if m.clock_freq_mhz >= 1000.0 else f"{m.clock_freq_mhz:.0f} MHz"
        print(f"[{tid}] {m.platform} - {m.design} ({freq_str}): {status}")
        if m.report_found:
            print(f"     Cells: {m.num_cells:,} (Seq: {m.num_seq_cells:,}, Comb: {m.num_comb_cells:,})")
            print(f"     Area:  {m.chip_area_um2:,.2f} µm² (Seq: {m.seq_area_um2:,.2f} µm²)")
            print(f"     Wires: {m.num_wires:,} ({m.num_wire_bits:,} bits)")
    print("-" * 70)
    t1, t3 = results.get("T1"), results.get("T3")
    t2, t4 = results.get("T2"), results.get("T4")
    if t1 and t3 and t1.report_found and t3.report_found:
        print(f"GF180MCU Overhead (SoC vs CPU): {format_delta(t3.chip_area_um2, t1.chip_area_um2)} area, {format_delta(t3.num_cells, t1.num_cells, False)} cells, {format_delta(t3.num_seq_cells, t1.num_seq_cells, False)} FFs")
    if t2 and t4 and t2.report_found and t4.report_found:
        print(f"ASAP7 Overhead (SoC vs CPU):    {format_delta(t4.chip_area_um2, t2.chip_area_um2)} area, {format_delta(t4.num_cells, t2.num_cells, False)} cells, {format_delta(t4.num_seq_cells, t2.num_seq_cells, False)} FFs")
    print("=" * 70)

    return 0


if __name__ == "__main__":
    sys.exit(main())
