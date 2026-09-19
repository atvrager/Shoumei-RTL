#!/usr/bin/env python3
"""gen-architecture-diagram.py - Generate an XKCD-style architecture treemap in SVG.

Generates a squarified treemap visualizing the hierarchical gate distribution of the
Shoumei Tomasulo RISC-V CPU, derived directly from the emitted SystemVerilog modules.

Usage:
  scripts/gen-architecture-diagram.py [--out docs/architecture-treemap.svg] [--png]
"""

from __future__ import annotations

import argparse
import logging
import re
import sys
from collections import defaultdict
from pathlib import Path

# Suppress matplotlib font discovery noise before importing matplotlib
logging.getLogger("matplotlib.font_manager").setLevel(logging.ERROR)

import matplotlib.patches as patches  # noqa: E402
import matplotlib.pyplot as plt  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
SV_DIR = ROOT / "output" / "sv-from-lean"
DEFAULT_TOP = "CPU_RV64IMAFD_Zicsr_Zifencei_Microcoded"
DEFAULT_OUT_SVG = ROOT / "docs" / "architecture-treemap.svg"

# Palette: Pastel comic colors for subsystems with corresponding border and inner tints
PALETTE = {
    "Register Renaming": {
        "bg": "#ffe5ec",
        "header": "#ffb3c6",
        "border": "#c9184a",
        "box_fill": "#fff0f3",
        "box_edge": "#800f2f",
    },
    "Execution Units": {
        "bg": "#fff3e6",
        "header": "#ffd8a8",
        "border": "#d9480f",
        "box_fill": "#fff9db",
        "box_edge": "#a61e4d",
    },
    "Retirement & CSRs": {
        "bg": "#f3f0ff",
        "header": "#d0bfff",
        "border": "#7048e8",
        "box_fill": "#f8f0fc",
        "box_edge": "#5f3dc4",
    },
    "Decode & Dispatch": {
        "bg": "#ebfbee",
        "header": "#b2f2bb",
        "border": "#2b8a3e",
        "box_fill": "#f4fce3",
        "box_edge": "#237032",
    },
    "Reservation Stations": {
        "bg": "#e7f5ff",
        "header": "#a5d8ff",
        "border": "#1971c2",
        "box_fill": "#f1f3f5",
        "box_edge": "#1864ab",
    },
    "Memory (LSU)": {
        "bg": "#e6fcf5",
        "header": "#96f2d7",
        "border": "#0ca678",
        "box_fill": "#e6faf5",
        "box_edge": "#099268",
    },
    "Fetch & Queues": {
        "bg": "#fff9db",
        "header": "#ffec99",
        "border": "#f59f00",
        "box_fill": "#fffbf0",
        "box_edge": "#e67700",
    },
    "Glue & Regs": {
        "bg": "#f8f9fa",
        "header": "#e9ecef",
        "border": "#495057",
        "box_fill": "#ffffff",
        "box_edge": "#343a40",
    },
}

SHORT_NAMES = {
    "Register Renaming": "Renaming",
    "Execution Units": "Execution",
    "Retirement & CSRs": "ROB & CSRs",
    "Reservation Stations": "Issue / RS",
    "Memory (LSU)": "Memory",
    "Fetch & Queues": "Fetch",
    "Decode & Dispatch": "Decode",
    "Glue & Regs": "Glue",
}

LABEL_CONVERSIONS = {
    "FP FMA (DP)": "FP FMA (DP)",
    "FP FMA (SP)": "FP FMA (SP)",
    "FP Multiplier (SP)": "FP Mul (SP)",
    "FP Multiplier (DP)": "FP Mul (DP)",
    "FP Adder (SP)": "FP Add (SP)",
    "FP Adder (DP)": "FP Add (DP)",
    "FP LongConverter (SP)": "FP Long Conv",
    "FP LongConverter": "FP Long Conv",
    "FP Divider (SP)": "FP Div (SP)",
    "FP Divider (DP)": "FP Div (DP)",
    "FP Sqrt (SP)": "FP Sqrt (SP)",
    "FP Sqrt (DP)": "FP Sqrt (DP)",
    "FP Misc (SP)": "FP Misc (SP)",
    "FP Misc (DP)": "FP Misc (DP)",
    "FP D_Misc (DP)": "FP Misc (DP)",
    "FP Converter (DP)": "FP D-Conv",
    "FP D_Converter (DP)": "FP D-Conv",
    "StoreBuffer8 (Speculative)": "StoreBuffer8",
    "Dual ALU (64b)": "Dual ALU (64b)",
    "Branch & Target Adders/Cmp": "Branch Logic",
    "RS Branch (2-Entry)": "RS Branch",
    "RS MulDiv (2-Entry)": "RS MulDiv",
    "RS Mem (2-Entry)": "RS Mem",
    "RS FP (2-Entry)": "RS FP",
    "RS Int (4-Entry, W2)": "RS Integer",
    "Top Logic & Muxes": "Top Logic & Muxes",
    "Pipeline Staging Regs": "Pipeline Regs",
    "ROB16 (16-Entry, W2)": "ROB16 (16-Entry)",
    "CSRFile (RV64G)": "CSRFile (RV64G)",
    "TrapSequencer": "TrapSeq (Microcode)",
    "Insn Queue (16x32)": "Insn Queue",
    "PC Queue (16x32)": "PC Queue",
    "FetchStage (Dual-Issue)": "Fetch",
    "Mul64 (Pipelined)": "Mul64 (Pipelined)",
    "Div64 (Iterative)": "Div64 (Iterative)",
    "IntFreeList (W2)": "IntFreeList (W2)",
    "FPFreeList (W1)": "FPFreeList (W1)",
    "IntPRF (64x64)": "IntPRF (64x64)",
    "FPPRF (64x64)": "FPPRF (64x64)",
    "BusyTable (W2)": "BusyTable (W2)",
    "FPBusyTable": "FPBusyTable",
    "IntRAT 0": "IntRAT 0",
    "IntRAT 1": "IntRAT 1",
    "FPRAT": "FPRAT",
    "Int Rename Stage Logic": "Rename Muxes",
    "FP Rename Stage Logic": "FP Rename Muxes",
    "FP Output Mux & Rounding": "FP Result Mux",
    "RV64G Dec (x2)": "RV64G Dec",
}


class ModuleAnalyzer:
    """Parses SV files to extract instances and calculate gate counts."""

    def __init__(self, sv_dir: Path):
        self.sv_dir = sv_dir
        self._memo: dict[str, tuple[int, list[tuple[str, str]]]] = {}
        self._hier_memo: dict[str, int] = {}

    def get_module(self, name: str) -> tuple[int, list[tuple[str, str]]]:
        """Return (direct_gates, list_of_(module, inst_name))."""
        if name in self._memo:
            return self._memo[name]

        path = self.sv_dir / f"{name}.sv"
        if not path.exists():
            self._memo[name] = (0, [])
            return 0, []

        text = path.read_text()
        assigns = len(re.findall(r"^\s*assign\s+", text, re.MULTILINE))
        dffs = len(re.findall(r"^\s*always_ff\s+@", text, re.MULTILINE))
        direct_gates = 1 if name == "DFlipFlop" else (assigns + dffs)

        inst_pattern = re.compile(
            r"^\s*([A-Za-z0-9_]+)\s+([A-Za-z0-9_]+)\s*\(", re.MULTILINE
        )
        instances = []
        for mod, inst in inst_pattern.findall(text):
            if mod in ("module", "always_comb", "always_ff", "initial", "final"):
                continue
            if (self.sv_dir / f"{mod}.sv").exists():
                instances.append((mod, inst))

        self._memo[name] = (direct_gates, instances)
        return self._memo[name]

    def hier_gates(self, name: str) -> int:
        """Compute total hierarchical gates recursively."""
        if name in self._hier_memo:
            return self._hier_memo[name]

        direct, insts = self.get_module(name)
        total = direct + sum(self.hier_gates(m) for m, _ in insts)
        self._hier_memo[name] = total
        return total


def squarify(
    values: list[dict], x: float, y: float, width: float, height: float
) -> list[tuple[dict, float, float, float, float]]:
    """Bruls, Huizing, van Wijk squarified treemap algorithm."""
    if not values or width <= 0 or height <= 0:
        return []

    total = sum(v["size"] for v in values)
    if total <= 0:
        return []

    rects: list[tuple[dict, float, float, float, float]] = []
    area = width * height
    norm_values = [{"item": v, "area": (v["size"] / total) * area} for v in values]

    def worst_ratio(row: list[dict], w: float) -> float:
        if not row or w <= 0:
            return float("inf")
        s = sum(r["area"] for r in row)
        if s <= 0:
            return float("inf")
        max_a = max(r["area"] for r in row)
        min_a = min(r["area"] for r in row)
        w2 = w * w
        s2 = s * s
        return max((w2 * max_a) / s2, s2 / (w2 * min_a))

    def step(children: list[dict], cur_x: float, cur_y: float, cur_w: float, cur_h: float) -> None:
        if not children:
            return
        if cur_w <= 1e-6 or cur_h <= 1e-6:
            for c in children:
                rects.append((c["item"], cur_x, cur_y, 0.0, 0.0))
            return

        if cur_w < cur_h:
            w = cur_w
            row = [children[0]]
            for c in children[1:]:
                if worst_ratio(row + [c], w) <= worst_ratio(row, w):
                    row.append(c)
                else:
                    break
            row_area = sum(r["area"] for r in row)
            row_h = row_area / w if w > 0 else 0.0
            offset = 0.0
            for r in row:
                item_w = r["area"] / row_h if row_h > 0 else 0.0
                rects.append((r["item"], cur_x + offset, cur_y, item_w, row_h))
                offset += item_w
            rem = children[len(row):]
            step(rem, cur_x, cur_y + row_h, cur_w, cur_h - row_h)
        else:
            w = cur_h
            row = [children[0]]
            for c in children[1:]:
                if worst_ratio(row + [c], w) <= worst_ratio(row, w):
                    row.append(c)
                else:
                    break
            row_area = sum(r["area"] for r in row)
            row_w = row_area / w if w > 0 else 0.0
            offset = 0.0
            for r in row:
                item_h = r["area"] / row_w if row_w > 0 else 0.0
                rects.append((r["item"], cur_x, cur_y + offset, row_w, item_h))
                offset += item_h
            rem = children[len(row):]
            step(rem, cur_x + row_w, cur_y, cur_w - row_w, cur_h)

    norm_values.sort(key=lambda v: v["item"]["size"], reverse=True)
    step(norm_values, float(x), float(y), float(width), float(height))
    return rects


def build_cpu_hierarchy(analyzer: ModuleAnalyzer, top_name: str) -> dict[str, list[dict]]:
    """Organize CPU modules into architectural subsystems with 100% gate accounting."""
    top_direct, top_insts = analyzer.get_module(top_name)

    subsystems: dict[str, list[dict]] = defaultdict(list)
    branch_target_sum = 0
    fpu_lut_sum = 0
    alu_lut_sum = 0
    decoder_sum = 0

    for mod, inst in top_insts:
        # Register Renaming
        if inst == "u_rename":
            ren_direct, sub_insts = analyzer.get_module(mod)
            extra_glue = 0
            for sm, si in sub_insts:
                g = analyzer.hier_gates(sm)
                if "FreeList" in sm:
                    subsystems["Register Renaming"].append({"name": "IntFreeList (W2)", "inst": si, "mod": sm, "size": g})
                elif "PhysReg" in sm:
                    subsystems["Register Renaming"].append({"name": "IntPRF (64x64)", "inst": si, "mod": sm, "size": g})
                elif "IntRAT" in sm:
                    idx = "0" if "0" in si else "1"
                    subsystems["Register Renaming"].append({"name": f"IntRAT {idx}", "inst": si, "mod": sm, "size": g})
                else:
                    extra_glue += g
            subsystems["Register Renaming"].append({"name": "Int Rename Stage Logic", "inst": "u_rename_logic", "mod": "Glue", "size": ren_direct + extra_glue})
        elif inst == "u_fp_rename":
            fp_ren_direct, sub_insts = analyzer.get_module(mod)
            fp_extra_glue = 0
            for sm, si in sub_insts:
                g = analyzer.hier_gates(sm)
                if "FreeList" in sm:
                    subsystems["Register Renaming"].append({"name": "FPFreeList (W1)", "inst": si, "mod": sm, "size": g})
                elif "PhysReg" in sm:
                    subsystems["Register Renaming"].append({"name": "FPPRF (64x64)", "inst": si, "mod": sm, "size": g})
                elif sm == "RAT_32x6":
                    subsystems["Register Renaming"].append({"name": "FPRAT", "inst": si, "mod": sm, "size": g})
                else:
                    fp_extra_glue += g
            subsystems["Register Renaming"].append({"name": "FP Rename Stage Logic", "inst": "u_fp_rename_logic", "mod": "Glue", "size": fp_ren_direct + fp_extra_glue})
        elif inst == "u_busy_table":
            subsystems["Register Renaming"].append({"name": "BusyTable (W2)", "inst": inst, "mod": mod, "size": analyzer.hier_gates(mod)})
        elif inst == "u_fp_busy_table":
            subsystems["Register Renaming"].append({"name": "FPBusyTable", "inst": inst, "mod": mod, "size": analyzer.hier_gates(mod)})

        # Execution Units
        elif inst == "u_exec_fp":
            fpu_direct, sub_insts = analyzer.get_module(mod)
            if fpu_direct > 0:
                subsystems["Execution Units"].append({"name": "FP Output Mux & Rounding", "inst": "u_fpu_mux", "mod": "Glue", "size": fpu_direct})
            for sm, si in sub_insts:
                g = analyzer.hier_gates(sm)
                label = sm.replace("FPDouble", "FP D_").replace("FP", "")
                if label.endswith("D") and not label.endswith("FPD"):
                    label = label[:-1] + " (DP)"
                elif not label.endswith(")"):
                    label = label + " (SP)"
                subsystems["Execution Units"].append({"name": f"FP {label}", "inst": si, "mod": sm, "size": g})
        elif inst == "u_exec_muldiv":
            muldiv_direct, sub_insts = analyzer.get_module(mod)
            for sm, si in sub_insts:
                g = analyzer.hier_gates(sm)
                label = "Mul64 (Pipelined)" if "Mul" in sm else "Div64 (Iterative)"
                subsystems["Execution Units"].append({"name": label, "inst": si, "mod": sm, "size": g})
            if muldiv_direct > 0:
                branch_target_sum += muldiv_direct
        elif inst == "u_exec":
            subsystems["Execution Units"].append({"name": "Dual ALU (64b)", "inst": inst, "mod": mod, "size": analyzer.hier_gates(mod)})
        elif inst in ("u_auipc_adder_0", "u_auipc_adder_1", "u_br_target", "u_jalr_target", "u_br_cmp", "u_atom_cmp", "u_atom_cmp_u"):
            branch_target_sum += analyzer.hier_gates(mod)

        # Retirement & Control
        elif inst == "u_rob":
            subsystems["Retirement & CSRs"].append({"name": "ROB16 (16-Entry, W2)", "inst": inst, "mod": mod, "size": analyzer.hier_gates(mod)})
        elif inst == "u_csr_file":
            subsystems["Retirement & CSRs"].append({"name": "CSRFile (RV64G)", "inst": inst, "mod": mod, "size": analyzer.hier_gates(mod)})
        elif inst == "u_trap_seq":
            subsystems["Retirement & CSRs"].append({"name": "TrapSequencer", "inst": inst, "mod": mod, "size": analyzer.hier_gates(mod)})

        # Decode & Dispatch
        elif "lut" in inst or "Decoder" in mod:
            if "FPU" in mod:
                fpu_lut_sum += analyzer.hier_gates(mod)
            elif "ALU" in mod:
                alu_lut_sum += analyzer.hier_gates(mod)
            elif "RV64G" in mod:
                decoder_sum += analyzer.hier_gates(mod)
            elif "AMO" in mod:
                subsystems["Decode & Dispatch"].append({"name": "AMO Dec", "inst": inst, "mod": mod, "size": analyzer.hier_gates(mod)})
            elif "MulDiv" in mod:
                subsystems["Decode & Dispatch"].append({"name": "MulDiv Dec", "inst": inst, "mod": mod, "size": analyzer.hier_gates(mod)})
            else:
                subsystems["Decode & Dispatch"].append({"name": mod.replace("OpDecoder_RV64IMAFD_Zicsr_Zifencei_Microcoded", "Decoder"), "inst": inst, "mod": mod, "size": analyzer.hier_gates(mod)})

        # Reservation Stations
        elif inst.startswith("u_rs_"):
            name_map = {
                "u_rs_int": "RS Int (4-Entry, W2)",
                "u_rs_fp": "RS FP (2-Entry)",
                "u_rs_memory": "RS Mem (2-Entry)",
                "u_rs_branch": "RS Branch (2-Entry)",
                "u_rs_muldiv": "RS MulDiv (2-Entry)",
            }
            subsystems["Reservation Stations"].append({"name": name_map.get(inst, inst), "inst": inst, "mod": mod, "size": analyzer.hier_gates(mod)})

        # Memory Subsystem
        elif inst == "u_lsu":
            lsu_direct, sub_insts = analyzer.get_module(mod)
            for sm, si in sub_insts:
                g = analyzer.hier_gates(sm)
                if "StoreBuffer" in sm:
                    subsystems["Memory (LSU)"].append({"name": "StoreBuffer8 (Speculative)", "inst": si, "mod": sm, "size": g})
                else:
                    subsystems["Memory (LSU)"].append({"name": "AGU (MemoryExec)", "inst": si, "mod": sm, "size": g + lsu_direct})

        # Fetch & Queues
        elif inst in ("u_fetch", "u_pc_queue", "u_insn_queue"):
            name_map = {
                "u_fetch": "FetchStage (Dual-Issue)",
                "u_pc_queue": "PC Queue (16x32)",
                "u_insn_queue": "Insn Queue (16x32)",
            }
            subsystems["Fetch & Queues"].append({"name": name_map.get(inst, inst), "inst": inst, "mod": mod, "size": analyzer.hier_gates(mod)})

        else:
            subsystems["Glue & Regs"].append({"name": inst, "inst": inst, "mod": mod, "size": analyzer.hier_gates(mod)})

    # Decode consolidated items
    if fpu_lut_sum > 0:
        subsystems["Decode & Dispatch"].append({"name": "FPU OpDecoder", "inst": "u_fpu_lut", "mod": "FPUOpDecoder", "size": fpu_lut_sum})
    if alu_lut_sum > 0:
        subsystems["Decode & Dispatch"].append({"name": "ALU Decoder (x2)", "inst": "u_alu_lut0/1", "mod": "ALUOpDecoder", "size": alu_lut_sum})
    if decoder_sum > 0:
        subsystems["Decode & Dispatch"].append({"name": "RV64G Dec (x2)", "inst": "u_decoder_0/1", "mod": "RV64GDecoder", "size": decoder_sum})

    # Consolidated branch & target logic
    if branch_target_sum > 0:
        subsystems["Execution Units"].append({"name": "Branch & Target Adders/Cmp", "inst": "u_br_target_group", "mod": "Adders/Cmp", "size": branch_target_sum})

    # Top-level direct gates (assigns + DFFs)
    if top_direct > 0:
        subsystems["Glue & Regs"].append({"name": "Top Logic & Muxes", "inst": "top_glue", "mod": "Glue", "size": top_direct})

    # Consolidate all pipeline registers & glue (< 100 gates) into single block
    consolidated_glue = []
    tiny_sum = 0
    for it in subsystems["Glue & Regs"]:
        if it["size"] < 100 and it["name"] != "Top Logic & Muxes":
            tiny_sum += it["size"]
        else:
            consolidated_glue.append(it)
    if tiny_sum > 0:
        consolidated_glue.append({"name": "Pipeline Staging Regs", "inst": "u_pipe_regs", "mod": "Regs", "size": tiny_sum})
    subsystems["Glue & Regs"] = consolidated_glue

    return dict(subsystems)


def format_box_text(
    name: str,
    gates: int,
    pct: float,
    inst: str,
    bw: float,
    bh: float,
) -> tuple[str, float]:
    """Format label text lines and calculate optimal font size to fit box bounds."""
    # Horizontal strip special case
    if bh < 1.6 and bw > 7.0:
        label = f"{name} • {gates:,}g ({pct:.1f}%)"
        fs = max(5.5, min(7.5, (bw * 0.80) / (len(label) * 0.046)))
        return label, fs

    lines = [name]

    # Subtitle line: gate count & percentage
    if bw >= 7.5 and bh >= 3.2:
        lines.append(f"{gates:,} gates ({pct:.1f}%)")
    elif bw >= 3.5 and bh >= 1.6:
        lines.append(f"{gates:,}g ({pct:.1f}%)")
    elif bh >= 1.2:
        lines.append(f"{gates:,}g")

    # Instance name line for spacious boxes
    if inst and bw >= 8.5 and bh >= 4.0:
        lines.append(f"`{inst}`")

    num_lines = len(lines)
    max_len = max(len(l) for l in lines)

    # Compute font sizes that fit height and width independently with generous safety margins
    fs_h = (bh * 0.70) / (num_lines * 0.18)
    fs_w = (bw * 0.78) / (max_len * 0.046)
    fs = max(4.8, min(8.8, fs_h, fs_w))

    return "\n".join(lines), fs


def draw_treemap(
    subsystems: dict[str, list[dict]],
    total_cpu_gates: int,
    out_svg: Path,
    out_png: Path | None = None,
) -> None:
    """Render the squarified treemap using matplotlib and plt.xkcd."""
    sub_totals = []
    for name, items in subsystems.items():
        s = sum(it["size"] for it in items)
        sub_totals.append({"name": name, "size": s, "items": items})

    sub_totals.sort(key=lambda x: x["size"], reverse=True)

    with plt.xkcd(scale=0.85, length=100, randomness=1.6):
        fig, ax = plt.subplots(figsize=(18, 11), dpi=100)
        ax.set_xlim(0, 100)
        ax.set_ylim(0, 100)
        ax.axis("off")

        # Top title banner
        ax.text(
            50,
            97.6,
            "Shoumei Tomasulo RV64G CPU — Microarchitecture Gate Treemap",
            ha="center",
            va="center",
            fontsize=18,
            fontweight="bold",
            color="#212529",
        )
        ax.text(
            50,
            94.8,
            f"Formally Verified in Lean 4 • {total_cpu_gates:,} Total Hierarchical Gates • RV64IMAFD_Zicsr_Zifencei",
            ha="center",
            va="center",
            fontsize=11.5,
            color="#495057",
        )

        canvas_x, canvas_y = 2.0, 3.5
        canvas_w, canvas_h = 96.0, 88.5

        sub_rects = squarify(sub_totals, canvas_x, canvas_y, canvas_w, canvas_h)

        for sub_item, sx, sy, sw, sh in sub_rects:
            sub_name = sub_item["name"]
            sub_size = sub_item["size"]
            sub_pct = (sub_size / total_cpu_gates) * 100
            colors = PALETTE.get(
                sub_name,
                {
                    "bg": "#f8f9fa",
                    "header": "#e9ecef",
                    "border": "#495057",
                    "box_fill": "#ffffff",
                    "box_edge": "#343a40",
                },
            )

            pad = 0.4
            box_x = sx + pad
            box_y = sy + pad
            box_w = max(0.1, sw - 2 * pad)
            box_h = max(0.1, sh - 2 * pad)

            sub_patch = patches.FancyBboxPatch(
                (box_x, box_y),
                box_w,
                box_h,
                boxstyle="round,pad=0.2,rounding_size=0.6",
                facecolor=colors["bg"],
                edgecolor=colors["border"],
                linewidth=2.2,
                zorder=1,
            )
            ax.add_patch(sub_patch)

            # Subsystem Header Banner - single line with adaptive name
            header_h = min(3.5, max(2.2, box_h * 0.12))
            if box_w < 16.0:
                short = SHORT_NAMES.get(sub_name, sub_name)
                header_text = f"{short} [{sub_pct:.1f}%]"
                header_fs = max(7.5, min(9.5, box_w * 0.55))
            elif box_w < 22.0:
                header_text = f"{sub_name} [{sub_pct:.1f}%]"
                header_fs = max(8.0, min(10.5, box_w * 0.48))
            else:
                header_text = f"{sub_name}  [{sub_size:,} gates • {sub_pct:.1f}%]"
                header_fs = max(9.0, min(12.0, box_w * 0.45))

            ax.text(
                box_x + 0.7,
                box_y + box_h - (header_h * 0.52),
                header_text,
                ha="left",
                va="center",
                fontsize=header_fs,
                fontweight="bold",
                color=colors["border"],
                clip_on=True,
                zorder=4,
            )

            # Layout child modules inside subsystem
            inner_x = box_x + 0.45
            inner_y = box_y + 0.45
            inner_w = max(0.1, box_w - 0.9)
            inner_h = max(0.1, box_h - header_h - 0.5)

            items = sub_item["items"]
            child_rects = squarify(items, inner_x, inner_y, inner_w, inner_h)

            for c_item, cx, cy, cw, ch in child_rects:
                if cw < 0.2 or ch < 0.2:
                    continue

                c_pad = 0.16
                c_bx = cx + c_pad
                c_by = cy + c_pad
                c_bw = max(0.1, cw - 2 * c_pad)
                c_bh = max(0.1, ch - 2 * c_pad)

                c_patch = patches.FancyBboxPatch(
                    (c_bx, c_by),
                    c_bw,
                    c_bh,
                    boxstyle="round,pad=0.1,rounding_size=0.35",
                    facecolor=colors["box_fill"],
                    edgecolor=colors["box_edge"],
                    linewidth=1.2,
                    zorder=2,
                )
                ax.add_patch(c_patch)

                raw_name = c_item["name"]
                name = LABEL_CONVERSIONS.get(raw_name, raw_name)
                c_size = c_item["size"]
                c_pct = (c_size / total_cpu_gates) * 100

                box_text, fs = format_box_text(
                    name,
                    c_size,
                    c_pct,
                    c_item.get("inst", ""),
                    c_bw,
                    c_bh,
                )

                ax.text(
                    c_bx + c_bw / 2,
                    c_by + c_bh / 2,
                    box_text,
                    ha="center",
                    va="center",
                    multialignment="center",
                    linespacing=1.18,
                    fontsize=fs,
                    fontweight="bold" if fs >= 6.8 else "normal",
                    color="#1a1a1a",
                    clip_on=True,
                    zorder=3,
                )

        ax.text(
            canvas_x + 0.5,
            canvas_y - 1.8,
            "* Treemap area is directly proportional to hierarchical gate count (combinational assigns + sequential flip-flops).",
            ha="left",
            va="center",
            fontsize=8.5,
            fontstyle="italic",
            color="#6c757d",
        )
        ax.text(
            canvas_x + canvas_w - 0.5,
            canvas_y - 1.8,
            "Generated by scripts/gen-architecture-diagram.py",
            ha="right",
            va="center",
            fontsize=8.5,
            color="#6c757d",
        )

        out_svg.parent.mkdir(parents=True, exist_ok=True)
        fig.savefig(out_svg, bbox_inches="tight", pad_inches=0.2)
        print(f"Exported architecture treemap SVG to: {out_svg}")

        if out_png:
            out_png.parent.mkdir(parents=True, exist_ok=True)
            fig.savefig(out_png, bbox_inches="tight", pad_inches=0.2, dpi=120)
            print(f"Exported architecture treemap PNG to: {out_png}")

        plt.close(fig)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Generate an XKCD-style architecture treemap in SVG."
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=DEFAULT_OUT_SVG,
        help=f"Output SVG path (default: {DEFAULT_OUT_SVG})",
    )
    parser.add_argument(
        "--png",
        action="store_true",
        help="Also export a PNG alongside the SVG for easy raster viewing",
    )
    parser.add_argument(
        "--top",
        type=str,
        default=DEFAULT_TOP,
        help=f"Top-level module name (default: {DEFAULT_TOP})",
    )
    args = parser.parse_args()

    if not SV_DIR.exists():
        print(
            f"Error: {SV_DIR} does not exist. Run 'make codegen' or 'lake exe generate_all' first.",
            file=sys.stderr,
        )
        return 1

    analyzer = ModuleAnalyzer(SV_DIR)
    total_gates = analyzer.hier_gates(args.top)
    if total_gates == 0:
        print(f"Error: Top module {args.top} not found or has 0 gates.", file=sys.stderr)
        return 1

    subsystems = build_cpu_hierarchy(analyzer, args.top)
    out_png = args.out.with_suffix(".png") if args.png else None

    draw_treemap(subsystems, total_gates, args.out, out_png)
    return 0


if __name__ == "__main__":
    sys.exit(main())
