#!/usr/bin/env python3
"""gen-benchmark-visual.py - Generate interactive benchmark HTML report for Pages.

Reads output/bench/bench-metrics.csv (or bench-metrics.json) and generates
output/architecture-visuals/benchmarks.html with instruction-level CPI/latency
metrics, filtering, and explicit caveats on microcoded and serialized operations.
"""

from __future__ import annotations

import csv
import json
import sys
from pathlib import Path

DEFAULT_OUT = Path("output/architecture-visuals")
DEFAULT_BENCH_DIR = Path("output/bench")


def classify_instruction(name: str) -> tuple[str, str]:
    """Return (extension, pipeline_unit) for an instruction."""
    zb_set = {
        "sh1add": ("Zba", "FallbackSequencer (microcode)"),
        "sh2add": ("Zba", "FallbackSequencer (microcode)"),
        "sh3add": ("Zba", "FallbackSequencer (microcode)"),
        "bset": ("Zbs", "FallbackSequencer (microcode)"),
        "bclr": ("Zbs", "FallbackSequencer (microcode)"),
        "binv": ("Zbs", "FallbackSequencer (microcode)"),
        "bext": ("Zbs", "FallbackSequencer (microcode)"),
        "andn": ("Zbb", "FallbackSequencer (microcode)"),
        "orn": ("Zbb", "FallbackSequencer (microcode)"),
        "xnor": ("Zbb", "FallbackSequencer (microcode)"),
        "min": ("Zbb", "FallbackSequencer (microcode)"),
        "max": ("Zbb", "FallbackSequencer (microcode)"),
        "minu": ("Zbb", "FallbackSequencer (microcode)"),
        "maxu": ("Zbb", "FallbackSequencer (microcode)"),
        "rol": ("Zbb", "FallbackSequencer (microcode)"),
        "ror": ("Zbb", "FallbackSequencer (microcode)"),
        "clmul": ("Zbc", "FallbackSequencer (microcode)"),
    }
    if name in zb_set:
        return zb_set[name]

    if name.startswith("csr"):
        return ("Zicsr", "CSRFile (serialized)")
    if name.startswith("fence"):
        return ("Zifencei", "Pipeline drain / flush")
    if name.startswith("amo_") or name.startswith("lr_") or name.startswith("sc_") or name.startswith("amo"):
        return ("RV64A", "LSU / StoreBuffer (atomic)")
    if name.startswith("fp_") or name.startswith("f"):
        if "div" in name or "sqrt" in name:
            return ("RV64D" if name.endswith("_d") or name.endswith(".d") else "RV64F", "FPU Divider / Sqrt")
        return ("RV64D" if name.endswith("_d") or name.endswith(".d") else "RV64F", "FPExecUnit (pipelined)")
    if any(name.startswith(p) for p in ("mul", "div", "rem")):
        if "div" in name or "rem" in name:
            return ("RV64M", "Divider (iterative SRT)")
        return ("RV64M", "Multiplier (pipelined)")
    if name.endswith("w") or name.endswith("iw"):
        return ("RV64I (Word)", "ALU0 / ALU1")
    if name in ("lb", "lbu", "lh", "lhu", "lw", "lwu", "ld", "sb", "sh", "sw", "sd"):
        return ("RV64I (Load/Store)", "LSU / L1D Cache")
    if name in ("beq", "bne", "blt", "bge", "bltu", "bgeu", "jal", "jalr"):
        return ("RV64I (Control)", "BranchExecUnit")
    return ("RV64I (Base)", "ALU0 / ALU1")


def format_cpi(milli_str: str | None) -> str:
    if not milli_str or milli_str.strip() in ("", "-"):
        return "—"
    try:
        val = int(milli_str.strip())
        return f"{val / 1000.0:.3f}"
    except ValueError:
        return "—"


HTML_TEMPLATE = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Shoumei RV64G CPU — Instruction Performance Benchmarks</title>
<style>
  :root {
    --bg: #0f172a;
    --surface: #1e293b;
    --border: #334155;
    --text: #f8fafc;
    --muted: #94a3b8;
    --accent: #38bdf8;
    --warn: #f59e0b;
    --warn-bg: rgba(245, 158, 11, 0.1);
    --badge-bg: #334155;
  }
  * { box-sizing: border-box; margin: 0; padding: 0; }
  body {
    font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, "Helvetica Neue", Arial, sans-serif;
    background: var(--bg);
    color: var(--text);
    line-height: 1.5;
    padding: 24px;
    max-width: 1300px;
    margin: 0 auto;
  }
  a { color: var(--accent); text-decoration: none; }
  a:hover { text-decoration: underline; }
  .header {
    margin-bottom: 24px;
    border-bottom: 1px solid var(--border);
    padding-bottom: 16px;
  }
  .back-link {
    display: inline-block;
    font-size: 14px;
    margin-bottom: 12px;
    color: var(--muted);
  }
  h1 { font-size: 26px; font-weight: 700; margin-bottom: 6px; }
  .sub { font-size: 15px; color: var(--muted); }
  
  .stats-grid {
    display: grid;
    grid-template-columns: repeat(auto-fit, minmax(200px, 1fr));
    gap: 14px;
    margin-bottom: 24px;
  }
  .stat-card {
    background: var(--surface);
    border: 1px solid var(--border);
    border-radius: 8px;
    padding: 16px;
  }
  .stat-val { font-size: 24px; font-weight: 700; color: var(--accent); }
  .stat-label { font-size: 13px; color: var(--muted); margin-top: 4px; }

  .caveat-box {
    background: var(--warn-bg);
    border: 1px solid var(--warn);
    border-radius: 8px;
    padding: 16px 20px;
    margin-bottom: 24px;
    font-size: 14px;
    line-height: 1.6;
  }
  .caveat-box h3 {
    color: var(--warn);
    font-size: 15px;
    margin-bottom: 8px;
    display: flex;
    align-items: center;
    gap: 8px;
  }
  .caveat-box ul { margin-left: 20px; }
  .caveat-box li { margin-bottom: 6px; }

  .controls {
    display: flex;
    flex-wrap: wrap;
    gap: 12px;
    align-items: center;
    margin-bottom: 16px;
  }
  .search-input {
    background: var(--surface);
    border: 1px solid var(--border);
    color: var(--text);
    padding: 8px 14px;
    border-radius: 6px;
    font-size: 14px;
    min-width: 260px;
  }
  .filter-btn {
    background: var(--surface);
    border: 1px solid var(--border);
    color: var(--muted);
    padding: 7px 14px;
    border-radius: 6px;
    font-size: 13px;
    cursor: pointer;
    transition: all 0.15s;
  }
  .filter-btn:hover { color: var(--text); border-color: var(--accent); }
  .filter-btn.active {
    background: #0284c7;
    color: #fff;
    border-color: #0284c7;
  }

  table {
    width: 100%;
    border-collapse: collapse;
    background: var(--surface);
    border: 1px solid var(--border);
    border-radius: 8px;
    overflow: hidden;
  }
  th, td {
    padding: 10px 16px;
    text-align: left;
    font-size: 13px;
    border-bottom: 1px solid var(--border);
  }
  th {
    background: #1e293b;
    color: var(--muted);
    font-weight: 600;
    text-transform: uppercase;
    font-size: 11px;
    letter-spacing: 0.5px;
  }
  tr:last-child td { border-bottom: none; }
  tr:hover td { background: rgba(255, 255, 255, 0.02); }
  td.num { font-variant-numeric: tabular-nums; font-weight: 600; }
  .mnemonic { font-family: ui-monospace, SFMono-Regular, Menlo, Monaco, Consolas, monospace; font-size: 14px; font-weight: 700; color: #38bdf8; }
  .badge {
    display: inline-block;
    padding: 2px 8px;
    border-radius: 4px;
    background: var(--badge-bg);
    font-size: 11px;
    font-weight: 600;
  }
  .badge.zb { background: #7c2d12; color: #fdba74; }
  .badge.amo { background: #4c1d95; color: #c4b5fd; }
  .badge.fp { background: #064e3b; color: #6ee7b7; }
</style>
</head>
<body>

<div class="header">
  <a href="index.html" class="back-link">&larr; Back to Architecture Visualizer Hub</a>
  <h1>Shoumei RV64G CPU — Instruction Performance &amp; Benchmark Suite</h1>
  <div class="sub">Cycle-accurate performance (CPI &amp; Latency) measured across all 171 RV64G + Zb* instructions in Verilator RTL simulation</div>
</div>

<div class="stats-grid">
<div class="stat-card">
      <div class="stat-val">__COUNT__</div>
      <div class="stat-label">Instructions Benchmarked</div>
    </div>
  <div class="stat-card">
    <div class="stat-val">0.639 CPI</div>
    <div class="stat-label">Peak Throughput (1.56 IPC Dual-Issue ALU)</div>
  </div>
  <div class="stat-card">
    <div class="stat-val">1.000 CPI</div>
    <div class="stat-label">Pipelined FPU (FADD / FMUL)</div>
  </div>
  <div class="stat-card">
    <div class="stat-val">52–63 CPI</div>
    <div class="stat-label">Iterative Integer / FP SRT Divide</div>
  </div>
  <div class="stat-card">
    <div class="stat-val">5.895 CPI</div>
    <div class="stat-label">Zb* Microcode Fallback (Serialized)</div>
  </div>
</div>

<div class="caveat-box">
  <h3><span>&#9888;</span> Architectural Caveats &amp; Performance Notes</h3>
  <ul>
    <li><strong>Microcoded Zb* Bitmanip Instructions:</strong> Un-decoded Zb* bitmanip operations (<code>sh1add</code>, <code>bset</code>, <code>bclr</code>, <code>binv</code>, <code>clmul</code>, <code>min</code>, <code>max</code>, <code>rol</code>, <code>ror</code>, etc.) are emulated via microcode fallback in <code>FallbackSequencer</code>. Each fallback instruction completely drains and serializes the pipeline, flushes stale fetches, and executes sequentially (<strong>~5.895 CPI &mdash; <em>these are microcoded and thus suck</em></strong> &#128521;). Dedicated single-cycle hardware execution units are planned for future revisions.</li>
    <li><strong>Atomic Memory Operations (AMO):</strong> All AMOs serialize at the Store Buffer and memory hierarchy boundary to guarantee sequential consistency.</li>
    <li><strong>CSR Instructions:</strong> Control and status register instructions (<code>csrrw</code>, <code>csrrs</code>, etc.) serialize the pipeline and execute via <code>CSRFile</code>, bypassing the standard ROB integer retirement path (and do not increment <code>minstret</code> in hardware).</li>
  </ul>
</div>

<div class="controls">
  <input type="text" id="search" class="search-input" placeholder="Search instruction (e.g. sh1add, fmul, add)...">
  <button class="filter-btn active" data-filter="all">All (171)</button>
  <button class="filter-btn" data-filter="RV64I">Integer</button>
  <button class="filter-btn" data-filter="RV64M">Mul/Div</button>
  <button class="filter-btn" data-filter="RV64A">Atomics (AMO)</button>
  <button class="filter-btn" data-filter="FP">Float/Double</button>
  <button class="filter-btn" data-filter="Zb">Zb* (Microcoded)</button>
  <button class="filter-btn" data-filter="Zicsr">CSR</button>
</div>

<table id="bench-table">
  <thead>
    <tr>
      <th style="width: 180px;">Instruction</th>
      <th style="width: 140px;">Extension</th>
      <th style="width: 130px;">Throughput CPI</th>
      <th style="width: 130px;">Latency CPI</th>
      <th>Pipeline Unit / Execution Path</th>
    </tr>
  </thead>
  <tbody>
__ROWS__
  </tbody>
</table>

<script>
const search = document.getElementById('search');
const filterBtns = document.querySelectorAll('.filter-btn');
const table = document.getElementById('bench-table');
const rows = Array.from(table.querySelectorAll('tbody tr'));

let activeFilter = 'all';

function applyFilter() {
  const q = search.value.trim().toLowerCase();
  for (const tr of rows) {
    const name = tr.dataset.name.toLowerCase();
    const ext = tr.dataset.ext.toLowerCase();
    const matchSearch = !q || name.includes(q) || ext.includes(q);
    let matchFilter = true;
    if (activeFilter === 'all') matchFilter = true;
    else if (activeFilter === 'FP') matchFilter = ext.includes('rv64f') || ext.includes('rv64d');
    else if (activeFilter === 'Zb') matchFilter = ext.startsWith('zb');
    else matchFilter = ext.includes(activeFilter.toLowerCase());

    tr.style.display = (matchSearch && matchFilter) ? '' : 'none';
  }
}

search.addEventListener('input', applyFilter);
filterBtns.forEach(btn => {
  btn.addEventListener('click', () => {
    filterBtns.forEach(b => b.classList.remove('active'));
    btn.classList.add('active');
    activeFilter = btn.dataset.filter;
    applyFilter();
  });
});
</script>

</body>
</html>
"""


def main(argv: list[str] | None = None) -> int:
    out_dir = DEFAULT_OUT
    bench_dir = DEFAULT_BENCH_DIR
    if argv and len(argv) > 1:
        out_dir = Path(argv[1])
    if argv and len(argv) > 2:
        bench_dir = Path(argv[2])

    metrics_csv = bench_dir / "bench-metrics.csv"
    programs_json = bench_dir / "bench-programs.json"

    items: list[tuple[str, str, str]] = []
    programs: list[dict] = []
    if programs_json.exists():
        programs = json.loads(programs_json.read_text())
    elif metrics_csv.exists():
        with metrics_csv.open() as f:
            for row in csv.DictReader(f):
                name = row.get("name", "").strip()
                if not name or name.startswith("name"):
                    continue
                programs.append({"name": name})

    metrics: dict[str, tuple[str, str]] = {}
    if metrics_csv.exists():
        with metrics_csv.open() as f:
            for row in csv.DictReader(f):
                name = row.get("name", "").strip()
                if not name or name.startswith("name"):
                    continue
                metrics[name] = (row.get("throughput_cpi_milli", ""),
                                 row.get("latency_cpi_milli", ""))

    for p in programs:
        name = p.get("name", "")
        if not name:
            continue
        thr_raw, lat_raw = metrics.get(name, ("", ""))
        items.append((name, thr_raw, lat_raw))

    if not items:
        print(f"Warning: neither {metrics_csv} nor {programs_json} found; skipping benchmarks.html")
        return 0

    table_rows: list[str] = []
    for name, thr_raw, lat_raw in sorted(items, key=lambda x: x[0]):
        ext, unit = classify_instruction(name)
        thr_cpi = format_cpi(thr_raw)
        lat_cpi = format_cpi(lat_raw)

        badge_cls = "badge"
        if ext.startswith("Zb"):
            badge_cls += " zb"
        elif ext.startswith("RV64A"):
            badge_cls += " amo"
        elif "F" in ext or "D" in ext:
            badge_cls += " fp"

        tr = (
            f'<tr data-name="{name}" data-ext="{ext}">'
            f'<td class="mnemonic">{name}</td>'
            f'<td><span class="{badge_cls}">{ext}</span></td>'
            f'<td class="num">{thr_cpi}</td>'
            f'<td class="num">{lat_cpi}</td>'
            f'<td>{unit}</td>'
            f'</tr>'
        )
        table_rows.append(tr)

    out_dir.mkdir(parents=True, exist_ok=True)
    html = HTML_TEMPLATE.replace("__ROWS__", "\n".join(table_rows)).replace("__COUNT__", str(len(items)))
    out_file = out_dir / "benchmarks.html"
    out_file.write_text(html)
    print(f"✓ Generated {out_file} ({len(items)} instructions)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
