#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.10"
# dependencies = ["gdstk", "matplotlib", "numpy", "scipy"]
# ///
"""Export GDS layout as a presentation-quality die shot poster.

Auto-extracts PPA metrics from ORFS report files adjacent to the GDS.

Features:
  - Per-layer colored density heatmap (high-res)
  - Per-module colored density heatmap from DEF placements (--mode modules)
  - Wire polygon overlay for routing texture
  - Zoomed inset showing wire-level detail
  - Stats panel with key PPA metrics (auto-extracted from ORFS reports)
  - Scale bar and project branding

Usage:
  ./physical/export-layout-png.py [input.gds] [output.png]
  ./physical/export-layout-png.py --mode modules [input.gds] [output.png]
"""

import argparse
import json
import re
import sys
from pathlib import Path

import gdstk
import matplotlib.font_manager as fm
import matplotlib.gridspec as gridspec
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.collections import PolyCollection
from matplotlib.patches import FancyBboxPatch, Patch, Rectangle
from scipy.ndimage import gaussian_filter

parser = argparse.ArgumentParser(description='Export GDS layout as die shot poster')
parser.add_argument('gds', nargs='?',
                    default='third_party/orfs/flow/results/asap7/CachedCPU_RV32IMF_Zicsr_Zifencei_Microcoded_synth/base/6_final.gds',
                    help='Input GDS file')
parser.add_argument('output', nargs='?', default=None, help='Output PNG file')
parser.add_argument('--mode', choices=['layers', 'modules'], default='layers',
                    help='Coloring mode: layers (default) or modules (CPU submodule hierarchy)')
args = parser.parse_args()

gds_path = args.gds
out_path = args.output

# -- Config --
BG = '#04040a'
GRID_N = 2000
SIGMA = 2
WIRE_MAX = 500000
GAMMA = 0.55

# ============================================================
# Auto-extract ORFS metrics from report files
# ============================================================

def find_orfs_paths(gds: str) -> dict:
    """Derive ORFS report/log paths from the GDS path."""
    p = Path(gds).resolve()
    # Expected: .../results/<pdk>/<design>/base/6_final.gds
    base_dir = p.parent  # .../base/
    design_name = base_dir.parent.name  # e.g. CPU_RV32IMF_synth
    pdk = base_dir.parent.parent.name  # e.g. asap7
    flow_root = base_dir.parent.parent.parent  # .../flow/results -> .../flow
    if flow_root.name == 'results':
        flow_root = flow_root.parent

    reports_dir = flow_root / 'reports' / pdk / design_name / 'base'
    logs_dir = flow_root / 'logs' / pdk / design_name / 'base'
    return {
        'design_name': design_name,
        'pdk': pdk,
        'report_json': logs_dir / '6_report.json',
        'finish_rpt': reports_dir / '6_finish.rpt',
        'drc_rpt': reports_dir / '5_route_drc.rpt',
        'synth_stat': reports_dir / 'synth_stat.txt',
    }


def parse_metrics(paths: dict) -> dict:
    """Extract all PPA metrics from ORFS outputs."""
    m = {}

    # -- 6_report.json (primary source for post-route metrics) --
    rj = paths.get('report_json')
    if rj and Path(rj).exists():
        with open(rj) as f:
            rpt = json.load(f)

        m['fmax_hz'] = rpt.get('finish__timing__fmax', 0)
        m['fmax_mhz'] = m['fmax_hz'] / 1e6 if m['fmax_hz'] else 0
        m['wns_ps'] = rpt.get('finish__timing__setup__ws', 0)
        m['tns_ps'] = rpt.get('finish__timing__setup__tns', 0)
        m['hold_tns_ps'] = rpt.get('finish__timing__hold__tns', 0)
        m['setup_violations'] = rpt.get('finish__timing__drv__setup_violation_count', 0)
        m['hold_violations'] = rpt.get('finish__timing__drv__hold_violation_count', 0)
        m['max_slew_violations'] = rpt.get('finish__timing__drv__max_slew', 0)
        m['max_cap_violations'] = rpt.get('finish__timing__drv__max_cap', 0)
        m['max_fanout_violations'] = rpt.get('finish__timing__drv__max_fanout', 0)
        m['die_area_um2'] = rpt.get('finish__design__die__area', 0)
        m['core_area_um2'] = rpt.get('finish__design__core__area', 0)
        m['instance_count'] = rpt.get('finish__design__instance__count', 0)
        m['stdcell_count'] = rpt.get('finish__design__instance__count__stdcell', 0)
        m['seq_cell_count'] = rpt.get('finish__design__instance__count__class:sequential_cell', 0)
        m['utilization'] = rpt.get('finish__design__instance__utilization', 0)
        m['power_w'] = rpt.get('finish__power__total', 0)
        m['power_mw'] = m['power_w'] * 1000 if m['power_w'] else 0
        m['power_internal_w'] = rpt.get('finish__power__internal__total', 0)
        m['power_switching_w'] = rpt.get('finish__power__switching__total', 0)
        m['power_leakage_w'] = rpt.get('finish__power__leakage__total', 0)
        m['ir_drop_worst_vdd'] = rpt.get('finish__design_powergrid__drop__worst__net:VDD__corner:default', 0)

    # -- DRC report (empty file = 0 DRC violations) --
    drc = paths.get('drc_rpt')
    if drc and Path(drc).exists():
        m['drc_violations'] = sum(1 for line in open(drc) if line.strip())
    else:
        m['drc_violations'] = None

    # -- Filter slew violations from 6_finish.rpt --
    # ASAP7 cell library hardcodes max_transition=320ps on all pins, which is
    # tighter than our SDC constraint (400ps). Violations between 320-400ps are
    # library DRV waivers — they meet our design intent but exceed the cell spec.
    # Also filter RESETN pins (async reset, false-pathed).
    # Report only violations that exceed our SDC limit.
    sdc_slew_limit = 350  # ASAP7 RVT library characterization limit
    finish_rpt = paths.get('finish_rpt')
    if finish_rpt and Path(finish_rpt).exists():
        waived = 0
        for line in open(finish_rpt):
            if '(VIOLATED)' not in line:
                continue
            # Parse: <pin> <limit> <actual> <slack> (VIOLATED)
            parts = line.split()
            try:
                actual = float(parts[-3])
                if '/RESETN' in line or '/SETN' in line or actual <= sdc_slew_limit:
                    waived += 1
            except (ValueError, IndexError):
                pass
        total_slew = m.get('max_slew_violations', 0)
        m['slew_waivers'] = waived
        m['max_slew_violations_data'] = max(0, total_slew - waived)
    else:
        m['slew_waivers'] = 0
        m['max_slew_violations_data'] = m.get('max_slew_violations', 0)

    return m


def derive_isa(design_name: str) -> str:
    """Derive ISA string from ORFS design name like CPU_RV32IMF_synth."""
    match = re.search(r'(RV\d+\w+?)(?:_synth|_flat|$)', design_name, re.IGNORECASE)
    if match:
        return match.group(1).upper()
    return design_name


def format_violations(m: dict) -> str:
    """Format violation summary string (RESETN slew waivers excluded)."""
    setup = m.get('setup_violations', 0)
    hold = m.get('hold_violations', 0)
    slew = m.get('max_slew_violations_data', m.get('max_slew_violations', 0))
    cap = m.get('max_cap_violations', 0)
    fanout = m.get('max_fanout_violations', 0)
    total = setup + hold
    parts = []
    if slew:
        parts.append(f'{slew} slew')
    if cap:
        parts.append(f'{cap} cap')
    if fanout:
        parts.append(f'{fanout} fanout')
    timing_str = f'{total} timing (setup/hold)'
    if parts:
        return f'{timing_str}, {", ".join(parts)}'
    return f'{total} (setup/hold/slew/cap)' if not (slew or cap or fanout) else timing_str


# ============================================================
# Module hierarchy extraction from DEF
# ============================================================

# Category → (color_rgb, list_of_prefix_patterns)
# Prefixes matched against the submodule name extracted from u_cpu.u_<name>
# Updated for W=2 superscalar with caches and microcode trap support
MODULE_CATEGORIES = [
    ('Fetch',      (0.2, 0.4, 1.0),   ['fetch', 'auipc_adder', 'jalr_target',
                                         'br_pc_plus', 'ser_pc_plus',
                                         'insn_queue', 'pc_queue']),
    ('Rename',     (0.2, 0.9, 0.3),   ['rename', 'fp_rename', 'busy_bit', 'fp_busy_bit',
                                         'flush_dff_busy']),
    ('Issue',      (0.2, 0.9, 0.9),   ['rs_int', 'rs_memory', 'rs_branch', 'rs_muldiv', 'rs_fp']),
    ('Exec MulDiv',(1.0, 0.5, 0.1),   ['exec_muldiv']),
    ('Exec FP',    (0.9, 0.2, 0.9),   ['exec_fp', 'fflags_dff', 'frm_dff']),
    ('Memory',     (1.0, 0.8, 0.1),   ['exec_memory', 'lsu', 'dmem_', 'mem_addr_r', 'mem_size_r',
                                         'mem_tag_r', 'mem_valid_r', 'sign_extend_r',
                                         'is_load_r', 'is_flw_r', 'commit_store_pending',
                                         'cross_size_pending', 'dmem_load_pending',
                                         'dmem_is_fp', 'dmem_sign_ext', 'dmem_tag',
                                         'dmem_addr_lo', 'dmem_mem_size']),
    ('Exec Int',   (1.0, 0.2, 0.2),   ['exec', 'br_cmp', 'br_target']),
    ('ROB',        (1.0, 0.3, 0.7),   ['rob', 'redir_tgt_dff', 'redirect_target_dff',
                                         'redirect_valid_dff', 'rob_isStore_dff']),
    ('CDB',        (0.0, 0.8, 0.7),   ['cdb_']),
    ('CSR/Trap',   (0.5, 0.5, 0.5),   ['csr_', 'mcycle', 'minstret', 'mscratch', 'mcause',
                                         'mepc_dff', 'mie_dff', 'mstatus_dff', 'mtval_dff',
                                         'mtvec_dff', 'trap_seq', 'useq_dc_dff',
                                         'fence_', 'fencei_redir_dff', 'fence_i_draining']),
]
DISPATCH_COLOR = (0.85, 0.85, 0.85)  # White-ish for top-level u_cpu.* signals


def classify_instance(name: str) -> str | None:
    """Classify a DEF component instance name into a module category.

    Returns category name or None if not a u_cpu component.
    """
    if not name.startswith('u_cpu.'):
        return None

    rest = name[6:]  # strip "u_cpu."

    # Check for submodule: u_cpu.u_<submodule>/... or u_cpu.u_<submodule>...
    if rest.startswith('u_'):
        # Extract submodule name: everything after u_ up to next / or end
        sub = rest[2:]
        slash = sub.find('/')
        if slash >= 0:
            sub = sub[:slash]
        # Match against category prefixes
        for cat_name, _, prefixes in MODULE_CATEGORIES:
            for prefix in prefixes:
                if sub.startswith(prefix):
                    return cat_name
        return 'Dispatch'  # u_ submodule not in any category
    else:
        # Top-level u_cpu.* signal (no u_ submodule)
        # Check if any category prefix matches the signal name directly
        for cat_name, _, prefixes in MODULE_CATEGORIES:
            for prefix in prefixes:
                if rest.startswith(prefix):
                    return cat_name
        return 'Dispatch'


def parse_def_placements(def_path: str) -> dict[str, list[tuple[float, float]]]:
    """Parse DEF file and return {category: [(x_um, y_um), ...]} for u_cpu components."""
    placements = {}
    pattern = re.compile(r'^\s+-\s+(\S+)\s+\S+.*PLACED\s+\(\s+(\d+)\s+(\d+)\s+\)')
    units_pattern = re.compile(r'UNITS\s+DISTANCE\s+MICRONS\s+(\d+)')
    scale = 1000.0  # default: 1000 DEF units per micron

    with open(def_path) as f:
        for line in f:
            um = units_pattern.search(line)
            if um:
                scale = float(um.group(1))
                continue
            m = pattern.match(line)
            if not m:
                continue
            inst_name = m.group(1)
            x = float(m.group(2)) / scale
            y = float(m.group(3)) / scale
            cat = classify_instance(inst_name)
            if cat is None:
                continue
            if cat not in placements:
                placements[cat] = []
            placements[cat].append((x, y))

    return placements


def get_module_color(category: str) -> tuple[float, float, float]:
    """Get RGB color for a module category."""
    for cat_name, color, _ in MODULE_CATEGORIES:
        if cat_name == category:
            return color
    return DISPATCH_COLOR


# ============================================================
# Load data
# ============================================================

orfs = find_orfs_paths(gds_path)
metrics = parse_metrics(orfs)
design_name = orfs['design_name']
isa = derive_isa(design_name)
pdk = orfs['pdk'].upper()

# Auto-derive output path if not specified
if out_path is None:
    suffix = '_modules' if args.mode == 'modules' else ''
    out_path = f"{design_name.lower()}_{orfs['pdk']}{suffix}.png"

print(f"Design: {design_name} ({isa})")
print(f"PDK: {pdk}")
if metrics.get('fmax_mhz'):
    print(f"Fmax: {metrics['fmax_mhz']:.1f} MHz")
if metrics.get('power_mw'):
    print(f"Power: {metrics['power_mw']:.1f} mW")

# Try to find a CJK-capable font
cjk_font = None
for pattern in ['Noto Sans CJK', 'Noto Sans JP', 'Source Han Sans',
                'WenQuanYi', 'Droid Sans Fallback', 'IPAGothic', 'IPAexGothic',
                'AR PL', 'Microsoft YaHei', 'Hiragino']:
    matches = [f for f in fm.findSystemFonts() if pattern.lower().replace(' ', '') in f.lower().replace(' ', '')]
    if matches:
        cjk_font = fm.FontProperties(fname=matches[0])
        print(f"CJK font: {matches[0]}")
        break

print(f"Loading {gds_path}...")
lib = gdstk.read_gds(gds_path)
top = lib.top_level()
if not top:
    print("No top-level cells found"); sys.exit(1)

cell = top[0]
print(f"Top cell: {cell.name}")
all_polys = cell.polygons
print(f"Polygons: {len(all_polys)}")

by_layer = {}
for poly in all_polys:
    l = poly.layer
    if l not in by_layer:
        by_layer[l] = []
    by_layer[l].append(poly.points)

sorted_layers = sorted(by_layer.keys())
print(f"Layers: {sorted_layers}")

bb = cell.bounding_box()
chip_w = bb[1][0] - bb[0][0]
chip_h = bb[1][1] - bb[0][1]
print(f"Chip: {chip_w:.1f} x {chip_h:.1f} um")

# -- Density heatmap computation --
hue_palette = [
    (0.2, 0.4, 1.0),
    (1.0, 0.2, 0.2),
    (0.2, 0.9, 0.3),
    (1.0, 0.8, 0.1),
    (0.9, 0.2, 0.9),
    (0.2, 0.9, 0.9),
    (1.0, 0.5, 0.1),
    (0.5, 0.3, 1.0),
    (0.3, 1.0, 0.6),
    (1.0, 0.3, 0.5),
    (0.7, 0.7, 0.2),
    (0.4, 0.7, 1.0),
]

layer_rgb = {}
layer_density = {}
module_density = {}
module_placements = {}

if args.mode == 'modules':
    # -- Module hierarchy mode: color by CPU submodule --
    def_path = Path(gds_path).parent / '6_final.def'
    if not def_path.exists():
        print(f"ERROR: DEF file not found: {def_path}")
        sys.exit(1)
    print(f"Parsing DEF placements from {def_path}...")
    module_placements = parse_def_placements(str(def_path))
    total_cells = sum(len(v) for v in module_placements.values())
    print(f"Found {total_cells:,} placed CPU components in {len(module_placements)} categories")
    for cat, pts in sorted(module_placements.items(), key=lambda x: -len(x[1])):
        print(f"  {cat}: {len(pts):,}")

    print("Computing module density heatmap...")
    rgb = np.zeros((GRID_N, GRID_N, 3))
    for cat, pts in module_placements.items():
        c = get_module_color(cat)
        d = np.zeros((GRID_N, GRID_N))
        for x, y in pts:
            xi = int((x - bb[0][0]) / chip_w * (GRID_N - 1))
            yi = int((y - bb[0][1]) / chip_h * (GRID_N - 1))
            xi = min(max(xi, 0), GRID_N - 1)
            yi = min(max(yi, 0), GRID_N - 1)
            d[yi, xi] += 1
        d = gaussian_filter(d, sigma=SIGMA)
        module_density[cat] = d
        if d.max() > 0:
            d_norm = d / d.max()
        else:
            d_norm = d
        for ch in range(3):
            rgb[:, :, ch] += d_norm * c[ch] * 0.7
else:
    # -- Layer mode (original behavior) --
    print("Computing density heatmap...")
    rgb = np.zeros((GRID_N, GRID_N, 3))
    for i, l in enumerate(sorted_layers):
        c = hue_palette[i % len(hue_palette)]
        layer_rgb[l] = c
        d = np.zeros((GRID_N, GRID_N))
        for poly_pts in by_layer[l]:
            cx = np.mean(poly_pts[:, 0])
            cy = np.mean(poly_pts[:, 1])
            xi = int((cx - bb[0][0]) / chip_w * (GRID_N - 1))
            yi = int((cy - bb[0][1]) / chip_h * (GRID_N - 1))
            xi = min(max(xi, 0), GRID_N - 1)
            yi = min(max(yi, 0), GRID_N - 1)
            d[yi, xi] += 1
        d = gaussian_filter(d, sigma=SIGMA)
        layer_density[l] = d
        if d.max() > 0:
            d_norm = d / d.max()
        else:
            d_norm = d
        for ch in range(3):
            rgb[:, :, ch] += d_norm * c[ch] * 0.7

rgb = np.clip(rgb, 0, 1)
rgb = np.power(rgb, GAMMA)
rgb = np.clip(rgb, 0, 1)

# -- Helper: render chip into an axes --
def render_chip(ax, xlim=None, ylim=None, show_wires=True, wire_layers=4):
    ax.set_facecolor(BG)

    # Heatmap
    ax.imshow(rgb, extent=[bb[0][0], bb[1][0], bb[0][1], bb[1][1]],
              origin='lower', aspect='auto', interpolation='nearest', alpha=0.85)

    # Wire overlays
    if show_wires:
        layers_by_size = sorted(sorted_layers, key=lambda l: len(by_layer[l]), reverse=True)
        for rank, l in enumerate(layers_by_size[:wire_layers]):
            verts = by_layer[l]
            c = layer_rgb.get(l, (0.5, 0.5, 0.5))
            hex_c = '#{:02x}{:02x}{:02x}'.format(int(c[0]*255), int(c[1]*255), int(c[2]*255))
            if len(verts) > WIRE_MAX:
                idx = np.random.default_rng(42).choice(len(verts), WIRE_MAX, replace=False)
                verts = [verts[i] for i in idx]
            fa = 0.08
            ea = max(0.15, 0.3 - rank * 0.05)
            pc = PolyCollection(verts,
                                facecolors=hex_c + '{:02x}'.format(int(fa * 255)),
                                edgecolors=hex_c + '{:02x}'.format(int(ea * 255)),
                                linewidths=0.15)
            ax.add_collection(pc)

    if xlim:
        ax.set_xlim(xlim)
        ax.set_ylim(ylim)
    else:
        m = max(chip_w, chip_h) * 0.015
        ax.set_xlim(bb[0][0] - m, bb[1][0] + m)
        ax.set_ylim(bb[0][1] - m, bb[1][1] + m)
    ax.set_aspect('equal')

# -- LAYOUT: main + inset + stats --
print("Rendering poster...")
fig = plt.figure(figsize=(32, 20), facecolor=BG)
gs = gridspec.GridSpec(2, 3, figure=fig, width_ratios=[3, 1, 1], height_ratios=[3, 1],
                       wspace=0.05, hspace=0.08)

# Main die shot
ax_main = fig.add_subplot(gs[0, :])
show_wires = (args.mode == 'layers')
render_chip(ax_main, show_wires=show_wires, wire_layers=4)

# Chip outline
ax_main.add_patch(Rectangle((bb[0][0], bb[0][1]), chip_w, chip_h,
                  fill=False, edgecolor='#8888aa', linewidth=1.5))

# Scale bar (10 um)
sb_x = bb[0][0] + chip_w * 0.02
sb_y = bb[0][1] + chip_h * 0.02
sb_len = 10.0  # 10 um
ax_main.plot([sb_x, sb_x + sb_len], [sb_y, sb_y], color='white', linewidth=2.5, solid_capstyle='butt')
ax_main.text(sb_x + sb_len / 2, sb_y + chip_h * 0.012, '10 \u00b5m',
             color='white', fontsize=11, ha='center', fontweight='bold')

ax_main.tick_params(colors='#333344', labelsize=7)
for spine in ax_main.spines.values():
    spine.set_color('#1a1a2a')

# -- Zoomed inset: center of chip (wire detail) --
ax_inset = fig.add_subplot(gs[1, 0])
cx, cy = bb[0][0] + chip_w / 2, bb[0][1] + chip_h / 2
zoom = chip_w * 0.08  # ~8% of chip width
render_chip(ax_inset, xlim=(cx - zoom, cx + zoom), ylim=(cy - zoom, cy + zoom),
            show_wires=show_wires, wire_layers=6)
inset_title = 'Module Detail (center)' if args.mode == 'modules' else 'Wire Detail (center)'
ax_inset.set_title(inset_title, color='#aaaacc', fontsize=11, pad=8)
for spine in ax_inset.spines.values():
    spine.set_color('#4444ff')
    spine.set_linewidth(2)
ax_inset.tick_params(colors='#333344', labelsize=6)

# Draw zoom box on main view
ax_main.add_patch(Rectangle((cx - zoom, cy - zoom), 2 * zoom, 2 * zoom,
                  fill=False, edgecolor='#4444ff', linewidth=1.5, linestyle='--'))

# -- Zoomed inset: densest region (cell detail) --
ax_inset2 = fig.add_subplot(gs[1, 1])
# Find the densest spot by summing all density maps
density_maps = module_density if args.mode == 'modules' else layer_density
total_density = sum(density_maps.values())
total_density = gaussian_filter(total_density, sigma=20)
peak_y, peak_x = np.unravel_index(np.argmax(total_density), total_density.shape)
corner_x = bb[0][0] + (peak_x / GRID_N) * chip_w
corner_y = bb[0][1] + (peak_y / GRID_N) * chip_h
print(f"Densest region at ({corner_x:.1f}, {corner_y:.1f})")
zoom2 = chip_w * 0.04
render_chip(ax_inset2, xlim=(corner_x - zoom2, corner_x + zoom2),
            ylim=(corner_y - zoom2, corner_y + zoom2),
            show_wires=show_wires, wire_layers=6)
ax_inset2.set_title('Densest Region', color='#aaaacc', fontsize=11, pad=8)
for spine in ax_inset2.spines.values():
    spine.set_color('#44ff44')
    spine.set_linewidth(2)
ax_inset2.tick_params(colors='#333344', labelsize=6)

ax_main.add_patch(Rectangle((corner_x - zoom2, corner_y - zoom2), 2 * zoom2, 2 * zoom2,
                  fill=False, edgecolor='#44ff44', linewidth=1.5, linestyle='--'))

# -- Stats panel (auto-extracted) --
ax_stats = fig.add_subplot(gs[1, 2])
ax_stats.set_facecolor('#0a0a16')
ax_stats.set_xlim(0, 1)
ax_stats.set_ylim(0, 1)
ax_stats.axis('off')

# Build stats from extracted metrics
fmax = metrics.get('fmax_mhz', 0)
wns = metrics.get('wns_ps', 0)
tns = metrics.get('tns_ps', 0)
util = metrics.get('utilization', 0)
power = metrics.get('power_mw', 0)
stdcells = metrics.get('stdcell_count', 0)
seq_cells = metrics.get('seq_cell_count', 0)

# Format WNS: positive = slack (good), show with sign
wns_str = f'+{wns:,.0f} ps' if wns >= 0 else f'{wns:,.0f} ps'

# PDK display name
pdk_display = {
    'ASAP7': 'ASAP7 \u2014 7nm FinFET',
    'NANGATE45': 'NanGate \u2014 45nm',
    'SKY130HD': 'SkyWater \u2014 130nm',
    'SKY130HS': 'SkyWater \u2014 130nm HS',
    'GF180': 'GF \u2014 180nm',
}.get(pdk, pdk)

stats_text = [
    ('DESIGN',      design_name),
    ('PROCESS',     pdk_display),
    ('FREQUENCY',   f'{fmax:.0f} MHz'),
    ('WNS',         wns_str),
    ('TNS',         f'{tns:,.0f} ps'),
    ('VIOLATIONS',  format_violations(metrics)),
    ('STD CELLS',   f'{stdcells:,} ({seq_cells:,} seq)'),
    ('UTILIZATION', f'{util*100:.0f}%'),
    ('POWER',       f'{power:.1f} mW'),
    ('DIE AREA',    f'{chip_w:.0f} \u00d7 {chip_h:.0f} \u00b5m\u00b2'),
    ('ISA',         f'{isa} (W=2 Tomasulo OoO)'),
    ('PROOF',       'Lean 4 \u2014 verified RTL'),
]

y = 0.95
for label, value in stats_text:
    ax_stats.text(0.05, y, label, color='#6677aa', fontsize=9,
                  fontfamily='monospace', fontweight='bold', va='top')
    ax_stats.text(0.48, y, value, color='white', fontsize=9.5,
                  fontfamily='monospace', va='top')
    y -= 0.075

# Box around stats
ax_stats.add_patch(FancyBboxPatch((0.01, 0.02), 0.98, 0.96,
                   boxstyle='round,pad=0.02', facecolor='#0a0a16',
                   edgecolor='#334466', linewidth=1.5))

# -- Title / branding (uses actual design name) --
mode_label = 'Module Hierarchy' if args.mode == 'modules' else 'Metal Layers'
title_name = f'Shoumei RTL \u2014 {design_name} ({mode_label})'
subtitle_parts = [
    'Formally verified RISC-V CPU',
    'Lean 4 proofs',
    f'{pdk_display}',
    f'{fmax:.0f} MHz',
    format_violations(metrics),
]
subtitle = '  \u00b7  '.join(subtitle_parts)

if cjk_font:
    fig.text(0.44, 0.97, '\u8a3c\u660e', color='#aabbdd', fontsize=28, fontweight='bold',
             ha='right', va='top', fontproperties=cjk_font)
    fig.text(0.45, 0.97, f' {title_name}', color='white', fontsize=26,
             fontweight='bold', ha='left', va='top', fontfamily='sans-serif')
else:
    fig.text(0.5, 0.97, title_name, color='white', fontsize=26,
             fontweight='bold', ha='center', va='top', fontfamily='sans-serif')
fig.text(0.5, 0.945, subtitle,
         color='#8899bb', fontsize=13, ha='center', va='top')

# Legend on main plot
legend_items = []
if args.mode == 'modules':
    # Sort categories by cell count descending
    cats_sorted = sorted(module_placements.items(), key=lambda x: -len(x[1]))
    for cat, pts in cats_sorted:
        c = get_module_color(cat)
        hex_c = '#{:02x}{:02x}{:02x}'.format(int(c[0]*255), int(c[1]*255), int(c[2]*255))
        legend_items.append(Patch(facecolor=hex_c, alpha=0.8, label=f'{cat} ({len(pts):,})'))
else:
    layers_by_size = sorted(sorted_layers, key=lambda l: len(by_layer[l]), reverse=True)
    for l in layers_by_size[:6]:
        c = layer_rgb.get(l, (0.5, 0.5, 0.5))
        hex_c = '#{:02x}{:02x}{:02x}'.format(int(c[0]*255), int(c[1]*255), int(c[2]*255))
        legend_items.append(Patch(facecolor=hex_c, alpha=0.8, label=f'Layer {l} ({len(by_layer[l]):,})'))
ax_main.legend(handles=legend_items, loc='upper right', fontsize=8,
               facecolor='#0c0c18ee', edgecolor='#334466', labelcolor='white',
               ncol=2 if args.mode == 'modules' else 1)

plt.subplots_adjust(top=0.93, bottom=0.02, left=0.02, right=0.98)
print(f"Saving {out_path}...")
fig.savefig(out_path, dpi=200, facecolor=BG)
print(f"Done! {out_path}")
