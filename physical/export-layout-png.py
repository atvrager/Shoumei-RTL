#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.10"
# dependencies = ["gdstk", "matplotlib", "numpy", "scipy"]
# ///
"""Export GDS layout as a presentation-quality die shot poster.

Features:
  - Per-layer colored density heatmap (high-res)
  - Wire polygon overlay for routing texture
  - Zoomed inset showing wire-level detail
  - Stats panel with key PPA metrics
  - Scale bar and project branding

Usage: ./physical/export-layout-png.py [input.gds] [output.png]
"""

import sys
import gdstk
import numpy as np
import matplotlib.pyplot as plt
import matplotlib.gridspec as gridspec
from matplotlib.collections import PolyCollection
from matplotlib.patches import Rectangle, FancyBboxPatch, FancyArrowPatch, Patch
from scipy.ndimage import gaussian_filter

gds_path = sys.argv[1] if len(sys.argv) > 1 else \
    "third_party/orfs/flow/results/asap7/CPU_RV32IMF_synth/base/6_final.gds"
out_path = sys.argv[2] if len(sys.argv) > 2 else "cpu_rv32imf_asap7.png"

# -- Config --
BG = '#04040a'
GRID_N = 2000
SIGMA = 2
WIRE_MAX = 500000
GAMMA = 0.55

# Try to find a CJK-capable font
import matplotlib.font_manager as fm
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

# -- Per-layer density heatmap --
print("Computing density heatmap...")
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
render_chip(ax_main, show_wires=True, wire_layers=4)

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
            show_wires=True, wire_layers=6)
ax_inset.set_title('Wire Detail (center)', color='#aaaacc', fontsize=11, pad=8)
for spine in ax_inset.spines.values():
    spine.set_color('#4444ff')
    spine.set_linewidth(2)
ax_inset.tick_params(colors='#333344', labelsize=6)

# Draw zoom box on main view
ax_main.add_patch(Rectangle((cx - zoom, cy - zoom), 2 * zoom, 2 * zoom,
                  fill=False, edgecolor='#4444ff', linewidth=1.5, linestyle='--'))

# -- Zoomed inset: densest region (cell detail) --
ax_inset2 = fig.add_subplot(gs[1, 1])
# Find the densest spot by summing all layer densities
total_density = sum(layer_density.values())
total_density = gaussian_filter(total_density, sigma=20)
peak_y, peak_x = np.unravel_index(np.argmax(total_density), total_density.shape)
corner_x = bb[0][0] + (peak_x / GRID_N) * chip_w
corner_y = bb[0][1] + (peak_y / GRID_N) * chip_h
print(f"Densest region at ({corner_x:.1f}, {corner_y:.1f})")
zoom2 = chip_w * 0.04
render_chip(ax_inset2, xlim=(corner_x - zoom2, corner_x + zoom2),
            ylim=(corner_y - zoom2, corner_y + zoom2),
            show_wires=True, wire_layers=6)
ax_inset2.set_title('Densest Region', color='#aaaacc', fontsize=11, pad=8)
for spine in ax_inset2.spines.values():
    spine.set_color('#44ff44')
    spine.set_linewidth(2)
ax_inset2.tick_params(colors='#333344', labelsize=6)

ax_main.add_patch(Rectangle((corner_x - zoom2, corner_y - zoom2), 2 * zoom2, 2 * zoom2,
                  fill=False, edgecolor='#44ff44', linewidth=1.5, linestyle='--'))

# -- Stats panel --
ax_stats = fig.add_subplot(gs[1, 2])
ax_stats.set_facecolor('#0a0a16')
ax_stats.set_xlim(0, 1)
ax_stats.set_ylim(0, 1)
ax_stats.axis('off')

stats_text = [
    ('DESIGN',      'CPU_RV32IM'),
    ('PROCESS',     'ASAP7 — 7nm FinFET'),
    ('FREQUENCY',   '407 MHz (target 200)'),
    ('WNS',         '+2,547 ps'),
    ('TNS',         '0 ps'),
    ('VIOLATIONS',  '0 (setup/hold/slew/cap)'),
    ('STD CELLS',   '74,206'),
    ('UTILIZATION',  '32%'),
    ('POWER',       '12.0 mW'),
    ('DIE AREA',    f'{chip_w:.0f} \u00d7 {chip_h:.0f} \u00b5m\u00b2'),
    ('ISA',         'RV32IM (Tomasulo OoO)'),
    ('PROOF',       'Lean 4 — verified RTL'),
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

# -- Title / branding --
if cjk_font:
    fig.text(0.44, 0.97, '証明', color='#aabbdd', fontsize=28, fontweight='bold',
             ha='right', va='top', fontproperties=cjk_font)
    fig.text(0.45, 0.97, ' Shoumei RTL — CPU_RV32IM', color='white', fontsize=26,
             fontweight='bold', ha='left', va='top', fontfamily='sans-serif')
else:
    fig.text(0.5, 0.97, 'Shoumei RTL — CPU_RV32IM', color='white', fontsize=26,
             fontweight='bold', ha='center', va='top', fontfamily='sans-serif')
fig.text(0.5, 0.945,
         'Formally verified RISC-V CPU  ·  Lean 4 proofs  ·  ASAP7 7nm  ·  407 MHz  ·  0 violations',
         color='#8899bb', fontsize=13, ha='center', va='top')

# Layer legend on main plot
legend_items = []
layers_by_size = sorted(sorted_layers, key=lambda l: len(by_layer[l]), reverse=True)
for l in layers_by_size[:6]:
    c = layer_rgb.get(l, (0.5, 0.5, 0.5))
    hex_c = '#{:02x}{:02x}{:02x}'.format(int(c[0]*255), int(c[1]*255), int(c[2]*255))
    legend_items.append(Patch(facecolor=hex_c, alpha=0.8, label=f'Layer {l} ({len(by_layer[l]):,})'))
ax_main.legend(handles=legend_items, loc='upper right', fontsize=8,
               facecolor='#0c0c18ee', edgecolor='#334466', labelcolor='white')

plt.subplots_adjust(top=0.93, bottom=0.02, left=0.02, right=0.98)
print(f"Saving {out_path}...")
fig.savefig(out_path, dpi=200, facecolor=BG)
print(f"Done! {out_path}")
