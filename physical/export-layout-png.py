#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.10"
# dependencies = ["gdstk", "matplotlib"]
# ///
"""Export GDS layout to PNG using gdstk + matplotlib."""

import sys
import gdstk
import matplotlib.pyplot as plt
from matplotlib.collections import PolyCollection

gds_path = sys.argv[1] if len(sys.argv) > 1 else \
    "third_party/orfs/flow/results/asap7/CPU_RV32IM_synth/base/6_final.gds"
out_path = sys.argv[2] if len(sys.argv) > 2 else "cpu_rv32im_asap7.png"

print(f"Loading {gds_path}...")
lib = gdstk.read_gds(gds_path)
top = lib.top_level()
if not top:
    print("No top-level cells found")
    sys.exit(1)

cell = top[0]
print(f"Top cell: {cell.name}")

# Flatten to get all polygons
print("Flattening (this may take a moment)...")
flat = cell.flatten()
all_polys = flat.polygons

print(f"Total polygons: {len(all_polys)}")

# ASAP7 layer colors (semi-transparent for overlap visibility)
layer_colors = {
    1:  '#3355ff',   # M1
    2:  '#ff3333',   # M2
    3:  '#33ff33',   # M3
    4:  '#ffff33',   # M4
    5:  '#ff33ff',   # M5
    6:  '#33ffff',   # M6
    7:  '#ff8833',   # M7
    8:  '#8833ff',   # M8
    9:  '#33ff88',   # M9
}

# Group polygons by layer
by_layer = {}
for poly in all_polys:
    layer = poly.layer
    if layer not in by_layer:
        by_layer[layer] = []
    by_layer[layer].append(poly.points)

print(f"Layers present: {sorted(by_layer.keys())}")

# Render
fig, ax = plt.subplots(figsize=(20, 20), facecolor='black')
ax.set_facecolor('black')

for layer in sorted(by_layer.keys()):
    verts = by_layer[layer]
    color = layer_colors.get(layer, '#444444')
    pc = PolyCollection(verts, facecolors=color, edgecolors='none', alpha=0.35)
    ax.add_collection(pc)

ax.autoscale_view()
ax.set_aspect('equal')
ax.set_title(
    f'CPU_RV32IM — ASAP7 7nm\n'
    f'407 MHz fmax | 74K cells | 32% util | WNS +2547ps | 0 violations',
    color='white', fontsize=16, fontweight='bold', pad=20
)
ax.tick_params(colors='#666666', labelsize=8)
for spine in ax.spines.values():
    spine.set_color('#333333')

plt.tight_layout()
print(f"Saving {out_path}...")
plt.savefig(out_path, dpi=300, bbox_inches='tight', facecolor='black')
print(f"Done! {out_path}")
