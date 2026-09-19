#!/usr/bin/env python3
"""gen-architecture-visuals.py - Sunburst, treemap and 3D gate-city views.

One flow for every netlist source: parse -> tree -> render.

  lean     output/sv-from-lean     hierarchical Lean circuits (subsystems)
  netlist  output/sv-netlist       Lean flat netlist (per-module accounting)
  gf180    syn_out_gf180/netlist   Yosys GF180MCU flattened cells
  asap7    syn_out_asap7/netlist   Yosys ASAP7 flattened cells

Per source: treemap PNG, Baobab-style sunburst SVG+PNG, three.js gate-city
HTML, plus a hub index.html. The hub also links Kanata pipeline traces
(kanata/*.txt) into the TS pipeline viewer (viewer.html).

Usage:
  scripts/gen-architecture-visuals.py [--out output/architecture-visuals] [--only lean,netlist]
"""

from __future__ import annotations

import argparse
import colorsys
import importlib.util
import json
import random
import re
import shutil
import sys
from collections import Counter
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parent.parent
DEFAULT_OUT = ROOT / "output" / "architecture-visuals"

LEAN_DIR = ROOT / "output" / "sv-from-lean"
FLAT_DIR = ROOT / "output" / "sv-netlist"
TOP_DEFAULT = "CPU_RV64IMAFD_Zicsr_Zifencei_Microcoded"

# Order matters: the hub lists sources in this order. `kind` selects the parser.
SOURCES = [
    ("lean", "hier", str(LEAN_DIR)),
    ("netlist", "flatmod", str(FLAT_DIR)),
    ("gf180", "cells", str(ROOT / "syn_out_gf180" / "netlist")),
    ("asap7", "cells", str(ROOT / "syn_out_asap7" / "netlist")),
]

SOURCE_TITLE = {
    "lean": "RV64G OoO CPU — Lean RTL (subsystem groups)",
    "netlist": "Lean flat netlist (per-module gate counts)",
    "gf180": "Yosys GF180MCU netlist (flattened, standard cells)",
    "asap7": "Yosys ASAP7 netlist (flattened, standard cells)",
}

MAX_CELL_TYPES = 30  # per-group cell-type leaves in Yosys trees

INST_RE = re.compile(r"^\s*([A-Za-z_][A-Za-z0-9_$]*)\s+\\?\S+\s*\(")
NON_CELL = {
    "module", "input", "output", "wire", "reg", "assign", "always", "if",
    "case", "end", "endmodule", "initial", "function", "task", "localparam",
    "parameter", "genvar", "generate", "supply", "defparam", "tri", "integer",
}
DFF_MARK = ("df", "dlx", "lat")  # PDK cell names containing these are sequential

TREEMAP_W, TREEMAP_H = 16.0, 9.0
CITY_W, CITY_H = 100.0, 62.0
CITY_HEIGHT_MAX = 22.0
ROOT_R, RING1_R, RING2_R = 1.0, 1.7, 2.45  # sunburst radii


def load_gen():
    """Import gen-architecture-diagram.py (hyphenated filename: importlib)."""
    path = Path(__file__).parent / "gen-architecture-diagram.py"
    spec = importlib.util.spec_from_file_location("gen_architecture_diagram", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


# ------------------------------------------------------------- tree builders

def tree_hier(gen, top: str) -> dict:
    """Subsystem tree: same 100% hierarchical accounting as the treemap."""
    analyzer = gen.ModuleAnalyzer(LEAN_DIR)
    subs = gen.build_cpu_hierarchy(analyzer, top)
    total = analyzer.hier_gates(top)

    children = []
    for group, items in subs.items():
        leaves = [{"name": item["name"], "size": item["size"]} for item in items]
        children.append({
            "name": group,
            "size": sum(i["size"] for i in leaves),
            "children": leaves,
        })

    return {"name": f"{top} — Lean RTL", "size": total, "unit": "gates", "children": children}


def tree_flatmod(gen) -> dict:
    """Per-module flat accounting: each flat module file is one leaf."""
    analyzer = gen.ModuleAnalyzer(FLAT_DIR)
    leaves = []
    for path in sorted(FLAT_DIR.glob("*.sv")):
        direct, _ = analyzer.get_module(path.stem)
        if direct > 0:
            leaves.append({"name": path.stem, "size": direct})

    leaves.sort(key=lambda c: -c["size"])
    total = sum(c["size"] for c in leaves)
    return {"name": "Lean flat netlist (per module)", "size": total, "unit": "gates", "children": leaves}


def _seq_count(cell: str) -> bool:
    return any(mark in cell.lower() for mark in DFF_MARK)


def tree_cells(netlist_dir: Path) -> dict:
    """Flattened Yosys netlist: root -> {Sequential, Combinational} -> cell types.

    A flattened netlist has no instance hierarchy, so cell type is the only
    structure left; the two groups keep the tree readable in every renderer.
    """
    counts: Counter[str] = Counter()
    for path in sorted(netlist_dir.glob("*.v")):
        for line in path.read_text().splitlines():
            m = INST_RE.match(line)
            if m and m.group(1) not in NON_CELL:
                counts[m.group(1)] += 1

    total = sum(counts.values())
    if total == 0:
        raise ValueError(f"no cells parsed from {netlist_dir}")

    def leaves(seq: bool) -> list[dict]:
        picked = {t: n for t, n in counts.items() if _seq_count(t) == seq}
        rows = sorted(picked.items(), key=lambda kv: -kv[1])
        head, rest = rows[:MAX_CELL_TYPES], rows[MAX_CELL_TYPES:]
        out = [{"name": t, "size": n} for t, n in head]
        if rest:
            out.append({"name": "Other", "size": sum(n for _, n in rest)})
        return out

    seq_total = sum(n for t, n in counts.items() if _seq_count(t))
    children = [
        {"name": "Sequential cells", "size": seq_total, "children": leaves(True)},
        {"name": "Combinational cells", "size": total - seq_total, "children": leaves(False)},
    ]
    return {"name": f"{netlist_dir.parent.name} — Yosys netlist", "size": total, "unit": "cells", "children": children}


def build_trees(gen) -> dict:
    """Build a tree per source dir that exists; warn and skip missing dirs."""
    trees = {}
    for name, kind, dir_str in SOURCES:
        d = Path(dir_str)
        if not d.exists():
            print(f"WARN: skipping {name}: {d} does not exist", file=sys.stderr)
            continue
        if kind == "hier":
            tree = tree_hier(gen, TOP_DEFAULT)
        elif kind == "flatmod":
            tree = tree_flatmod(gen)
        else:
            tree = tree_cells(d)
        trees[name] = tree
        print(f"{name:8s} {tree['size']:>8,} {tree['unit']}  {tree['name']}")
    return trees


# -------------------------------------------------------------- shared pieces

def seed_xkcd() -> None:
    """Keep xkcd sketch/tickles stable between runs (matplotlib random state)."""
    np.random.seed(42)
    random.seed(42)


def size_units(size: int, unit: str) -> str:
    return f"{size:,} {unit}"


def pal_color(gen, key: str, shade: int) -> str:
    """Stable pastel per group: PALETTE bg when known, else deterministic HSV."""
    if key in gen.PALETTE:
        return gen.PALETTE[key]["bg"]
    h = (sum(ord(c) for c in key) * 47) % 360
    sat = 0.55 if shade == 1 else 0.60
    lum = 0.82 if shade == 1 else 0.90
    r, g, b = colorsys.hls_to_rgb(h / 360, lum, sat)
    return f"#{int(r * 255):02x}{int(g * 255):02x}{int(b * 255):02x}"


def json_safe(data: dict) -> str:
    """JSON for an inline <script>: terminate early `</` to keep HTML valid."""
    return json.dumps(data).replace("</", "<\\/")


# ----------------------------------------------------------------- treemap

def draw_treemap(gen, tree: dict, out: Path) -> None:
    """Two-level squarified treemap: group rects, then leaves inside groups."""
    import matplotlib.pyplot as plt
    import matplotlib.patches as mp

    seed_xkcd()
    with plt.xkcd(scale=0.85, length=90, randomness=1.4):
        fig, ax = plt.subplots(figsize=(16, 9), dpi=100)
        groups = tree["children"] if tree.get("children") else [tree]
        rects = gen.squarify([{"name": g["name"], "size": g["size"]} for g in groups],
                             0, 0, TREEMAP_W, TREEMAP_H)

        for g, gx, gy, gw, gh in rects:
            gc = pal_color(gen, g["name"], 0)
            ax.add_patch(mp.FancyBboxPatch((gx + 0.05, gy + 0.05), gw - 0.1, gh - 0.1,
                         boxstyle="round,pad=0.01", facecolor=gc, edgecolor="#555555", linewidth=1.0))
            pct = g["size"] / tree["size"] * 100
            if gw >= 2.8:
                ax.text(gx + 0.15, gy + gh - 0.35, f"{g['name']}\n{size_units(g['size'], tree['unit'])} ({pct:.1f}%)",
                        fontsize=10.5, fontweight="bold", color="#222222", va="top")

            if g.get("children"):
                rects_in = gen.squarify(g["children"], gx + 0.15, gy + 0.5, gw - 0.3, gh - 0.65)
                for c, cx, cy, cw, ch in rects_in:
                    if cw * ch < 0.12 or cw < 0.45 or ch < 0.3:
                        continue
                    cc = pal_color(gen, g["name"], 1)
                    ax.add_patch(mp.FancyBboxPatch((cx + 0.03, cy + 0.03), cw - 0.06, ch - 0.06,
                                 boxstyle="round,pad=0.01", facecolor=cc, edgecolor="#444444", linewidth=0.6))
                    cpct = c["size"] / tree["size"] * 100
                    fs = 8.5 if cw > 2.4 else 7.0 if cw > 1.3 else 0
                    if fs:
                        ax.text(cx + cw / 2, cy + ch / 2,
                                f"{c['name']}\n{c['size']:,} ({cpct:.1f}%)",
                                ha="center", va="center", fontsize=fs,
                                fontweight="bold" if fs >= 7.6 else "normal",
                                color="#1a1a1a", multialignment="center")
            else:
                if gw >= 1.4 and gh >= 0.55:
                    ax.text(gx + gw / 2, gy + gh / 2, f"{g['name']} ({g['size']:,})",
                            ha="center", va="center", fontsize=7.5, color="#1a1a1a")

        ax.set_title(f"{tree['name']} — {size_units(tree['size'], tree['unit'])}",
                     fontsize=15, pad=12)
        ax.set_xlim(0, TREEMAP_W)
        ax.set_ylim(0, TREEMAP_H)
        ax.axis("off")
        ax.set_aspect("equal")

    fig.savefig(out, bbox_inches="tight", pad_inches=0.1)
    plt.close(fig)


# ---------------------------------------------------------------- sunburst

def draw_sunburst(gen, tree: dict, out_svg: Path, out_png: Path) -> None:
    """Baobab-style rings: root disk, one ring per level, span proportional to size."""
    import matplotlib.pyplot as plt
    from matplotlib.patches import Wedge

    seed_xkcd()
    with plt.xkcd(scale=0.8, length=80, randomness=1.3):
        fig, ax = plt.subplots(figsize=(12, 12), dpi=100)
        children = tree.get("children") or [tree]
        total = tree["size"]

        # Root disk + total in the center
        ax.add_patch(Wedge((0, 0), ROOT_R, 0, 360, facecolor="#4a4a4a", edgecolor="white", linewidth=1.5))
        ax.text(0, 0, f"{tree['name'].split(' — ')[-1]}\n{size_units(total, tree['unit'])}",
                ha="center", va="center", fontsize=10, fontweight="bold", color="white")

        a0 = 0.0
        for g in children:
            span = (g["size"] / total) * 2 * np.pi
            if g["size"] <= 0 and span <= 0:
                continue
            ax.add_patch(Wedge((0, 0), RING1_R, np.degrees(a0), np.degrees(a0 + span),
                         width=RING1_R - ROOT_R, facecolor=pal_color(gen, g["name"], 0),
                         edgecolor="white", linewidth=1.0))
            mid = a0 + span / 2
            rm = (ROOT_R + RING1_R) / 2
            if span > np.radians(14):
                ax.text(rm * np.cos(mid), rm * np.sin(mid), g["name"],
                        ha="center", va="center", fontsize=9, fontweight="bold", color="#222222")
            elif span > np.radians(5):
                ax.text(rm * np.cos(mid) * 0.92, rm * np.sin(mid) * 0.92, g["name"],
                        ha="center", va="center", fontsize=6.5, color="#222222")

            # Second ring: grandchildren occupy the parent's angular span
            leaves = g.get("children") or []
            if leaves:
                b0 = a0
                for c in leaves:
                    lspan = (c["size"] / g["size"]) * span if g["size"] else 0.0
                    ax.add_patch(Wedge((0, 0), RING2_R, np.degrees(b0), np.degrees(b0 + lspan),
                                 width=RING2_R - RING1_R, facecolor=pal_color(gen, g["name"], 1),
                                 edgecolor="white", linewidth=0.8))
                    if lspan > np.radians(8):
                        lmid = b0 + lspan / 2
                        lr = (RING1_R + RING2_R) / 2
                        ax.text(lr * np.cos(lmid), lr * np.sin(lmid), c["name"],
                                ha="center", va="center", fontsize=6, color="#222222", rotation=0)
                    b0 += lspan
            a0 += span

        ax.set_title(f"{tree['name']} — {size_units(total, tree['unit'])}", fontsize=14, pad=10)
        ax.set_xlim(-RING2_R * 1.06, RING2_R * 1.06)
        ax.set_ylim(-RING2_R * 1.06, RING2_R * 1.06)
        ax.axis("off")
        ax.set_aspect("equal")

    fig.savefig(out_svg, format="svg", bbox_inches="tight", pad_inches=0.1)
    fig.savefig(out_png, format="png", dpi=110, bbox_inches="tight", pad_inches=0.1)
    plt.close(fig)


def flatten_city(tree: dict, gen) -> tuple[list[dict], list[dict]]:
    """Leaves for the 3D city: (leaf list, group legend). Each leaf carries color."""
    leaves, legend = [], []
    for g in tree.get("children") or [tree]:
        color = pal_color(gen, g["name"], 0).replace("hsl(", "hsl(")  # keep as-is
        legend.append({"name": g["name"], "size": g["size"], "color": color})
        if g.get("children"):
            for c in g["children"]:
                leaves.append({"name": c["name"], "size": c["size"], "group": g["name"], "color": color})
        else:
            leaves.append({"name": g["name"], "size": g["size"], "group": g["name"], "color": color})
    return leaves, legend


# ------------------------------------------------------------------ 3D city

CITY_TEMPLATE = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<title>__TITLE__ — Gate city</title>
<style>
  body { margin: 0; font-family: system-ui, sans-serif; background: #101418; color: #c8cdd3; overflow: hidden; }
  #info { position: absolute; top: 12px; left: 12px; z-index: 10; background: rgba(0,0,0,.55);
          padding: 8px 14px; border-radius: 8px; font-size: 13px; line-height: 1.5; }
  #info b { color: #fff; }
  #legend { position: absolute; bottom: 12px; left: 12px; z-index: 10; background: rgba(0,0,0,.55);
            padding: 8px 14px; border-radius: 8px; font-size: 12px; max-height: 45vh; overflow-y: auto; }
  #legend div { display: flex; align-items: center; gap: 6px; margin: 2px 0; }
  .swatch { width: 10px; height: 10px; border-radius: 2px; display: inline-block; flex: none; }
  #tooltip { position: absolute; z-index: 20; display: none; background: rgba(0,0,0,.85);
             padding: 6px 10px; border-radius: 6px; font-size: 12px; pointer-events: none;
             border: 1px solid #444; max-width: 320px; }
  a { color: #8ab4ff; }
</style>
</head>
<body>
<div id="info"><b>__TITLE__</b><br>__COUNT__ __UNIT__ &middot; drag to orbit, scroll to zoom, hover for details</div>
<div id="legend">__LEGEND__</div>
<div id="tooltip"></div>

<script type="importmap">
{ "imports": {
    "three": "https://cdn.jsdelivr.net/npm/three@0.170.0/build/three.module.js",
    "three/addons/": "https://cdn.jsdelivr.net/npm/three@0.170.0/examples/jsm/"
} }
</script>
<script type="module">
import * as THREE from "three";
import { OrbitControls } from "three/addons/controls/OrbitControls.js";

const DATA = __DATA__;
const W = DATA.w, H = DATA.h, MAXS = DATA.maxSize;

const scene = new THREE.Scene();
scene.background = new THREE.Color(0x101418);
scene.fog = new THREE.Fog(0x101418, 220, 420);

const camera = new THREE.PerspectiveCamera(50, innerWidth / innerHeight, 0.1, 1000);
const renderer = new THREE.WebGLRenderer({ antialias: true });
renderer.setSize(innerWidth, innerHeight);
renderer.setPixelRatio(Math.min(devicePixelRatio, 2));
document.body.appendChild(renderer.domElement);

scene.add(new THREE.HemisphereLight(0xffffff, 0x404040, 1.1));
const sun = new THREE.DirectionalLight(0xffffff, 1.0);
sun.position.set(60, 120, 40);
scene.add(sun);

const grid = new THREE.GridHelper(160, 40, 0x2a3038, 0x1e232a);
grid.position.y = -0.01;
scene.add(grid);

const boxes = [];
for (const b of DATA.leaves) {
  const bw = b.w, bd = b.h, bh = 0.6 + (Math.sqrt(b.size) / Math.sqrt(MAXS)) * (DATA.hmax - 0.6);
  const geo = new THREE.BoxGeometry(bw, bh, bd);
  const mat = new THREE.MeshLambertMaterial({ color: b.color });
  const mesh = new THREE.Mesh(geo, mat);
  mesh.position.set(b.x + bw / 2, bh / 2, -(b.y + bd / 2));
  mesh.userData = b;
  scene.add(mesh);
  const edge = new THREE.LineSegments(new THREE.EdgesGeometry(geo),
                  new THREE.LineBasicMaterial({ color: 0x000000, transparent: true, opacity: 0.25 }));
  edge.position.copy(mesh.position);
  scene.add(edge);
  boxes.push(mesh);
}

const cx = W / 2, cz = -(H / 2);
camera.position.set(cx + 95, 85, cz + 95);
const controls = new OrbitControls(camera, renderer.domElement);
controls.target.set(cx, 4, cz);
controls.enableDamping = true;
controls.dampingFactor = 0.08;
controls.maxPolarAngle = Math.PI / 2.1;

const raycaster = new THREE.Raycaster();
const pointer = new THREE.Vector2();
const tooltip = document.getElementById("tooltip");

function fmt(n) { return n.toLocaleString("en-US"); }

renderer.domElement.addEventListener("pointermove", (ev) => {
  pointer.x = (ev.clientX / innerWidth) * 2 - 1;
  pointer.y = -(ev.clientY / innerHeight) * 2 + 1;
  raycaster.setFromCamera(pointer, camera);
  const hits = raycaster.intersectObjects(boxes);
  if (hits.length) {
    const d = hits[0].object.userData;
    const pct = (d.size / DATA.total * 100).toFixed(2);
    tooltip.style.display = "block";
    tooltip.style.left = Math.min(ev.clientX + 14, innerWidth - 330) + "px";
    tooltip.style.top = Math.max(ev.clientY - 30, 8) + "px";
    tooltip.innerHTML = "<b>" + d.name + "</b><br>" + fmt(d.size) + " " + DATA.unit +
                        " (" + pct + "%)<br><span style='color:#9aa'>" + d.group + "</span>";
  } else {
    tooltip.style.display = "none";
  }
});

addEventListener("resize", () => {
  camera.aspect = innerWidth / innerHeight;
  camera.updateProjectionMatrix();
  renderer.setSize(innerWidth, innerHeight);
});

(function animate() {
  requestAnimationFrame(animate);
  controls.update();
  renderer.render(scene, camera);
})();
</script>
</body>
</html>
"""


def draw_city(gen, tree: dict, out: Path) -> None:
    """Gate-city HTML: squarified footprint, box height ~ sqrt(gate count)."""
    leaves, legend = flatten_city(tree, gen)
    if not leaves:
        raise ValueError("city needs at least one leaf")

    total = tree["size"]
    rects = gen.squarify(leaves, 0, 0, CITY_W, CITY_H)
    max_size = max(c["size"] for c in leaves)

    city_leaves = []
    for c, cx, cy, cw, ch in rects:
        pct = c["size"] / total * 100
        city_leaves.append({"name": c["name"], "x": round(cx, 3), "y": round(cy, 3),
                            "w": round(cw, 3), "h": round(ch, 3), "size": c["size"],
                            "pct": round(pct, 2), "group": c["group"], "color": c["color"]})

    legend_html = "".join(
        f'<div><span class="swatch" style="background:{l["color"]}"></span>'
        f'{l["name"]} &mdash; {l["size"]:,} ({l["size"] / total * 100:.1f}%)</div>'
        for l in legend)

    data = {"leaves": city_leaves, "w": CITY_W, "h": CITY_H, "maxSize": max_size,
            "unit": tree["unit"], "total": total, "hmax": CITY_HEIGHT_MAX}
    html = (CITY_TEMPLATE
            .replace("__TITLE__", tree["name"].replace("&", "&amp;").replace("<", "&lt;"))
            .replace("__COUNT__", f"{total:,}")
            .replace("__UNIT__", tree["unit"])
            .replace("__LEGEND__", legend_html)
            .replace("__DATA__", json_safe(data)))
    out.write_text(html)


# ---------------------------------------------------------------------- hub

HUB_TEMPLATE = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Shoumei RTL — Architecture visualizations</title>
<style>
  body { font-family: system-ui, sans-serif; margin: 0; background: #0f1318; color: #c8cdd3; }
  header { padding: 20px 28px; border-bottom: 1px solid #232a32; }
  header h1 { margin: 0 0 4px; color: #fff; }
  header p { margin: 0; font-size: 14px; }
  main { padding: 20px 28px; }
  section { margin-bottom: 26px; }
  h2 { color: #fff; font-size: 17px; margin: 0 0 8px; }
  .gallery { display: flex; gap: 18px; flex-wrap: wrap; align-items: flex-start; }
  .card { border: 1px solid #232a32; border-radius: 10px; background: #141a21; padding: 12px; max-width: 640px; }
  .card img { width: 100%; border-radius: 6px; display: block; }
  .card .meta { margin: 8px 2px 0; font-size: 13px; }
  a { color: #8ab4ff; }
  table { border-collapse: collapse; font-size: 13px; }
  td { padding: 3px 10px 3px 0; }
</style>
</head>
<body>
<header>
  <h1>Shoumei RTL &mdash; Architecture visualizations</h1>
  <p>Generated from Lean circuits and Yosys netlists by <code>scripts/gen-architecture-visuals.py</code> on every merge to <code>main</code>.</p>
</header>
<main>
  __SECTIONS__
</main>
</body>
</html>
"""


def hub_section(title: str, body: str) -> str:
    return f"<section><h2>{title}</h2>{body}</section>"


def leaf_links(name: str, png: str, svg: str, city: str) -> str:
    return (f'<div class="card"><img src="{png}" alt="{name}">'
            f'<div class="meta"><a href="{png}">PNG</a> · '
            f'<a href="{svg}">SVG (sunburst)</a> · '
            f'<a href="{city}">3D gate city</a></div></div>')


def draw_hub(trees: dict, out_dir: Path, gen) -> None:
    sections = []

    # Hero: the detailed CPU treemap regenerated by gen-architecture-diagram.py
    hero = out_dir / "architecture-treemap.png"
    if hero.exists():
        body = leaf_links("Detailed CPU gate treemap (subsystem + leaf labels)",
                          "architecture-treemap.png", "architecture-treemap.svg",
                          "city-lean.html")
        sections.append(hub_section("Detailed CPU gate treemap (XKCD)", body))

    for name, tree in trees.items():
        title = SOURCE_TITLE.get(name, name)
        body = leaf_links(title, f"treemap-{name}.png", f"sunburst-{name}.svg",
                          f"city-{name}.html")
        body += (f'<p style="font-size:13px;margin:6px 2px">{tree["size"]:,} '
                 f'{tree["unit"]} total</p>')
        sections.append(hub_section(title, body))

    # Kanata pipeline traces published by the Test group
    kanata_dir = out_dir / "kanata"
    if kanata_dir.exists():
        traces = sorted(kanata_dir.glob("*.txt"))
        if traces:
            rows = "".join(
                f'<tr><td><a href="viewer.html?trace=kanata/{t.name}">view</a></td>'
                f'<td><a href="kanata/{t.name}">{t.name}</a></td></tr>'
                for t in traces)
            body = ("<p style='font-size:13px'>Pipeline traces from the Verilator "
                    "test suite, rendered by the TypeScript viewer "
                    "(<code>viewer/viewer.ts</code>). "
                    "Open a raw <code>.txt</code> in <a href='https://github.com/anders-energy/konata'>Konata</a> for the classic view.</p>"
                    f"<table>{rows}</table>")
            sections.append(hub_section("Pipeline traces (Kanata)", body))

    out_dir.joinpath("index.html").write_text(
        HUB_TEMPLATE.replace("__SECTIONS__", "\n".join(sections)))


# --------------------------------------------------------------------- main

def parse_args(argv: list[str]) -> argparse.Namespace:
    p = argparse.ArgumentParser(description="Generate architecture visualizations for Pages.")
    p.add_argument("--out", type=Path, default=DEFAULT_OUT,
                   help=f"output directory (default: {DEFAULT_OUT})")
    p.add_argument("--only", type=str, default="",
                   help="comma-separated subset of sources: lean,netlist,gf180,asap7")
    return p.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv if argv is not None else sys.argv[1:])

    gen = load_gen()
    if not gen.ensure_xkcd_font():
        print("WARN: xkcd font unavailable; falling back to default font", file=sys.stderr)

    tree = build_trees(gen)
    if not tree:
        print("Error: no sources available (run 'make codegen' and the Yosys synths).",
              file=sys.stderr)
        return 1

    only = {s.strip() for s in args.only.split(",") if s.strip()}
    out_dir = args.out
    out_dir.mkdir(parents=True, exist_ok=True)

    for name in tree:
        if only and name not in only:
            continue
        t = tree[name]
        draw_treemap(gen, t, out_dir / f"treemap-{name}.png")
        draw_sunburst(gen, t, out_dir / f"sunburst-{name}.svg", out_dir / f"sunburst-{name}.png")
        draw_city(gen, t, out_dir / f"city-{name}.html")
        print(f"rendered {name}: treemap, sunburst, city")

    # Hero images come from the existing treemap generator when present
    for f in ("architecture-treemap.png", "architecture-treemap.svg"):
        src = ROOT / "output" / f
        if src.exists():
            shutil.copyfile(src, out_dir / f)

    draw_hub(tree, out_dir, gen)
    print(f"hub: {out_dir / 'index.html'}")
    return 0


if __name__ == "__main__":
    sys.exit(main())