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
import math
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
    ("gf180", "cellsh", str(ROOT / "syn_out_gf180_hier" / "netlist")),
    ("asap7", "cellsh", str(ROOT / "syn_out_asap7_hier" / "netlist")),
]

SOURCE_TITLE = {
    "lean": "RV64G OoO CPU — Lean RTL (subsystem groups)",
    "netlist": "Lean flat netlist (per-module gate counts)",
    "gf180": "Yosys GF180MCU netlist (hierarchical, module-first)",
    "asap7": "Yosys ASAP7 netlist (hierarchical, module-first)",
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


def load_gen():
    """Import gen-architecture-diagram.py (hyphenated filename: importlib)."""
    path = Path(__file__).parent / "gen-architecture-diagram.py"
    spec = importlib.util.spec_from_file_location("gen_architecture_diagram", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


# ------------------------------------------------------------- tree builders

def module_children(gen, analyzer, mod: str) -> list[dict]:
    """One level of instance children plus the module's own direct gates.

    A module's size is direct gates + its instances; without a synthetic
    "direct logic" node every ring under the module would show a gap.
    """
    direct, insts = analyzer.get_module(mod)
    kids = []
    for sub, _inst in insts:
        sz = analyzer.hier_gates(sub)
        if sz > 0:
            kids.append({"name": sub, "size": sz})
    covered = sum(k["size"] for k in kids)
    left = analyzer.hier_gates(mod) - covered
    if left > 0:
        kids.append({"name": f"direct logic ({left:,}g)", "size": left})
    kids.sort(key=lambda c: -c["size"])
    return kids


def tree_hier(gen, top: str) -> dict:
    """Subsystem tree: same 100% hierarchical accounting as the treemap."""
    analyzer = gen.ModuleAnalyzer(LEAN_DIR)
    subs = gen.build_cpu_hierarchy(analyzer, top)
    total = analyzer.hier_gates(top)

    children = []
    for group, items in subs.items():
        leaves = [{
            "name": item["name"],
            "size": item["size"],
            "children": module_children(gen, analyzer, item["name"]),
        } for item in items]
        children.append({
            "name": group,
            "size": sum(i["size"] for i in leaves),
            "children": leaves,
        })

    return {"name": f"{top} — Lean RTL", "short": "Lean RTL", "size": total, "unit": "gates", "children": children}


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
    return {"name": "Lean flat netlist (per module)", "short": "Flat netlist", "size": total, "unit": "gates", "children": leaves}


def _seq_count(cell: str) -> bool:
    return any(mark in cell.lower() for mark in DFF_MARK)


def _cell_groups(counts: Counter) -> list[dict]:
    """{Sequential, Combinational} children with per-type leaves (shared)."""

    def leaves(seq: bool) -> list[dict]:
        picked = {t: n for t, n in counts.items() if _seq_count(t) == seq}
        rows = sorted(picked.items(), key=lambda kv: -kv[1])
        head, rest = rows[:MAX_CELL_TYPES], rows[MAX_CELL_TYPES:]
        out = [{"name": t, "size": n} for t, n in head]
        if rest:
            out.append({"name": "Other", "size": sum(n for _, n in rest)})
        return out

    seq_total = sum(n for t, n in counts.items() if _seq_count(t))
    return [
        {"name": "Sequential cells", "size": seq_total, "children": leaves(True)},
        {"name": "Combinational cells", "size": sum(counts.values()) - seq_total, "children": leaves(False)},
    ]


MODULE_RE = re.compile(r"^\s*module\s+([A-Za-z0-9_$]+)", re.MULTILINE)


def tree_cells_hier(netlist_dir: Path) -> dict:
    """Hierarchical Yosys netlist: root -> module -> {seq, comb} -> cell types.

    Uses the FLATTEN=0 synth output so the first cut is the module, exactly
    as the Lean hierarchy; only then sequential vs combinational.
    """
    path_str = str(netlist_dir)
    if "gf180" in path_str:
        tech = "GF180MCU (180 nm)"
    elif "asap7" in path_str:
        tech = "ASAP7 (7 nm)"
    else:
        tech = netlist_dir.parent.name
    text_all = "\n".join(p.read_text() for p in sorted(netlist_dir.glob("*.v")))
    known = {m.group(1) for m in MODULE_RE.finditer(text_all)}

    per_module: dict[str, Counter] = {}
    order: list[str] = []

    for text in (p.read_text() for p in sorted(netlist_dir.glob("*.v"))):
        for m in MODULE_RE.finditer(text):
            name = m.group(1)
            nxt = MODULE_RE.search(text, m.end())
            block = text[m.end():nxt.start() if nxt else len(text)]
            counts = Counter()
            for line in block.splitlines():
                im = INST_RE.match(line)
                if im and im.group(1) not in NON_CELL and im.group(1) not in known:
                    counts[im.group(1)] += 1
            if counts:
                per_module[name] = counts
                order.append(name)

    children = [{
        "name": name,
        "size": sum(per_module[name].values()),
        "children": _cell_groups(per_module[name]),
    } for name in order]
    total = sum(c["size"] for c in children)
    if total == 0:
        raise ValueError(f"no cells parsed from {netlist_dir}")
    return {"name": f"{tech} — Yosys netlist", "short": tech,
            "size": total, "unit": "cells", "children": children}


def prune_zero(node: dict) -> dict:
    """Drop zero-size children everywhere (squarify divides by min area)."""
    if "children" in node:
        node["children"] = [
            prune_zero(c) for c in node["children"] if c["size"] > 0
        ]
    return node


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
            tree = tree_cells_hier(d)
        trees[name] = prune_zero(tree)
        print(f"{name:8s} {tree['size']:>8,} {tree['unit']}  {tree['name']}")
    return trees


# -------------------------------------------------------------- shared pieces

def seed_xkcd() -> None:
    """Keep xkcd sketch/tickles stable between runs (matplotlib random state)."""
    np.random.seed(42)
    random.seed(42)


def size_units(size: int, unit: str) -> str:
    return f"{size:,} {unit}"


def style_ctx(plt, style: str, *, scale: float = 0.85, length: float = 90,
              randomness: float = 1.4):
    """xkcd sketch context, or null for the clean vector twin.

    plt.xkcd applies a stroke path-effect, which forces SVG text to glyph
    outlines (13 MB hero). The clean twin renders the same layout with
    svg.fonttype=none: small SVGs with selectable, zoomable <text>.
    """
    import contextlib

    if style == "xkcd":
        return plt.xkcd(scale=scale, length=length, randomness=randomness)
    plt.rcParams["svg.fonttype"] = "none"
    return contextlib.nullcontext()


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
    """Two-level squarified treemap; xkcd PNG plus clean vector SVG twin."""
    import matplotlib.pyplot as plt
    import matplotlib.patches as mp

    seed_xkcd()
    for style, target, dpi in (
        ("xkcd", out, 150),
        ("clean", out.with_suffix(".svg"), None),
    ):
        with style_ctx(plt, style):
            fig, ax = plt.subplots(figsize=(16, 9), dpi=100)
            fig.patch.set_facecolor("#101418")
            ax.set_facecolor("#101418")
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
                         fontsize=15, pad=12, color="#e6e9ee")
            ax.set_xlim(0, TREEMAP_W)
            ax.set_ylim(0, TREEMAP_H)
            ax.axis("off")
            ax.set_aspect("equal")

            if dpi:
                fig.savefig(target, bbox_inches="tight", pad_inches=0.1, dpi=dpi)
            else:
                fig.savefig(target, bbox_inches="tight", pad_inches=0.1)
            plt.close(fig)

# ---------------------------------------------------------------- sunburst

def draw_sunburst(gen, tree: dict, out_svg: Path, out_png: Path) -> None:
    """Baobab rings, one ring per tree level; xkcd PNG plus clean SVG twin."""
    import matplotlib.pyplot as plt
    from matplotlib.patches import Wedge

    seed_xkcd()
    max_depth = 6      # rings beyond this collapse into the deepest drawn ring
    ring_w = 0.72
    root_r = 1.0
    label_min = (14.0, 8.0, 5.0, 3.5, 2.5)  # min wedge angle (deg) to label per level

    def draw_items(ax, items, a0, r0, depth, total, group) -> None:
        """Wedges for one level; children recurse into the next ring."""
        a = a0
        for it in items:
            span = (it["size"] / total) * 2 * np.pi
            if span <= 0:
                continue
            r1 = r0 + ring_w
            ax.add_patch(Wedge((0, 0), r1, np.degrees(a), np.degrees(a + span),
                         width=ring_w, facecolor=pal_color(gen, group, depth & 1),
                         edgecolor="#101418", linewidth=0.8))
            deg = np.degrees(span)
            if depth < len(label_min) and deg > label_min[depth]:
                mid = a + span / 2
                rm = r0 + ring_w / 2
                fs = 9.0 if depth == 0 else 7.0 if depth == 1 else 6.0
                ax.text(rm * np.cos(mid), rm * np.sin(mid), it["name"],
                        ha="center", va="center", fontsize=fs, color="#1a1a1a")
            kids = it.get("children") or []
            if kids and depth + 1 < max_depth:
                draw_items(ax, kids, a, r1, depth + 1, total, group)
            a += span

    for style, target, fmt, dpi in (
        ("xkcd", out_png, "png", 150),
        ("clean", out_svg, "svg", None),
    ):
        with style_ctx(plt, style, scale=0.8, length=80, randomness=1.3):
            fig, ax = plt.subplots(figsize=(12, 12), dpi=100)
            fig.patch.set_facecolor("#101418")
            ax.set_facecolor("#101418")
            children = tree.get("children") or [tree]
            total = tree["size"]

            # Root disk + total in the center (light hub, dark text)
            center_name = tree.get("short", tree["name"].split(" — ")[-1])
            ax.add_patch(Wedge((0, 0), root_r, 0, 360, facecolor="#e9edf1", edgecolor="#101418", linewidth=2.0))
            ax.text(0, 0, f"{center_name}\n{size_units(total, tree['unit'])}",
                    ha="center", va="center", fontsize=10.5, fontweight="bold", color="#1a1a1a")

            a0 = 0.0
            for g in children:
                span = (g["size"] / total) * 2 * np.pi
                if span > 0:
                    draw_items(ax, [g], a0, root_r, 0, total, g["name"])
                    a0 += span

            max_r = root_r + ring_w * (max_depth - 0.5)
            ax.set_title(f"{tree['name']} — {size_units(total, tree['unit'])}", fontsize=14, pad=10, color="#e6e9ee")
            ax.set_xlim(-max_r * 1.07, max_r * 1.07)
            ax.set_ylim(-max_r * 1.07, max_r * 1.07)
            ax.axis("off")
            ax.set_aspect("equal")

            if dpi:
                fig.savefig(target, format=fmt, dpi=dpi, bbox_inches="tight", pad_inches=0.1)
            else:
                fig.savefig(target, format=fmt, bbox_inches="tight", pad_inches=0.1)
            plt.close(fig)


def flatten_city(tree: dict, gen) -> tuple[list[dict], list[dict]]:
    """Leaves for the 3D city: (leaf list, group legend). Each leaf carries color."""
    leaves, legend = [], []
    for g in tree.get("children") or [tree]:
        color = pal_color(gen, g["name"], 0)
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


# ---------------------------------------------------------- 3D hierarchy

def layout_tree3d(tree: dict, gen) -> dict:
    """Cone layout: depth layers, angular span proportional to share.

    Layout done here (sunburst angle math on the client would duplicate it);
    the JS scene just consumes flat arrays.
    """
    nodes: list[dict] = []
    edges: list[list[int]] = []
    total = tree["size"]
    max_log = max(1.0, math.log10(1 + total))

    def walk(node: dict, depth: int, a0: float, span: float,
             parent: int | None, group: str) -> None:
        idx = len(nodes)
        mid = a0 + span / 2
        ring_r = 2.6 + depth * 3.6
        rad = 0.4 + 2.2 * math.log10(1 + node["size"]) / max_log
        nodes.append({
            "name": node["name"],
            "size": node["size"],
            "pct": round(node["size"] / total * 100, 2),
            "x": round(math.sin(mid) * ring_r, 3),
            "y": round(-depth * 3.2, 3),
            "z": round(math.cos(mid) * ring_r, 3),
            "r": round(min(rad, 3.0), 3),
            "color": pal_color(gen, group, 0),
            "group": group,
        })
        if parent is not None:
            edges.append([parent, idx])
        kids = node.get("children") or []
        child_group = node["name"] if depth == 0 else group
        a = a0
        for k in kids:
            kspan = (k["size"] / node["size"]) * span if node["size"] else 0.0
            walk(k, depth + 1, a, kspan, idx, child_group)
            a += kspan

    walk(tree, 0, 0.0, 2 * math.pi, None, tree["name"])
    legend = [{"name": c["name"], "size": c["size"], "color": pal_color(gen, c["name"], 0)}
              for c in tree.get("children") or [tree]]
    return {"nodes": nodes, "edges": edges, "legend": legend, "total": total}


TREE_TEMPLATE = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<title>__TITLE__ — Hierarchy tree</title>
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
             border: 1px solid #444; max-width: 340px; line-height: 1.45; }
  #tooltip b { color: #fff; }
  #panel { position: absolute; right: 12px; top: 12px; z-index: 10; display: none; background: rgba(0,0,0,.85);
           border: 1px solid #2a3038; border-radius: 8px; padding: 10px 14px; font-size: 12px; max-width: 300px;
           max-height: 70vh; overflow-y: auto; line-height: 1.5; }
  #panel b { color: #fff; }
  a { color: #8ab4ff; }
</style>
</head>
<body>
<div id="info"><b>__TITLE__</b><br>__COUNT__ __UNIT__ &middot; drag to orbit, scroll to zoom, hover to trace a path, click to pin</div>
<div id="legend">__LEGEND__</div>
<div id="tooltip"></div>
<div id="panel"></div>

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
const N = DATA.nodes;

const scene = new THREE.Scene();
scene.background = new THREE.Color(0x101418);
const camera = new THREE.PerspectiveCamera(50, innerWidth / innerHeight, 0.1, 2000);
const renderer = new THREE.WebGLRenderer({ antialias: true });
renderer.setSize(innerWidth, innerHeight);
renderer.setPixelRatio(Math.min(devicePixelRatio, 2));
document.body.appendChild(renderer.domElement);

scene.add(new THREE.HemisphereLight(0xffffff, 0x404040, 1.15));
const sun = new THREE.DirectionalLight(0xffffff, 1.0);
sun.position.set(60, 120, 40);
scene.add(sun);

const spheres = [];
const tubes = [];
for (const n of N) {
  const geo = new THREE.SphereGeometry(n.r, 20, 16);
  const mat = new THREE.MeshLambertMaterial({ color: n.color, transparent: true });
  const mesh = new THREE.Mesh(geo, mat);
  mesh.position.set(n.x, n.y, n.z);
  mesh.userData = { idx: spheres.length };
  scene.add(mesh);
  spheres.push(mesh);
}
const parentOf = new Map();
for (const [p, c] of DATA.edges) {
  parentOf.set(c, p);
  const a = new THREE.Vector3(N[p].x, N[p].y, N[p].z);
  const b = new THREE.Vector3(N[c].x, N[c].y, N[c].z);
  const mid = a.clone().add(b).multiplyScalar(0.5);
  const len = a.distanceTo(b);
  const m = new THREE.Mesh(
    new THREE.CylinderGeometry(0.028, 0.028, len, 6),
    new THREE.MeshLambertMaterial({ color: 0x4a5568, transparent: true, opacity: 0.85 })
  );
  m.position.copy(mid);
  m.lookAt(b);
  m.rotateX(Math.PI / 2);
  scene.add(m);
  tubes.push(m);
}

// exposed for automated checks
window.__shoumei = { nodes: spheres.length, edges: DATA.edges.length, total: DATA.total, unit: DATA.unit };
const box = new THREE.Box3().setFromObject(spheres[0] ?? new THREE.Object3D(), true);
for (const s of spheres) box.expandByObject(s);
const center = box.getCenter(new THREE.Vector3());
const size = box.getSize(new THREE.Vector3()).length() || 20;
camera.position.set(center.x + size * 0.9, center.y + size * 0.6, center.z + size * 0.9);
const controls = new OrbitControls(camera, renderer.domElement);
controls.target.copy(center);
controls.enableDamping = true;
controls.dampingFactor = 0.08;

const raycaster = new THREE.Raycaster();
const pointer = new THREE.Vector2();
const tooltip = document.getElementById("tooltip");
const panel = document.getElementById("panel");
let active = -1;

function descendants(i) {
  const out = [i];
  for (let k = 0; k < out.length; k++) {
    for (const [p, c] of DATA.edges) if (p === out[k] && !out.includes(c)) out.push(c);
  }
  return new Set(out);
}
function ancestors(i) {
  const out = new Set([i]);
  let cur = i;
  while (parentOf.has(cur)) { cur = parentOf.get(cur); out.add(cur); }
  return out;
}
function applyFocus(i) {
  const focus = i >= 0 ? new Set([...ancestors(i), ...descendants(i)]) : null;
  for (const s of spheres) {
    const on = focus === null || focus.has(s.userData.idx);
    s.material.opacity = on ? 1 : 0.10;
  }
  for (const t of tubes) t.material.opacity = 0.9;
  for (let e = 0; e < DATA.edges.length; e++) {
    const [p, c] = DATA.edges[e];
    if (focus !== null && !(focus.has(p) && focus.has(c))) tubes[e].material.opacity = 0.06;
  }
}
function fmt(n) { return n.toLocaleString("en-US"); }

renderer.domElement.addEventListener("pointermove", (ev) => {
  pointer.x = (ev.clientX / innerWidth) * 2 - 1;
  pointer.y = -(ev.clientY / innerHeight) * 2 + 1;
  raycaster.setFromCamera(pointer, camera);
  const hit = raycaster.intersectObjects(spheres)[0];
  if (hit) {
    const i = hit.object.userData.idx;
    const d = N[i];
    active = i;
    applyFocus(i);
    tooltip.style.display = "block";
    tooltip.style.left = Math.min(ev.clientX + 14, innerWidth - 350) + "px";
    tooltip.style.top = Math.max(ev.clientY - 30, 8) + "px";
    tooltip.innerHTML = "<b>" + d.name + "</b><br>" + fmt(d.size) + " " + DATA.unit +
      " (" + d.pct + "%) <span style='color:#9aa'>&middot; " + d.group + "</span>";
  } else {
    active = -1;
    applyFocus(-1);
    tooltip.style.display = "none";
  }
});
renderer.domElement.addEventListener("click", () => {
  if (active < 0) { panel.style.display = "none"; return; }
  const d = N[active];
  const kids = [];
  for (const [p, c] of DATA.edges) if (p === active) kids.push(N[c]);
  kids.sort((a, b) => b.size - a.size);
  panel.style.display = "block";
  panel.innerHTML = "<b>" + d.name + "</b> — " + fmt(d.size) + " " + DATA.unit + " (" + d.pct + "%)<br>" +
    (kids.length ? "<span style='color:#9aa'>children:</span><br>" + kids.slice(0, 30)
      .map(k => "&nbsp;&nbsp;" + k.name + " <span style='color:#9aa'>" + fmt(k.size) + "</span>").join("<br>")
      : "<span style='color:#9aa'>leaf</span>") +
    (kids.length > 30 ? "<br>&nbsp;&nbsp;<span style='color:#9aa'>… " + (kids.length - 30) + " more</span>" : "");
  panel.style.top = "12px";
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


def draw_tree3d(gen, tree: dict, out: Path) -> None:
    """3D hierarchy HTML: cone layout, spheres sized by share, parent edges."""
    data = layout_tree3d(tree, gen)
    if not data["nodes"]:
        raise ValueError("tree needs at least one node")

    legend_html = "".join(
        f'<div><span class="swatch" style="background:{l["color"]}"></span>'
        f'{l["name"]} &mdash; {l["size"]:,} ({l["size"] / data["total"] * 100:.1f}%)</div>'
        for l in data["legend"])
    html = (TREE_TEMPLATE
            .replace("__TITLE__", tree["name"].replace("&", "&amp;").replace("<", "&lt;"))
            .replace("__COUNT__", f'{data["total"]:,}')
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
  main { padding: 20px 28px; display: grid; grid-template-columns: 1fr; gap: 22px; align-items: start; max-width: 1720px; margin: 0 auto; }
  main.grid { grid-template-columns: repeat(auto-fit, minmax(min(480px, 100%), 1fr)); max-width: none; }
  h2 { color: #fff; font-size: 17px; margin: 0; grid-column: 1 / -1; }
  .card { border: 1px solid #232a32; border-radius: 10px; background: #141a21; padding: 14px; }
  .card h3 { margin: 0 0 6px; color: #fff; font-size: 15px; }
  .card a.fig { display: block; border-radius: 6px; overflow: hidden; border: 1px solid #2a3038; }
  .card a.fig img { width: 100%; height: auto; display: block; }
  .card a.fig:hover { border-color: #4a5568; }
  .card .note { margin: 6px 2px 8px; font-size: 12.5px; color: #9aa4b0; }
  .card .meta { font-size: 13px; }
  a { color: #8ab4ff; }
  table { border-collapse: collapse; font-size: 13px; }
  td { padding: 3px 10px 3px 0; }
</style>
</head>
<body>
<header>
  <h1>Shoumei RTL &mdash; Architecture visualizations</h1>
  <p>Generated from Lean circuits and Yosys netlists by <code>scripts/gen-architecture-visuals.py</code> on every merge to <code>main</code>.
  <span style="float:right">
    <button onclick="setView('')">Wide</button>
    <button onclick="setView('grid')">Grid</button>
  </span></p>
</header>
<main id="gallery">
  __SECTIONS__
</main>
<script>
  // Wide (readable figures) by default; grid for an overview
  function setView(mode) { document.getElementById("gallery").className = mode; }
</script>
</body>
</html>
"""


def source_card(title: str, tm_svg: str, tm_png: str, sb_svg: str, sb_png: str,
                city: str, tree3d: str, note: str) -> str:
    """Card with crisp SVG figures (click for full-size PNG) and links."""
    fig_tm = (f'<a class="fig" href="{tm_png}"><img src="{tm_svg}" alt="{title} treemap"></a>'
              if tm_svg else f'<a class="fig" href="{tm_png}"><img src="{tm_png}" alt="{title} treemap"></a>')
    fig_sb = ""
    if sb_svg:
        fig_sb = f'<a class="fig" style="margin-top:8px" href="{sb_png}"><img src="{sb_svg}" alt="{title} sunburst"></a>'
    links = f'<a href="{tm_svg}">treemap SVG</a> · <a href="{tm_png}">treemap PNG</a>'
    if sb_svg:
        links += f' · <a href="{sb_svg}">sunburst SVG</a> · <a href="{sb_png}">sunburst PNG</a>'
    links += f' · <a href="{city}">3D gate city</a> · <a href="{tree3d}">3D hierarchy</a>'
    return (f'<div class="card"><h3>{title}</h3><div class="note">{note}</div>'
            f'{fig_tm}{fig_sb}<div class="meta">{links}</div></div>')


def draw_hub(trees: dict, out_dir: Path, gen) -> None:
    parts: list[str] = []

    # Hero: the detailed CPU treemap regenerated by gen-architecture-diagram.py
    hero = out_dir / "architecture-treemap.svg"
    if hero.exists():
        parts.append("<h2>Detailed CPU gate treemap (XKCD)</h2>")
        parts.append(source_card(
            "RV64G OoO CPU — subsystem + leaf labels",
            "architecture-treemap.svg", "architecture-treemap.png",
            "", "", "city-lean.html", "tree-lean.html",
            "click a figure for full size · labels readable at any zoom"))

    for name, tree in trees.items():
        title = SOURCE_TITLE.get(name, name)
        note = f'{tree["size"]:,} {tree["unit"]} total · click a figure for full size'
        parts.append(f"<h2>{title}</h2>")
        parts.append(source_card(title, f"treemap-{name}.svg", f"treemap-{name}.png",
                                 f"sunburst-{name}.svg", f"sunburst-{name}.png",
                                 f"city-{name}.html", f"tree-{name}.html", note))

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
            parts.append("<h2>Pipeline traces (Kanata)</h2>")
            parts.append(f'<div class="card">{body}</div>')

    out_dir.joinpath("index.html").write_text(
        HUB_TEMPLATE.replace("__SECTIONS__", "\n".join(parts)))


# --------------------------------------------------------------------- main

def draw_hero_svg(gen, out_svg: Path) -> None:
    """Clean vector twin of the detailed CPU treemap (house text, small file)."""
    import contextlib
    import matplotlib.pyplot as plt

    analyzer = gen.ModuleAnalyzer(LEAN_DIR)
    subsystems = gen.build_cpu_hierarchy(analyzer, TOP_DEFAULT)
    total = analyzer.hier_gates(TOP_DEFAULT)

    real_xkcd = plt.xkcd
    plt.rcParams["svg.fonttype"] = "none"
    plt.xkcd = lambda *_a, **_k: contextlib.nullcontext()
    try:
        gen.draw_treemap(subsystems, total, out_svg)
    finally:
        plt.xkcd = real_xkcd


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
        draw_tree3d(gen, t, out_dir / f"tree-{name}.html")
        print(f"rendered {name}: treemap, sunburst, city, tree")

    # Hero: reuse the detailed treemap painter, but patch plt.xkcd away so
    # the SVG keeps real <text> (the xkcd stroke effect forces glyph paths,
    # which would bloat the hub copy past 13 MB). PNG stays the xkcd one.
    hero_png = ROOT / "output" / "architecture-treemap.png"
    if hero_png.exists():
        shutil.copyfile(hero_png, out_dir / "architecture-treemap.png")
        draw_hero_svg(gen, out_dir / "architecture-treemap.svg")

    draw_hub(tree, out_dir, gen)
    print(f"hub: {out_dir / 'index.html'}")
    return 0


if __name__ == "__main__":
    sys.exit(main())