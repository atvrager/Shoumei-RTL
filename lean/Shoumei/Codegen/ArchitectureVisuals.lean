/-
Codegen/ArchitectureVisuals.lean - Native Lean architecture visualizer for Pages

Generates complete, deterministic vector SVGs (AYAYA style) and 3D HTML models
for the GitHub Pages gallery (output/architecture-visuals/):
- Treemaps (clean vector SVG in pastel AYAYA palette)
- Sunbursts (annular multi-ring Baobab layout in vector SVG)
- 3D Gate-City (Three.js WebGL visualization)
- 3D Hierarchy Tree (Three.js WebGL cone layout)
- Pages Hub (index.html linking all SVGs, SoC diagram, benchmarks, and Kanata traces)

Zero external font dependencies, zero matplotlib, 100% deterministic text SVG.
-/

import Lean.Data.Json
import Shoumei.DSL
import Shoumei.RISCV.Config
import Shoumei.Codegen.ArchitectureDiagram
import Std.Data.HashMap

namespace Shoumei.Codegen.ArchitectureVisuals

open Shoumei
open Shoumei.Codegen.ArchitectureDiagram
open Lean (Json toJson)

/-! ## Helper structures -/

structure VisNode where
  name     : String
  size     : Nat
  color    : Option String := none
  children : List VisNode  := []
  deriving Inhabited, Repr

partial def VisNode.totalSize (n : VisNode) : Nat :=
  if n.children.isEmpty then n.size
  else n.children.foldl (· + ·.totalSize) 0

/-- Convert Lean.Data.Json to VisNode tree. -/
partial def fromJson (j : Json) : Option VisNode := do
  let name ← (j.getObjValAs? String "name").toOption
  let size := (j.getObjValAs? Nat "size").toOption.getD 0
  let color := (j.getObjValAs? String "color").toOption
  let kids := match j.getObjVal? "children" with
    | .ok (Json.arr arr) => arr.toList.filterMap fromJson
    | _ => []
  some { name, size, color, children := kids }

def defaultOutDir : System.FilePath := "output/architecture-visuals"

/-! ## AYAYA Color Palette Generation -/

/-- Deterministic pastel color from string key. -/
def palColor (key : String) (shade : Nat := 0) : String :=
  let h := (key.toList.foldl (fun acc c => acc + c.toNat) 0 * 47) % 360
  -- Pastel AYAYA palette: soft hues, gentle saturation
  let sat := if shade == 0 then 55 else 45
  let lum := if shade == 0 then 88 else 93
  -- Simple HSL to RGB hex conversion
  let s := sat.toFloat / 100.0
  let l := lum.toFloat / 100.0
  let c := (1.0 - Float.abs (2.0 * l - 1.0)) * s
  let h_div_60 := h.toFloat / 60.0
  let h_mod_2 := h_div_60 - 2.0 * Float.floor (h_div_60 / 2.0)
  let x := c * (1.0 - Float.abs (h_mod_2 - 1.0))
  let m := l - c / 2.0
  let (r1, g1, b1) :=
    if h < 60 then (c, x, 0.0)
    else if h < 120 then (x, c, 0.0)
    else if h < 180 then (0.0, c, x)
    else if h < 240 then (0.0, x, c)
    else if h < 300 then (x, 0.0, c)
    else (c, 0.0, x)
  let r := (Float.round ((r1 + m) * 255.0)).toUInt64.toNat
  let g := (Float.round ((g1 + m) * 255.0)).toUInt64.toNat
  let b := (Float.round ((b1 + m) * 255.0)).toUInt64.toNat
  let hex2 (n : Nat) : String :=
    let d1 := n / 16
    let d0 := n % 16
    let toHex (d : Nat) := if d < 10 then Char.ofNat (48 + d) else Char.ofNat (87 + d)
    String.ofList [toHex d1, toHex d0]
  s!"#{hex2 r}{hex2 g}{hex2 b}"

def nodeColor (n : VisNode) (shade : Nat := 0) : String :=
  n.color.getD (palColor n.name shade)

/-! ## Sunburst SVG Generator (Baobab rings, AYAYA style) -/

def pi : Float := 3.141592653589793

structure ArcSector where
  name     : String
  size     : Nat
  color    : String
  r0       : Float
  r1       : Float
  a0       : Float
  a1       : Float
  depth    : Nat

/-- Collect concentric annular sectors up to maxDepth. -/
partial def collectArcs (n : VisNode) (rootR ringW : Float) (maxDepth : Nat) : List ArcSector :=
  let total := n.size.toFloat
  if total <= 0.0 then [] else
  let rec walk (kids : List VisNode) (depth : Nat) (a : Float) (spanTotal : Float) (r : Float) : List ArcSector := Id.run do
    if depth >= maxDepth then return []
    let kTotal := kids.foldl (· + ·.size.toFloat) 0.0
    if kTotal <= 0.0 then return []
    let mut sectors := []
    let mut curA := a
    for k in kids do
      let kSpan := (k.size.toFloat / kTotal) * spanTotal
      if kSpan > 0.001 then
        let col := nodeColor k (depth % 2)
        sectors := sectors ++ [{
          name := k.name,
          size := k.size,
          color := col,
          r0 := r,
          r1 := r + ringW,
          a0 := curA,
          a1 := curA + kSpan,
          depth := depth
        }]
        if !k.children.isEmpty then
          sectors := sectors ++ walk k.children (depth + 1) curA kSpan (r + ringW)
        curA := curA + kSpan
    return sectors
  let children := if n.children.isEmpty then [n] else n.children
  walk children 0 0.0 (2.0 * pi) rootR

/-- Format Float with 2 decimal places. -/
def fmt2 (f : Float) : String :=
  let t := (Float.round (f * 100.0)).toUInt64.toNat
  s!"{t / 100}.{if (t % 100) < 10 then "0" else ""}{t % 100}"

/-- Render an annular sector path. -/
def renderSector (cx cy : Float) (s : ArcSector) : String := Id.run do
  let x0 := cx + s.r1 * Float.cos s.a0
  let y0 := cy + s.r1 * Float.sin s.a0
  let x1 := cx + s.r1 * Float.cos s.a1
  let y1 := cy + s.r1 * Float.sin s.a1
  let x2 := cx + s.r0 * Float.cos s.a1
  let y2 := cy + s.r0 * Float.sin s.a1
  let x3 := cx + s.r0 * Float.cos s.a0
  let y3 := cy + s.r0 * Float.sin s.a0
  let largeArc := if (s.a1 - s.a0) > pi then "1" else "0"
  let pathD := s!"M {fmt1 x0} {fmt1 y0} " ++
               s!"A {fmt1 s.r1} {fmt1 s.r1} 0 {largeArc} 1 {fmt1 x1} {fmt1 y1} " ++
               s!"L {fmt1 x2} {fmt1 y2} " ++
               s!"A {fmt1 s.r0} {fmt1 s.r0} 0 {largeArc} 0 {fmt1 x3} {fmt1 y3} Z"
  let mut out := s!"  <path d=\"{pathD}\" fill=\"{s.color}\" stroke=\"#ffffff\" stroke-width=\"1.0\" opacity=\"0.95\">\n" ++
                 s!"    <title>{xmlEscape s.name}: {commas s.size}</title>\n" ++
                 s!"  </path>\n"

  -- Add label if sector is wide enough (> 6 degrees)
  let spanDeg := (s.a1 - s.a0) * 180.0 / pi
  if spanDeg > 5.5 && (s.r1 - s.r0) > 20.0 then
    let midA := (s.a0 + s.a1) / 2.0
    let midR := (s.r0 + s.r1) / 2.0
    let tx := cx + midR * Float.cos midA
    let ty := cy + midR * Float.sin midA
    let rotDeg := midA * 180.0 / pi
    let (rot, anchor) :=
      if Float.cos midA >= 0.0 then (rotDeg, "middle")
      else (rotDeg + 180.0, "middle")
    let maxChars := (spanDeg * 0.4).toUInt64.toNat + 3
    let label := if s.name.length <= maxChars then s.name else (s.name.take (maxChars - 1)).toString ++ "…"
    let fs := if s.depth == 0 then "11" else "9.5"
    out := out ++ s!"  <text x=\"{fmt1 tx}\" y=\"{fmt1 ty}\" font-size=\"{fs}\" font-weight=\"700\" " ++
                  s!"fill=\"#2c222e\" text-anchor=\"{anchor}\" dominant-baseline=\"central\" " ++
                  s!"transform=\"rotate({fmt1 rot}, {fmt1 tx}, {fmt1 ty})\">{xmlEscape label}</text>\n"
  return out

/-- Render complete Baobab Sunburst SVG in AYAYA style. -/
def renderSunburstSvg (root : VisNode) (title unit : String) : String := Id.run do
  let width := 1000.0
  let height := 1000.0
  let cx := width / 2.0
  let cy := height / 2.0 + 20.0
  let rootR := 110.0
  let ringW := 75.0
  let sectors := collectArcs root rootR ringW 5

  let mut s := s!"<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"0 0 {fmt1 width} {fmt1 height}\" width=\"{fmt1 width}\" height=\"{fmt1 height}\">\n"
  s := s ++ styleBlock

  -- Background card
  s := s ++ rect 12.0 12.0 (width - 24.0) (height - 24.0) 16.0 "#faf7f9" "#eddce4" 1.5

  -- Header
  s := s ++ text 36.0 52.0 "title" s!"{title} — Baobab Sunburst"
  s := s ++ text 36.0 76.0 "subtitle" s!"Hierarchical distribution of {commas root.size} {unit} across subsystems and units"

  -- Concentric Rings
  for sec in sectors do
    s := s ++ renderSector cx cy sec

  -- Central Disk (Hub)
  s := s ++ s!"  <circle cx=\"{fmt1 cx}\" cy=\"{fmt1 cy}\" r=\"{fmt1 rootR}\" fill=\"#ffffff\" stroke=\"#f3d9e6\" stroke-width=\"3.0\"/>\n"
  let shortTitle := if root.name.contains " — " then (root.name.splitOn " — ").getLast! else root.name
  s := s ++ s!"  <text x=\"{fmt1 cx}\" y=\"{fmt1 (cy - 12.0)}\" font-size=\"14\" font-weight=\"800\" fill=\"#3d2c3e\" text-anchor=\"middle\">{xmlEscape shortTitle}</text>\n"
  s := s ++ s!"  <text x=\"{fmt1 cx}\" y=\"{fmt1 (cy + 10.0)}\" font-size=\"18\" font-weight=\"800\" fill=\"#d9480f\" text-anchor=\"middle\">{commas root.size}</text>\n"
  s := s ++ s!"  <text x=\"{fmt1 cx}\" y=\"{fmt1 (cy + 28.0)}\" font-size=\"11\" font-weight=\"700\" fill=\"#8a6f86\" text-anchor=\"middle\">{unit}</text>\n"

  -- Footer
  s := s ++ text 36.0 (height - 26.0) "foot" "concentric depth rings · area proportional to hierarchical gate count"
  s := s ++ text (width - 36.0) (height - 26.0) "foot" "drawn by Lean ✿ same bytes on every machine ✿ ayaya~" " text-anchor=\"end\""
  return s ++ "</svg>\n"

/-! ## Treemap SVG Generator for Any Tree (AYAYA style) -/

def renderTreeSvg (root : VisNode) (title unit : String) : String := Id.run do
  let width := 1600.0
  let height := 1000.0
  let topY := 96.0
  let margin := 24.0
  let mapW := width - 2.0 * margin
  let mapH := height - topY - margin - 32.0

  let groups := if root.children.isEmpty then [root] else root.children
  let rects := squarify groups (fun g => g.size.toFloat) margin topY mapW mapH

  let mut s := s!"<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"0 0 {fmt1 width} {fmt1 height}\" width=\"{fmt1 width}\" height=\"{fmt1 height}\">\n"
  s := s ++ styleBlock
  s := s ++ rect 8.0 8.0 (width - 16.0) (height - 16.0) 16.0 "#faf7f9" "#eddce4" 1.5

  -- Header
  s := s ++ text margin 46.0 "title" s!"{title} — Treemap"
  s := s ++ text margin 70.0 "subtitle" s!"{commas root.size} {unit} total"

  -- Boxes
  for r in rects do
    let g := r.item
    let col := nodeColor g 0
    s := s ++ rect r.x r.y r.w r.h 8.0 col "#ffffff" 1.5
    let pctVal := if root.size == 0 then 0.0 else g.size.toFloat / root.size.toFloat * 100.0
    if r.w >= 60.0 && r.h >= 30.0 then
      let label := s!"{g.name} ({commas g.size}, {fmt1 pctVal}%)"
      s := s ++ text (r.x + 8.0) (r.y + 18.0) "leaf" label

    -- Inner children if any
    if !g.children.isEmpty && r.w >= 80.0 && r.h >= 60.0 then
      let inRects := squarify g.children (fun c => c.size.toFloat) (r.x + 4.0) (r.y + 26.0) (r.w - 8.0) (r.h - 30.0)
      for ir in inRects do
        let c := ir.item
        if ir.w >= 10.0 && ir.h >= 10.0 then
          let ccol := nodeColor c 1
          s := s ++ rect ir.x ir.y ir.w ir.h 4.0 ccol "#ffffff" 1.0
          if ir.w >= 45.0 && ir.h >= 20.0 then
            let clabel := if ir.w >= 80.0 then s!"{c.name} ({commas c.size})" else c.name
            s := s ++ text (ir.x + 4.0) (ir.y + 14.0) "leaf-s" clabel

  -- Footer
  s := s ++ text margin (height - 16.0) "foot" s!"squarified layout · {commas root.size} {unit}"
  s := s ++ text (width - margin) (height - 16.0) "foot" "drawn by Lean ✿ same bytes on every machine ✿ ayaya~" " text-anchor=\"end\""
  return s ++ "</svg>\n"

/-! ## Three.js 3D City & Tree HTML Templates -/

def cityTemplate : String := r##"<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>__TITLE__ — Gate City</title>
<style>
  body { margin: 0; font-family: system-ui, -apple-system, sans-serif; background: #0b0e14; color: #c8cdd3; overflow: hidden; }
  #info { position: absolute; top: 12px; left: 12px; z-index: 10; background: rgba(20,26,35,0.85);
          backdrop-filter: blur(8px); border: 1px solid #232c3b; padding: 10px 16px; border-radius: 8px; font-size: 13px; line-height: 1.5; }
  #info b { color: #fff; }
  #legend { position: absolute; bottom: 12px; left: 12px; z-index: 10; background: rgba(20,26,35,0.85);
            backdrop-filter: blur(8px); border: 1px solid #232c3b; padding: 10px 16px; border-radius: 8px; font-size: 12px; max-height: 45vh; overflow-y: auto; }
  #legend div { display: flex; align-items: center; gap: 6px; margin: 3px 0; }
  .swatch { width: 10px; height: 10px; border-radius: 2px; display: inline-block; flex: none; }
  #tooltip { position: absolute; z-index: 20; display: none; background: rgba(15,23,42,0.95);
             padding: 8px 12px; border-radius: 6px; font-size: 12px; pointer-events: none;
             border: 1px solid #38bdf8; max-width: 320px; box-shadow: 0 4px 12px rgba(0,0,0,0.5); }
  a { color: #38bdf8; text-decoration: none; }
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
scene.background = new THREE.Color(0x0b0e14);
scene.fog = new THREE.Fog(0x0b0e14, 220, 420);

const camera = new THREE.PerspectiveCamera(50, innerWidth / innerHeight, 0.1, 1000);
const renderer = new THREE.WebGLRenderer({ antialias: true });
renderer.setSize(innerWidth, innerHeight);
renderer.setPixelRatio(Math.min(devicePixelRatio, 2));
document.body.appendChild(renderer.domElement);

scene.add(new THREE.HemisphereLight(0xffffff, 0x404040, 1.2));
const sun = new THREE.DirectionalLight(0xffffff, 1.0);
sun.position.set(60, 120, 40);
scene.add(sun);

const grid = new THREE.GridHelper(160, 40, 0x232c3b, 0x141a23);
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
                        " (" + pct + "%)<br><span style='color:#38bdf8'>" + d.group + "</span>";
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
"##

def renderCityHtml (root : VisNode) (title unit : String) : String := Id.run do
  let cityW := 100.0
  let cityH := 62.0
  let cityHMax := 22.0
  let total := root.size
  -- Extract flat leaves with group assignment
  let mut leaves := []
  let mut legendList := []
  let groups := if root.children.isEmpty then [root] else root.children
  for g in groups do
    let gCol := nodeColor g 0
    legendList := legendList ++ [(g.name, g.size, gCol)]
    if g.children.isEmpty then
      leaves := leaves ++ [({ g with color := some gCol }, g.name)]
    else
      for c in g.children do
        let cCol := nodeColor c 0
        leaves := leaves ++ [({ c with color := some cCol }, g.name)]

  let rects := squarify (leaves.map (·.1)) (fun it => it.size.toFloat) 0.0 0.0 cityW cityH
  let maxS := leaves.foldl (fun m (l, _) => max m l.size) 1

  let mut jsonLeaves := []
  for (r, (_, grp)) in rects.zip leaves do
    let item := r.item
    let col := item.color.getD "#38bdf8"
    let pctVal := (item.size.toFloat / total.toFloat * 100.0)
    let obj := Json.mkObj [
      ("name", toJson item.name),
      ("x", toJson r.x),
      ("y", toJson r.y),
      ("w", toJson r.w),
      ("h", toJson r.h),
      ("size", toJson item.size),
      ("pct", toJson pctVal),
      ("group", toJson grp),
      ("color", toJson col)
    ]
    jsonLeaves := jsonLeaves ++ [obj]

  let legendHtml := String.intercalate "" (legendList.map fun (name, sz, col) =>
    let pctVal := fmt1 (sz.toFloat / total.toFloat * 100.0)
    s!"<div><span class=\"swatch\" style=\"background:{col}\"></span>{xmlEscape name} &mdash; {commas sz} ({pctVal}%)</div>")

  let dataObj := Json.mkObj [
    ("leaves", Json.arr jsonLeaves.toArray),
    ("w", toJson cityW),
    ("h", toJson cityH),
    ("maxSize", toJson maxS),
    ("unit", toJson unit),
    ("total", toJson total),
    ("hmax", toJson cityHMax)
  ]

  let safeData := (dataObj.compress).replace "</" "<\\/"
  return (cityTemplate
    |>.replace "__TITLE__" (xmlEscape title)
    |>.replace "__COUNT__" (commas total)
    |>.replace "__UNIT__" unit
    |>.replace "__LEGEND__" legendHtml
    |>.replace "__DATA__" safeData)

def treeTemplate : String := r##"<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>__TITLE__ — Hierarchy Tree</title>
<style>
  body { margin: 0; font-family: system-ui, -apple-system, sans-serif; background: #0b0e14; color: #c8cdd3; overflow: hidden; }
  #info { position: absolute; top: 12px; left: 12px; z-index: 10; background: rgba(20,26,35,0.85);
          backdrop-filter: blur(8px); border: 1px solid #232c3b; padding: 10px 16px; border-radius: 8px; font-size: 13px; line-height: 1.5; }
  #info b { color: #fff; }
  #legend { position: absolute; bottom: 12px; left: 12px; z-index: 10; background: rgba(20,26,35,0.85);
            backdrop-filter: blur(8px); border: 1px solid #232c3b; padding: 10px 16px; border-radius: 8px; font-size: 12px; max-height: 45vh; overflow-y: auto; }
  #legend div { display: flex; align-items: center; gap: 6px; margin: 3px 0; }
  .swatch { width: 10px; height: 10px; border-radius: 2px; display: inline-block; flex: none; }
  #tooltip { position: absolute; z-index: 20; display: none; background: rgba(15,23,42,0.95);
             padding: 8px 12px; border-radius: 6px; font-size: 12px; pointer-events: none;
             border: 1px solid #38bdf8; max-width: 340px; line-height: 1.45; box-shadow: 0 4px 12px rgba(0,0,0,0.5); }
  #tooltip b { color: #fff; }
  a { color: #38bdf8; text-decoration: none; }
</style>
</head>
<body>
<div id="info"><b>__TITLE__</b><br>__COUNT__ __UNIT__ &middot; drag to orbit, scroll to zoom, hover to trace hierarchy</div>
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
const scene = new THREE.Scene();
scene.background = new THREE.Color(0x0b0e14);

const camera = new THREE.PerspectiveCamera(50, innerWidth / innerHeight, 0.1, 1000);
const renderer = new THREE.WebGLRenderer({ antialias: true });
renderer.setSize(innerWidth, innerHeight);
renderer.setPixelRatio(Math.min(devicePixelRatio, 2));
document.body.appendChild(renderer.domElement);

scene.add(new THREE.HemisphereLight(0xffffff, 0x404040, 1.2));
const sun = new THREE.DirectionalLight(0xffffff, 1.0);
sun.position.set(40, 80, 50);
scene.add(sun);

const nodes = DATA.nodes;
const meshes = [];
for (const n of nodes) {
  const geo = new THREE.SphereGeometry(n.r, 24, 24);
  const mat = new THREE.MeshLambertMaterial({ color: n.color });
  const mesh = new THREE.Mesh(geo, mat);
  mesh.position.set(n.x, n.y, n.z);
  mesh.userData = n;
  scene.add(mesh);
  meshes.push(mesh);
}

const lineMat = new THREE.LineBasicMaterial({ color: 0x475569, transparent: true, opacity: 0.6 });
for (const [pIdx, cIdx] of DATA.edges) {
  const p = nodes[pIdx], c = nodes[cIdx];
  const pts = [new THREE.Vector3(p.x, p.y, p.z), new THREE.Vector3(c.x, c.y, c.z)];
  const geo = new THREE.BufferGeometry().setFromPoints(pts);
  scene.add(new THREE.Line(geo, lineMat));
}

camera.position.set(0, 30, 65);
const controls = new OrbitControls(camera, renderer.domElement);
controls.target.set(0, -10, 0);
controls.enableDamping = true;
controls.dampingFactor = 0.08;

const raycaster = new THREE.Raycaster();
const pointer = new THREE.Vector2();
const tooltip = document.getElementById("tooltip");

function fmt(n) { return n.toLocaleString("en-US"); }

renderer.domElement.addEventListener("pointermove", (ev) => {
  pointer.x = (ev.clientX / innerWidth) * 2 - 1;
  pointer.y = -(ev.clientY / innerHeight) * 2 + 1;
  raycaster.setFromCamera(pointer, camera);
  const hits = raycaster.intersectObjects(meshes);
  if (hits.length) {
    const d = hits[0].object.userData;
    tooltip.style.display = "block";
    tooltip.style.left = Math.min(ev.clientX + 14, innerWidth - 350) + "px";
    tooltip.style.top = Math.max(ev.clientY - 30, 8) + "px";
    tooltip.innerHTML = "<b>" + d.name + "</b><br>" + fmt(d.size) + " gates (" + d.pct + "%)<br><span style='color:#38bdf8'>" + d.group + "</span>";
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
"##

partial def build3d (totalF : Float) (n : VisNode) (depth : Nat) (a0 span : Float) (parentIdx : Option Nat) (grp : String)
    (nodesAcc : List Json) (edgesAcc : List Json) : List Json × List Json := Id.run do
  let idx := nodesAcc.length
  let midA := a0 + span / 2.0
  let ringR := 2.6 + depth.toFloat * 3.6
  let rad := 0.5 + 2.0 * (n.size.toFloat / totalF)
  let pctVal := fmt1 (n.size.toFloat / totalF * 100.0)
  let nodeObj := Json.mkObj [
    ("name", toJson n.name),
    ("size", toJson n.size),
    ("pct", toJson pctVal),
    ("x", toJson (Float.sin midA * ringR)),
    ("y", toJson (-depth.toFloat * 3.2)),
    ("z", toJson (Float.cos midA * ringR)),
    ("r", toJson (min rad 2.8)),
    ("color", toJson (nodeColor n (depth % 2))),
    ("group", toJson grp)
  ]
  let mut curNodes := nodesAcc ++ [nodeObj]
  let mut curEdges := match parentIdx with
    | some p => edgesAcc ++ [Json.arr #[toJson p, toJson idx]]
    | none   => edgesAcc

  let children := n.children
  let childGrp := if depth == 0 then n.name else grp
  let kTotal := children.foldl (· + ·.size.toFloat) 0.0
  let mut curA := a0
  for k in children do
    let kSpan := if kTotal > 0.0 then (k.size.toFloat / kTotal) * span else 0.0
    let (nextNodes, nextEdges) := build3d totalF k (depth + 1) curA kSpan (some idx) childGrp curNodes curEdges
    curNodes := nextNodes
    curEdges := nextEdges
    curA := curA + kSpan
  return (curNodes, curEdges)

def renderTree3dHtml (root : VisNode) (title unit : String) : String := Id.run do
  let total := root.size
  let totalF := total.toFloat
  let (nodes, edges) := build3d totalF root 0 0.0 (2.0 * pi) none root.name [] []

  let legendList := (if root.children.isEmpty then [root] else root.children).map fun c =>
    (c.name, c.size, nodeColor c 0)

  let legendHtml := String.intercalate "" (legendList.map fun (name, sz, col) =>
    let pctVal := fmt1 (sz.toFloat / totalF * 100.0)
    s!"<div><span class=\"swatch\" style=\"background:{col}\"></span>{xmlEscape name} &mdash; {commas sz} ({pctVal}%)</div>")

  let dataObj := Json.mkObj [
    ("nodes", Json.arr nodes.toArray),
    ("edges", Json.arr edges.toArray),
    ("total", toJson total)
  ]

  let safeData := (dataObj.compress).replace "</" "<\\/"
  return (treeTemplate
    |>.replace "__TITLE__" (xmlEscape title)
    |>.replace "__COUNT__" (commas total)
    |>.replace "__UNIT__" unit
    |>.replace "__LEGEND__" legendHtml
    |>.replace "__DATA__" safeData)

/-! ## Pages Hub HTML Generator -/

def hubTemplate : String := r##"<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Shoumei RTL &mdash; Architecture Visualizations</title>
<style>
  :root {
    --bg: #0b0e14;
    --card-bg: #141a23;
    --card-border: #232c3b;
    --accent: #38bdf8;
    --accent-pink: #f472b6;
    --text: #e0e6ed;
    --text-muted: #8892b0;
  }
  * { box-sizing: border-box; margin: 0; padding: 0; }
  body { font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, "Helvetica Neue", Arial, sans-serif; background: var(--bg); color: var(--text); line-height: 1.5; }
  header { padding: 24px 32px; border-bottom: 1px solid var(--card-border); background: #111620; display: flex; justify-content: space-between; align-items: center; }
  header h1 { font-size: 20px; font-weight: 700; color: #fff; display: flex; align-items: center; gap: 8px; }
  header p { font-size: 13px; color: var(--text-muted); margin-top: 4px; }
  .view-toggle { display: flex; gap: 6px; }
  .view-toggle button { background: #1e293b; border: 1px solid #334155; color: var(--text); padding: 6px 12px; border-radius: 6px; font-size: 12px; font-weight: 600; cursor: pointer; }
  .view-toggle button:hover { border-color: var(--accent); color: var(--accent); }
  main { padding: 24px 32px; max-width: 1720px; margin: 0 auto; display: grid; grid-template-columns: 1fr; gap: 24px; }
  main.grid { grid-template-columns: repeat(auto-fit, minmax(min(520px, 100%), 1fr)); }
  h2 { font-size: 16px; font-weight: 700; color: #fff; margin-bottom: 8px; grid-column: 1 / -1; display: flex; align-items: center; gap: 6px; }
  .card { border: 1px solid var(--card-border); border-radius: 10px; background: var(--card-bg); padding: 18px; box-shadow: 0 4px 16px rgba(0,0,0,0.25); }
  .card h3 { font-size: 15px; font-weight: 700; color: #fff; margin-bottom: 6px; }
  .card .note { font-size: 12.5px; color: var(--text-muted); margin-bottom: 14px; }
  .card a.fig { display: block; border-radius: 8px; overflow: hidden; border: 1px solid #2a3444; background: #080a0f; transition: border-color 0.15s ease; }
  .card a.fig:hover { border-color: var(--accent); }
  .card a.fig img { width: 100%; height: auto; display: block; }
  .card .meta { font-size: 13px; margin-top: 14px; display: flex; flex-wrap: wrap; gap: 12px; align-items: center; }
  a { color: var(--accent); text-decoration: none; }
  a:hover { text-decoration: underline; }
  .btn-launch { display: inline-block; padding: 9px 18px; background: #1e293b; border: 1px solid var(--accent); color: var(--accent); border-radius: 6px; font-weight: 600; font-size: 13px; }
  .btn-launch:hover { background: rgba(56, 189, 248, 0.1); text-decoration: none; }
  table { width: 100%; border-collapse: collapse; font-size: 13px; margin-top: 8px; }
  td { padding: 6px 12px 6px 0; border-bottom: 1px solid #1e293b; }
  .ayaya-badge { font-size: 11px; font-weight: 700; color: #f472b6; background: rgba(244, 114, 182, 0.1); border: 1px solid rgba(244, 114, 182, 0.3); padding: 2px 8px; border-radius: 12px; }
</style>
</head>
<body>
<header>
  <div>
    <h1>証明 Shoumei RTL &mdash; Architecture Visualizations <span class="ayaya-badge">AYAYA Vector SVG</span></h1>
    <p>Emitted natively by Lean 4 code generators &bull; Byte-identical on every machine &bull; Zero raster drift</p>
  </div>
  <div class="view-toggle">
    <button onclick="document.getElementById('gallery').className=''">Wide View</button>
    <button onclick="document.getElementById('gallery').className='grid'">Grid View</button>
  </div>
</header>
<main id="gallery">
__SECTIONS__
</main>
</body>
</html>
"##

def renderSourceCard (title note tmSvg sbSvg cityHtml treeHtml : String) : String :=
  let baseLinks := s!"<a href=\"{tmSvg}\">Treemap SVG</a>"
  let sbPart := if !sbSvg.isEmpty then s!" &middot; <a href=\"{sbSvg}\">Sunburst SVG</a>" else ""
  let links := s!"{baseLinks}{sbPart} &middot; <a href=\"{cityHtml}\">3D Gate City</a> &middot; <a href=\"{treeHtml}\">3D Hierarchy</a>"
  s!"<div class=\"card\">\n" ++
  s!"  <h3>{xmlEscape title}</h3>\n" ++
  s!"  <div class=\"note\">{xmlEscape note}</div>\n" ++
  s!"  <a class=\"fig\" href=\"{tmSvg}\" target=\"_blank\"><img src=\"{tmSvg}\" alt=\"{xmlEscape title} Treemap\"></a>\n" ++
  (if !sbSvg.isEmpty then s!"  <a class=\"fig\" style=\"margin-top:12px\" href=\"{sbSvg}\" target=\"_blank\"><img src=\"{sbSvg}\" alt=\"{xmlEscape title} Sunburst\"></a>\n" else "") ++
  s!"  <div class=\"meta\">{links}</div>\n" ++
  s!"</div>\n"

/-! ## Pipeline Traces Scanner -/

def renderKanataSection (outDir : System.FilePath) : IO String := do
  let kanataDir := outDir / "kanata"
  if !(← kanataDir.pathExists) then return ""
  let entries ← kanataDir.readDir
  let traces := entries.filter (·.fileName.endsWith ".txt")
  if traces.isEmpty then return ""
  let rows := String.intercalate "" (traces.toList.map fun t =>
    s!"<tr><td style=\"width:60px\"><a href=\"viewer.html?trace=kanata/{t.fileName}\">view</a></td>" ++
    s!"<td><a href=\"kanata/{t.fileName}\">{t.fileName}</a></td></tr>")
  let body := s!"<p style=\"font-size:13px;color:var(--text-muted);margin-bottom:8px;\">" ++
              "Pipeline traces from the Verilator test suite, rendered by the TypeScript viewer (<code>viewer/viewer.ts</code>). " ++
              "Open a raw <code>.txt</code> in <a href=\"https://github.com/anders-energy/konata\">Konata</a> for the classic view.</p>" ++
              s!"<table>{rows}</table>"
  return s!"<h2>Pipeline Traces (Kanata)</h2>\n<div class=\"card\">{body}</div>\n"

/-- Simple cell counter for a Verilog netlist file. -/
def parseVerilogCells (text : String) : List (String × Nat) := Id.run do
  let lines := text.splitOn "\n"
  let mut counts : Std.HashMap String Nat := {}
  for line in lines do
    let trimmed := line.trimAscii.toString
    if trimmed.startsWith "module " || trimmed.startsWith "endmodule" || trimmed.startsWith "//" || trimmed.isEmpty then
      continue
    -- Check if it looks like an instance line: `cell_type inst_name (`
    let tokens := trimmed.splitOn " " |>.filter (!·.isEmpty)
    if tokens.length >= 2 then
      let cellType := tokens.getD 0 ""
      let rest := tokens.getD 1 ""
      if !cellType.startsWith "wire" && !cellType.startsWith "input" && !cellType.startsWith "output" &&
         !cellType.startsWith "reg" && !cellType.startsWith "assign" && !cellType.startsWith "parameter" &&
         !cellType.startsWith "localparam" && !cellType.startsWith "always" && !cellType.startsWith "initial" &&
         !cellType.startsWith "defparam" then
        if rest.contains '(' || tokens.any (·.contains '(') then
          let cur := counts.getD cellType 0
          counts := counts.insert cellType (cur + 1)
  return counts.toList

/-- Read netlist files from a directory and build a VisNode tree. -/
def parseNetlistDir (netlistDir : System.FilePath) (techName : String) : IO (Option VisNode) := do
  if !(← netlistDir.pathExists) then return none
  let entries ← netlistDir.readDir
  let vFiles := entries.filter (fun e => e.fileName.endsWith ".v")
  if vFiles.isEmpty then return none
  let mut totalCells := 0
  let mut modNodes : List VisNode := []
  for f in vFiles do
    let content ← IO.FS.readFile f.path
    let cells := parseVerilogCells content
    let modCellCount : Nat := cells.foldl (fun (acc : Nat) (_, (c : Nat)) => acc + c) 0
    if modCellCount > 0 then
      totalCells := totalCells + modCellCount
      let cellKids := cells.map fun (name, c) => { name, size := c : VisNode }
      let modName := (f.fileName.take (f.fileName.length - 2)).toString
      modNodes := modNodes ++ [{ name := modName, size := modCellCount, children := cellKids }]
  if totalCells == 0 then return none
  let sortedMods := modNodes.toArray.qsort (·.size > ·.size) |>.toList
  return some { name := s!"{techName} — Yosys netlist", size := totalCells, children := sortedMods }

/-! ## Main Generator Entry Point -/

/-- Generates the complete Pages visualization suite natively in Lean. -/
def generateAllVisuals (circuits : List Circuit) (top : Circuit) (outDir : System.FilePath := defaultOutDir) : IO Unit := do
  IO.FS.createDirAll outDir

  -- 1. Hero CPU Treemap from ArchitectureDiagram
  let (groups, total) := buildGroups circuits top
  let heroSvg := renderSvg groups total circuits.length top.instances.length (uncounted circuits top)
  let heroPath := outDir / "architecture-treemap.svg"
  IO.FS.writeFile heroPath heroSvg

  -- Also update docs/architecture-treemap.svg and output/architecture-treemap.svg
  IO.FS.createDirAll "docs"
  IO.FS.writeFile "docs/architecture-treemap.svg" heroSvg

  -- 2. Build Lean RTL Tree
  let leanJson := hierarchyJson circuits top total
  let leanTree := (fromJson leanJson).getD { name := top.name, size := total }

  -- Emit Lean visualizations
  IO.FS.writeFile (outDir / "treemap-lean.svg") (renderTreeSvg leanTree "RV64G OoO CPU — Lean RTL" "gates")
  IO.FS.writeFile (outDir / "sunburst-lean.svg") (renderSunburstSvg leanTree "RV64G OoO CPU — Lean RTL" "gates")
  IO.FS.writeFile (outDir / "city-lean.html") (renderCityHtml leanTree "RV64G OoO CPU — Lean RTL" "gates")
  IO.FS.writeFile (outDir / "tree-lean.html") (renderTree3dHtml leanTree "RV64G OoO CPU — Lean RTL" "gates")

  -- 3. Build Flat Netlist Tree (from circuits)
  let flatLeaves := circuits.filter (·.gates.length > 0) |>.map fun c =>
    { name := c.name, size := c.gates.length : VisNode }
  let flatTotal := flatLeaves.foldl (· + ·.size) 0
  let flatTree : VisNode := {
    name := "Lean flat netlist (per module)",
    size := flatTotal,
    children := flatLeaves.toArray.qsort (·.size > ·.size) |>.toList
  }

  IO.FS.writeFile (outDir / "treemap-netlist.svg") (renderTreeSvg flatTree "Lean Flat Netlist" "gates")
  IO.FS.writeFile (outDir / "sunburst-netlist.svg") (renderSunburstSvg flatTree "Lean Flat Netlist" "gates")
  IO.FS.writeFile (outDir / "city-netlist.html") (renderCityHtml flatTree "Lean Flat Netlist" "gates")
  IO.FS.writeFile (outDir / "tree-netlist.html") (renderTree3dHtml flatTree "Lean Flat Netlist" "gates")

  -- 4. Check for synthesized netlists (GF180 / ASAP7) if present
  let gf180Dir : System.FilePath := "syn_out_gf180_hier/netlist"
  let gf180Node ← parseNetlistDir gf180Dir "GF180MCU (180 nm)"
  if let some gf180Tree := gf180Node then
    IO.FS.writeFile (outDir / "treemap-gf180.svg") (renderTreeSvg gf180Tree "GF180MCU Netlist" "cells")
    IO.FS.writeFile (outDir / "sunburst-gf180.svg") (renderSunburstSvg gf180Tree "GF180MCU Netlist" "cells")
    IO.FS.writeFile (outDir / "city-gf180.html") (renderCityHtml gf180Tree "GF180MCU Netlist" "cells")
    IO.FS.writeFile (outDir / "tree-gf180.html") (renderTree3dHtml gf180Tree "GF180MCU Netlist" "cells")

  let asap7Dir : System.FilePath := "syn_out_asap7_hier/netlist"
  let asap7Node ← parseNetlistDir asap7Dir "ASAP7 (7 nm)"
  if let some asap7Tree := asap7Node then
    IO.FS.writeFile (outDir / "treemap-asap7.svg") (renderTreeSvg asap7Tree "ASAP7 Netlist" "cells")
    IO.FS.writeFile (outDir / "sunburst-asap7.svg") (renderSunburstSvg asap7Tree "ASAP7 Netlist" "cells")
    IO.FS.writeFile (outDir / "city-asap7.html") (renderCityHtml asap7Tree "ASAP7 Netlist" "cells")
    IO.FS.writeFile (outDir / "tree-asap7.html") (renderTree3dHtml asap7Tree "ASAP7 Netlist" "cells")

  -- 5. Construct Hub index.html
  let mut sections := []

  -- Detailed CPU Treemap Hero
  sections := sections ++ ["<h2>Detailed CPU Gate Treemap (Lean RTL)</h2>\n" ++
    renderSourceCard "RV64G OoO CPU — Subsystems & Leaf Units"
      "Deterministic vector SVG &middot; Scalable to any resolution &middot; Byte-identical on every host"
      "architecture-treemap.svg" "" "city-lean.html" "tree-lean.html"]

  -- Interactive SoC Diagram Card
  sections := sections ++ ["<h2>Shoumei System-on-Chip (SoC) Interactive Architecture</h2>\n" ++
    "<div class=\"card\">\n" ++
    "  <h3>Shoumei SoC &mdash; Top-Level Die, Interconnect &amp; Peripherals</h3>\n" ++
    "  <div class=\"note\">Interactive SVG block diagram: RV64G OoO CPU, TileLink TL-UH crossbar, ACLINT, APLIC, UART, GPIO, BootROM &amp; SRAM</div>\n" ++
    "  <p style=\"margin: 14px 0;\"><a class=\"btn-launch\" href=\"soc-diagram.html\">Launch Interactive SoC Diagram &rarr;</a> &nbsp; <span style=\"font-size:13px;color:var(--text-muted);\">Includes pad ring pinout, TileLink bus flow &amp; block inspector</span></p>\n" ++
    "</div>\n"]

  -- Benchmarks Card
  sections := sections ++ ["<h2>Instruction Performance &amp; Benchmarks (CPI / Latency)</h2>\n" ++
    "<div class=\"card\">\n" ++
    "  <h3>RV64G + Zb* Instruction Performance &mdash; Cycle-Accurate Measurements</h3>\n" ++
    "  <div class=\"note\">Measured cycle-accurate throughput and latency across all 171 instructions on Shoumei RTL</div>\n" ++
    "  <p style=\"margin: 14px 0;\"><a class=\"btn-launch\" href=\"benchmarks.html\">View Instruction Benchmark Results &rarr;</a> &nbsp; <span style=\"font-size:13px;color:var(--text-muted);\">Interactive table with search, extension filters &amp; pipeline metrics</span></p>\n" ++
    "  <div class=\"meta\" style=\"font-size:12px;color:var(--text-muted);line-height:1.6;margin-top:10px;padding-top:10px;border-top:1px solid var(--card-border);\">\n" ++
    "    <strong style=\"color:#f59e0b;\">Architectural Caveats:</strong><br/>\n" ++
    "    &bull; <em>Microcoded Zb* bitmanip (sh1add, bset, clmul, etc.):</em> Emulated via microcode fallback (<code>FallbackSequencer</code>), serializing the pipeline (~5.9 CPI). Dedicated single-cycle execution units planned for future revisions.<br/>\n" ++
    "    &bull; <em>Atomic memory operations (AMO):</em> Serialized through the Store Buffer and memory hierarchy boundary.<br/>\n" ++
    "    &bull; <em>CSR instructions:</em> Pipeline-serialized; execute via <code>CSRFile</code> and do not increment <code>minstret</code> in hardware.\n" ++
    "  </div>\n" ++
    "</div>\n"]

  -- Lean RTL Suite Card
  sections := sections ++ ["<h2>Lean RTL Hierarchical Model</h2>\n" ++
    renderSourceCard "RV64G OoO CPU &mdash; Lean RTL (Subsystem Groups)"
      s!"{commas total} gates total &middot; Vector SVG &middot; Click figure for full size"
      "treemap-lean.svg" "sunburst-lean.svg" "city-lean.html" "tree-lean.html"]

  -- Flat Netlist Suite Card
  sections := sections ++ ["<h2>Lean Flat Netlist Model</h2>\n" ++
    renderSourceCard "Lean Flat Netlist (Per-Module Gate Counts)"
      s!"{commas flatTotal} gates across {flatLeaves.length} modules"
      "treemap-netlist.svg" "sunburst-netlist.svg" "city-netlist.html" "tree-netlist.html"]

  -- Synthesized Netlists Cards (if present)
  if let some gf180Tree := gf180Node then
    sections := sections ++ ["<h2>GF180MCU Synthesis Netlist Model</h2>\n" ++
      renderSourceCard "GF180MCU Netlist (Yosys)"
        s!"{commas gf180Tree.size} cells total &middot; Vector SVG &middot; Click figure for full size"
        "treemap-gf180.svg" "sunburst-gf180.svg" "city-gf180.html" "tree-gf180.html"]

  if let some asap7Tree := asap7Node then
    sections := sections ++ ["<h2>ASAP7 Synthesis Netlist Model</h2>\n" ++
      renderSourceCard "ASAP7 Netlist (Yosys)"
        s!"{commas asap7Tree.size} cells total &middot; Vector SVG &middot; Click figure for full size"
        "treemap-asap7.svg" "sunburst-asap7.svg" "city-asap7.html" "tree-asap7.html"]

  -- Kanata Traces
  let kanataSection ← renderKanataSection outDir
  if !kanataSection.isEmpty then
    sections := sections ++ [kanataSection]

  let hubHtml := hubTemplate.replace "__SECTIONS__" (String.intercalate "\n" sections)
  IO.FS.writeFile (outDir / "index.html") hubHtml

  IO.println s!"✓ Generated complete architecture visualization suite in {outDir}"
  IO.println "  - Hero treemap: architecture-treemap.svg"
  IO.println "  - Lean RTL: treemap-lean.svg, sunburst-lean.svg, city-lean.html, tree-lean.html"
  IO.println "  - Netlist: treemap-netlist.svg, sunburst-netlist.svg, city-netlist.html, tree-netlist.html"
  if gf180Node.isSome then
    IO.println "  - GF180MCU: treemap-gf180.svg, sunburst-gf180.svg, city-gf180.html, tree-gf180.html"
  if asap7Node.isSome then
    IO.println "  - ASAP7: treemap-asap7.svg, sunburst-asap7.svg, city-asap7.html, tree-asap7.html"
  IO.println "  - Pages Hub: index.html"

end Shoumei.Codegen.ArchitectureVisuals
