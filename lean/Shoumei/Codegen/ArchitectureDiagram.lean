/-
ArchitectureDiagram.lean - CPU gate treemap, rendered from the Circuit registry

Every box is a registry module; its area is the module's hierarchical gate
count (its own DSL gates plus everything it instantiates).  The picture is a
function of the same `Circuit` values the proofs talk about, so it cannot
drift from them, and plain SVG text is byte-identical on every host.

```
  CPU instances ──classify──▶ subsystem ──expand big containers──▶ items
                                 │                                  │
                                 ▼                                  ▼
                        squarify(subsystems)  ─────────▶   squarify(items) ─▶ SVG
```
-/

import Lean.Data.Json
import Shoumei.DSL

namespace Shoumei.Codegen.ArchitectureDiagram

open Shoumei
open Lean (Json toJson)

/-! ## Gate accounting -/

/-- Hierarchical gate count of every registry module.

    `circuits` is in topological order (leaves first), so one left fold sees
    each child before its parents.  The first occurrence of a name wins, as in
    codegen.  Modules outside the registry (the behavioural riscv-opcodes
    decoders) are absent and count as 0. -/
def hierSizes (circuits : List Circuit) : Std.HashMap String Nat :=
  circuits.foldl (init := {}) fun m c =>
    if m.contains c.name then m else
    let kids := c.instances.foldl (fun a i => a + m.getD i.moduleName 0) 0
    m.insert c.name (c.gates.length + kids)

/-! ## Subsystems -/

inductive Subsystem where
  | execute | rename | issue | retire | microcode | memory | fetch | decode | glue
  deriving BEq, Hashable, Repr, Inhabited

/-- Presentation of one subsystem (pastel panel, saturated accent). -/
structure Style where
  title  : String
  emoji  : String
  panel  : String  -- panel fill
  accent : String  -- panel border, header text
  ink    : String  -- leaf border, stats text

def Subsystem.style : Subsystem → Style
  | .execute   => ⟨"Execution",     "⚡", "#fff4e0", "#f08c00", "#d9480f"⟩
  | .rename    => ⟨"Renaming",      "🌸", "#ffeef3", "#f06595", "#c2255c"⟩
  | .issue     => ⟨"Issue queues",  "💎", "#e7f5ff", "#4dabf7", "#1971c2"⟩
  | .retire    => ⟨"Retire & CSRs", "🎀", "#f8f0fc", "#cc5de8", "#862e9c"⟩
  | .microcode => ⟨"Microcode",     "🔮", "#f3f0ff", "#845ef7", "#5f3dc4"⟩
  | .memory    => ⟨"Memory",        "🌊", "#e6fcf5", "#20c997", "#087f5b"⟩
  | .fetch     => ⟨"Fetch",         "⭐", "#fff9db", "#fcc419", "#e67700"⟩
  | .decode    => ⟨"Decode",        "🍃", "#ebfbee", "#51cf66", "#2b8a3e"⟩
  | .glue      => ⟨"Glue & CDB",    "💫", "#f1f3f5", "#adb5bd", "#495057"⟩

/-- How a top-level instance name is matched. -/
inductive NameMatch where
  | pre (s : String)  -- name starts with `s`
  | has (s : String)  -- name contains `s`

def NameMatch.test : NameMatch → String → Bool
  | .pre p, s => s.startsWith p
  | .has p, s => (s.splitOn p).length > 1

/-- Top-level CPU instance name → subsystem.  First match wins; anything
    unmatched (pipeline registers, CDB FIFOs, flush DFFs) is glue. -/
def classifier : List (NameMatch × Subsystem) := [
  (.pre "u_fallback_seq", .microcode), (.pre "u_trap_seq", .microcode),
  (.has "_lut", .decode),              (.pre "u_decoder", .decode),
  (.pre "u_exec_memory", .memory),     (.pre "u_lsu", .memory),
  (.pre "u_exec", .execute),           (.pre "u_br_", .execute),
  (.pre "u_jalr_", .execute),          (.pre "u_auipc_", .execute),
  (.pre "u_atom_", .execute),
  (.pre "u_rename", .rename),          (.pre "u_fp_rename", .rename),
  (.pre "u_busy_table", .rename),      (.pre "u_fp_busy_table", .rename),
  (.pre "u_rs_", .issue),
  (.pre "u_rob", .retire),             (.pre "u_csr", .retire),
  (.pre "u_fetch", .fetch),            (.pre "u_pc_queue", .fetch),
  (.pre "u_insn_queue", .fetch)
]

def classify (inst : String) : Subsystem :=
  (classifier.find? (·.1.test inst)).map (·.2) |>.getD .glue

/-! ## Labels

Readable names for boxes.  The longest matching prefix wins, so the tables are
order-independent (`FPFMAD` beats `FPFMA`).  Instance names are tried first
because one module can play several roles (`Queue16x32_DualPort` is both the
PC and the instruction queue). -/

def instLabels : List (String × String) := [
  ("u_pc_queue", "PC queue"),            ("u_insn_queue", "Insn queue"),
  ("u_fetch", "Fetch stage"),
  ("u_rs_int", "RS int"),                ("u_rs_branch", "RS branch"),
  ("u_rs_memory", "RS mem"),             ("u_rs_muldiv", "RS mul/div"),
  ("u_rs_fp", "RS FP"),
  ("u_busy_table", "Int busy table"),    ("u_fp_busy_table", "FP busy table"),
  ("u_fpu_lut", "FPU op decode"),        ("u_alu_lut", "ALU op decode"),
  ("u_amo_lut", "AMO op decode"),        ("u_muldiv_lut", "Mul/div op decode"),
  ("u_br_cmp", "Branch compare"),        ("u_atom_cmp", "AMO compare"),
  ("u_atom_add", "AMO adder"),           ("u_br_target", "Branch target"),
  ("u_jalr_target", "JALR target"),      ("u_auipc_adder", "AUIPC adder"),
  ("u_exec_branch", "Branch unit"),
  ("u_cdb_fifo", "CDB FIFO"),            ("u_cdb_mux", "CDB mux")
]

def moduleLabels : List (String × String) := [
  ("FPExecUnit", "FPU"),
  ("FPFMAD", "FMA·D"),                   ("FPFMA", "FMA·S"),
  ("FPMultiplierD", "FMul·D"),           ("FPMultiplier", "FMul·S"),
  ("FPAdderD", "FAdd·D"),                ("FPAdder", "FAdd·S"),
  ("FPDividerD", "FDiv·D"),              ("FPDivider", "FDiv·S"),
  ("FPSqrtD", "FSqrt·D"),                ("FPSqrt", "FSqrt·S"),
  ("FPDoubleMisc", "FMisc·D"),           ("FPMisc", "FMisc·S"),
  ("FPLongConverter", "FCvt·L"),         ("FPDoubleConverter", "FCvt·D"),
  ("Queue1Flow", "Pipe queue"),
  ("IntPhysRegFile", "Int PRF 64×64"),   ("FPPhysRegFile", "FP PRF 64×64"),
  ("BitmapFreeList_64_W2", "Int free list"),
  ("BitmapFreeList_64_W1", "FP free list"),
  ("IntRAT", "Int RAT"),                 ("RAT_", "FP RAT"),
  ("CRAT", "Checkpoint RAT"),
  ("IntRenameStage", "Int rename"),      ("FPRenameStage", "FP rename"),
  ("MulDivExecUnit", "Mul/Div"),         ("IntegerExecUnit", "Dual ALU"),
  ("PipelinedMultiplier", "Int multiplier"), ("Divider", "Int divider"),
  ("FallbackSequencer", "Zb* fallback"), ("TrapSequencer", "Trap sequencer"),
  ("StoreBuffer", "Store buffer"),       ("MemoryExecUnit", "AGU"),
  ("LSU", "LSU"),
  ("ROB", "ROB"),                        ("CSRFile", "CSR file")
]

/-- Label of the longest key in `table` that prefixes `name`. -/
def bestPrefix (table : List (String × String)) (name : String) : Option String :=
  let hits := table.filter (name.startsWith ·.1)
  let best := hits.foldl (fun (acc : Option (String × String)) h =>
    match acc with
    | some b => if h.1.length > b.1.length then some h else acc
    | none => some h) none
  best.map (·.2)

def label (inst : CircuitInstance) : String :=
  (bestPrefix instLabels inst.instName).getD <|
    (bestPrefix moduleLabels inst.moduleName).getD inst.moduleName

/-! ## Grouping -/

/-- A treemap leaf: possibly several same-label instances merged. -/
structure Item where
  label : String
  size  : Nat
  count : Nat := 1
  deriving Inhabited, Repr

def Item.name (it : Item) : String :=
  if it.count > 1 then s!"{it.label} ×{it.count}" else it.label

structure Group where
  sub   : Subsystem
  items : List Item
  deriving Inhabited

def Group.size (g : Group) : Nat := g.items.foldl (· + ·.size) 0

/-- Every subsystem, in the order groups are collected. -/
def subsystemOrder : List Subsystem :=
  [.execute, .rename, .issue, .retire, .microcode, .memory, .fetch, .decode, .glue]

/-- Containers at least this share of the core are shown one level deeper. -/
def expandShare : Float := 0.05
/-- Leaves below this share of the core fold into one "+N more" box. -/
def foldShare : Float := 0.0025

/-- Merge same-label items, keeping first-seen order. -/
def mergeItems (items : List Item) : List Item :=
  items.foldl (init := []) fun acc it =>
    match acc.find? (·.label == it.label) with
    | none => acc ++ [it]
    | some _ => acc.map fun a =>
        if a.label == it.label then { a with size := a.size + it.size, count := a.count + it.count }
        else a

/-- Largest first; ties broken by name so the layout is total. -/
def sortItems (items : List Item) : List Item :=
  items.toArray.qsort (fun a b => a.size > b.size || (a.size == b.size && a.name < b.name)) |>.toList

/-- Fold leaves smaller than `minSize` into one box when there are several. -/
def foldSmall (minSize : Nat) (items : List Item) : List Item :=
  let (small, big) := items.partition (·.size < minSize)
  if small.length < 2 then items else
  big ++ [{ label := s!"+{small.length} more", size := small.foldl (· + ·.size) 0 }]

/-- Items contributed by one top-level instance: the instance itself, or,
    for a large container, its children plus the container's own logic. -/
def instItems (reg : Std.HashMap String Circuit) (sizes : Std.HashMap String Nat)
    (total : Nat) (inst : CircuitInstance) : List Item :=
  let size := sizes.getD inst.moduleName 0
  let whole := [{ label := label inst, size := size : Item }]
  if size.toFloat < expandShare * total.toFloat then whole else
  match reg.get? inst.moduleName with
  | none => whole
  | some c =>
    if c.instances.isEmpty then whole else
    let kids := c.instances.map fun k => { label := label k, size := sizes.getD k.moduleName 0 : Item }
    let covered := kids.foldl (· + ·.size) 0
    let own := size - covered
    kids ++ (if own > 0 then [{ label := s!"{label inst} logic", size := own }] else [])

/-- Subsystem groups of `top`, largest first.  The top module's own gates are
    glue; items and groups are merged, folded and sorted for layout. -/
def buildGroups (circuits : List Circuit) (top : Circuit) : List Group × Nat :=
  let sizes := hierSizes circuits
  let reg : Std.HashMap String Circuit :=
    circuits.foldl (fun m c => if m.contains c.name then m else m.insert c.name c) {}
  let total := top.gates.length + top.instances.foldl (· + sizes.getD ·.moduleName 0) 0
  let minSize := (foldShare * total.toFloat).toUInt64.toNat
  let topGlue : Item := { label := "Top-level glue", size := top.gates.length }
  let groups := subsystemOrder.map fun sub =>
    let insts := top.instances.filter (classify ·.instName == sub)
    let raw := insts.flatMap (instItems reg sizes total)
    let raw := if sub == .glue then topGlue :: raw else raw
    { sub, items := sortItems (foldSmall minSize (mergeItems (raw.filter (·.size > 0)))) : Group }
  let groups := groups.filter (·.size > 0)
  let groups := groups.toArray.qsort (fun a b => a.size > b.size) |>.toList
  (groups, total)

/-- Top-level instances whose module is not a registry `Circuit`; their gates
    are not counted, and the footer says so. -/
def uncounted (circuits : List Circuit) (top : Circuit) : List String :=
  let names := circuits.map (·.name)
  (top.instances.map (·.moduleName)).filter (!names.contains ·) |>.eraseDups

/-! ## Squarified layout (Bruls, Huizing, van Wijk) -/

structure Rect (α : Type) where
  item : α
  x : Float
  y : Float
  w : Float
  h : Float

/-- Worst aspect ratio of a row of areas laid along a side of length `side`. -/
def worstRatio (areas : List Float) (side : Float) : Float :=
  let s := areas.foldl (· + ·) 0.0
  if areas.isEmpty || side <= 0.0 || s <= 0.0 then 1e18 else
  let hi := areas.foldl max 0.0
  let lo := areas.foldl min s
  let (side2, s2) := (side * side, s * s)
  max (side2 * hi / s2) (s2 / (side2 * lo))

/-- Greedily grow a row while the worst aspect ratio does not get worse. -/
def takeRow (side : Float) : List (α × Float) → List (α × Float) → List (α × Float) × List (α × Float)
  | row, [] => (row, [])
  | row, next :: rest =>
    if worstRatio ((row ++ [next]).map (·.2)) side <= worstRatio (row.map (·.2)) side
    then takeRow side (row ++ [next]) rest
    else (row, next :: rest)

/-- Lay out `items` (already scaled to area, largest first) in the box.
    `fuel` bounds the recursion: every step places at least one item. -/
def squarifyStep : Nat → List (α × Float) → Float → Float → Float → Float → List (Rect α)
  | 0, _, _, _, _, _ => []
  | _, [], _, _, _, _ => []
  | fuel + 1, first :: rest, x, y, w, h =>
    let horizontal := w < h  -- lay the row along the shorter side
    let side := if horizontal then w else h
    let (row, remaining) := takeRow side [first] rest
    let rowArea := row.foldl (· + ·.2) 0.0
    let depth := if side > 0.0 then rowArea / side else 0.0
    let (rects, _) := row.foldl (fun (acc, off) (it, area) =>
      let len := if depth > 0.0 then area / depth else 0.0
      let r : Rect _ := if horizontal
        then { item := it, x := x + off, y := y, w := len, h := depth }
        else { item := it, x := x, y := y + off, w := depth, h := len }
      (acc ++ [r], off + len)) ([], 0.0)
    rects ++ (if horizontal
      then squarifyStep fuel remaining x (y + depth) w (h - depth)
      else squarifyStep fuel remaining (x + depth) y (w - depth) h)

/-- Squarified treemap of `items` weighted by `weight`, largest first. -/
def squarify (items : List α) (weight : α → Float) (x y w h : Float) : List (Rect α) :=
  let total := items.foldl (· + weight ·) 0.0
  if total <= 0.0 || w <= 0.0 || h <= 0.0 then [] else
  let scaled := items.map fun it => (it, weight it / total * (w * h))
  let sorted := scaled.toArray.qsort (fun a b => a.2 > b.2) |>.toList
  squarifyStep sorted.length sorted x y w h

/-! ## Formatting -/

/-- One decimal place, clamped at 0 (coordinates and percentages only). -/
def fmt1 (f : Float) : String :=
  let t := (Float.round (f * 10.0)).toUInt64.toNat
  s!"{t / 10}.{t % 10}"

/-- 588358 → "588,358". -/
def commas (n : Nat) : String :=
  let rec group : List Char → List Char
    | a :: b :: c :: d :: rest => a :: b :: c :: ',' :: group (d :: rest)
    | other => other
  String.ofList (group (toString n).toList.reverse).reverse

def xmlEscape (s : String) : String :=
  s.foldl (fun acc c => acc ++ match c with
    | '&' => "&amp;" | '<' => "&lt;" | '>' => "&gt;" | '"' => "&quot;"
    | c => c.toString) ""

def pct (part total : Nat) : Float :=
  if total == 0 then 0.0 else part.toFloat / total.toFloat * 100.0

/-- Rough rendered width of `s` at font size `fs` (rounded sans ≈ 0.58 em). -/
def textWidth (s : String) (fs : Float) : Float := s.length.toFloat * fs * 0.58

/-! ## SVG -/

def canvasW : Float := 1600.0
def canvasH : Float := 1000.0
def margin : Float := 24.0
def mapTop : Float := 96.0
def headerH : Float := 30.0
def legendChars : Nat := 200
def fontStack : String := "'Nunito','Quicksand','Varela Round','Segoe UI','Helvetica Neue',sans-serif"

def rect (x y w h rx : Float) (fill stroke : String) (sw : Float) (extra := "") : String :=
  s!"<rect x=\"{fmt1 x}\" y=\"{fmt1 y}\" width=\"{fmt1 w}\" height=\"{fmt1 h}\" rx=\"{fmt1 rx}\" " ++
  s!"fill=\"{fill}\" stroke=\"{stroke}\" stroke-width=\"{fmt1 sw}\"{extra}/>\n"

def text (x y : Float) (cls : String) (body : String) (extra := "") : String :=
  s!"<text x=\"{fmt1 x}\" y=\"{fmt1 y}\" class=\"{cls}\"{extra}>{xmlEscape body}</text>\n"

def styleBlock : String :=
  "<style>\n" ++
  s!"text \{ font-family: {fontStack}; }\n" ++
  ".title { font-size: 26px; font-weight: 800; fill: #3d2c3e; }\n" ++
  ".subtitle { font-size: 13px; font-weight: 600; fill: #8a6f86; }\n" ++
  ".pill { font-size: 12px; font-weight: 800; }\n" ++
  ".sparkle { font-size: 15px; }\n" ++
  ".head { font-size: 14px; font-weight: 800; }\n" ++
  ".leaf { font-size: 11px; font-weight: 800; fill: #3d2c3e; }\n" ++
  ".leaf-s { font-size: 9.5px; font-weight: 700; fill: #3d2c3e; }\n" ++
  ".stats { font-size: 9.5px; font-weight: 700; }\n" ++
  ".legend { font-size: 10.5px; font-weight: 600; fill: #6b5a69; }\n" ++
  ".foot { font-size: 11px; font-weight: 600; fill: #a8949f; }\n" ++
  "</style>\n"

def defsBlock : String :=
  "<defs>\n" ++
  "<linearGradient id=\"bg\" x1=\"0\" y1=\"0\" x2=\"1\" y2=\"1\">" ++
  "<stop offset=\"0\" stop-color=\"#fff0f6\"/><stop offset=\"0.5\" stop-color=\"#fdf8ff\"/>" ++
  "<stop offset=\"1\" stop-color=\"#eef6ff\"/></linearGradient>\n" ++
  "<filter id=\"soft\" x=\"-5%\" y=\"-5%\" width=\"110%\" height=\"115%\">" ++
  "<feDropShadow dx=\"0\" dy=\"3\" stdDeviation=\"3\" flood-color=\"#c2255c\" flood-opacity=\"0.10\"/></filter>\n" ++
  styleBlock ++ "</defs>\n"

/-- Decorative sparkles sprinkled over the header (fixed positions). -/
def sparkles : String :=
  let spots : List (Float × Float × String × String) := [
    (648.0, 30.0, "✦", "#f783ac"), (676.0, 52.0, "✧", "#b197fc"),
    (700.0, 26.0, "✿", "#ffa8a8"), (1560.0, 78.0, "✧", "#74c0fc"),
    (18.0, 84.0, "✦", "#ffd43b")]
  String.join (spots.map fun (x, y, glyph, color) =>
    text x y "sparkle" glyph s!" fill=\"{color}\"")

def pill (x : Float) (body fill stroke ink : String) : String × Float :=
  let w := textWidth body 12.0 + 26.0
  (rect x 22.0 w 28.0 14.0 fill stroke 1.5 ++
   text (x + w / 2.0) 41.0 "pill" body s!" fill=\"{ink}\" text-anchor=\"middle\"", w)

/-- Header: title, subtitle and stat pills (all derived from the registry). -/
def header (total modules insts : Nat) : String := Id.run do
  let mut s := text margin 42.0 "title" "証明 Shoumei ✿ RV64G out-of-order core"
  s := s ++ text margin 66.0 "subtitle"
    "gate treemap · every box is a Lean Circuit · area ∝ hierarchical gate count · (ﾉ◕ヮ◕)ﾉ*:・ﾟ✧"
  let pills := [
    (s!"🌸 {commas total} gates", "#fff0f6", "#f783ac", "#c2255c"),
    (s!"🧩 {commas insts} instances", "#f3f0ff", "#b197fc", "#6741d9"),
    (s!"📦 {commas modules} modules", "#e7f5ff", "#74c0fc", "#1971c2")]
  let widths := pills.map fun (b, _, _, _) => textWidth b 12.0 + 26.0
  let mut x := canvasW - margin - widths.foldl (· + ·) 0.0 - 10.0 * (pills.length - 1).toFloat
  for (b, fill, stroke, ink) in pills do
    let (svg, w) := pill x b fill stroke ink
    s := s ++ svg
    x := x + w + 10.0
  s ++ sparkles

/-- Overflow entries: leaves too small to carry their own label. -/
structure Legend where
  entries : List String := []

def Legend.add (l : Legend) (entry : String) : Legend × Nat :=
  ({ entries := l.entries ++ [entry] }, l.entries.length + 1)

/-- Greedy wrap of legend entries into lines of at most `legendChars`. -/
def Legend.lines (l : Legend) : List String :=
  let sep := "   ·   "
  let (done, cur) := l.entries.foldl (fun (done, cur) e =>
    if cur.isEmpty then (done, e)
    else if cur.length + sep.length + e.length > legendChars then (done ++ [cur], e)
    else (done, cur ++ sep ++ e)) (([] : List String), "")
  if cur.isEmpty then done else done ++ [cur]

/-- Leaf label size bounds (px): big boxes get big labels, up to `leafFontMax`. -/
def leafFontMin : Float := 11.0
def leafFontMax : Float := 22.0

/-- Stats line size relative to the name line. -/
def statsScale : Float := 0.85

/-- Largest label size in bounds that fits both lines into a `w`×`h` box. -/
def leafFont (name stats : String) (w h : Float) : Float :=
  let chars := max name.length.toFloat (stats.length.toFloat * statsScale)
  let byW := (w - 12.0) / (chars * 0.58)
  max leafFontMin (min leafFontMax (min byW (h / 4.0)))

/-- One leaf box.  Label size degrades: title + stats → title → number badge. -/
def leaf (st : Style) (it : Item) (total : Nat) (r : Rect Item) (legend : Legend) : String × Legend :=
  let pad := 2.5
  let (x, y, w, h) := (r.x + pad, r.y + pad, r.w - 2.0 * pad, r.h - 2.0 * pad)
  let entry := s!"[{legend.entries.length + 1}] {it.name} {commas it.size}"
  if w < 3.0 || h < 3.0 then ("", (legend.add entry).1) else
  let box := rect x y w h 7.0 "#ffffff" st.ink 1.2
  let stats := s!"{commas it.size} · {fmt1 (pct it.size total)}%"
  let (cx, cy) := (x + w / 2.0, y + h / 2.0)
  let mid := " text-anchor=\"middle\""
  let fs := leafFont it.name stats w h
  let sfs := fs * statsScale
  if textWidth it.name fs <= w - 8.0 && textWidth stats sfs <= w - 8.0 && h >= 34.0 then
    (box ++ text cx (cy - 0.25 * fs) "leaf" it.name s!"{mid} style=\"font-size:{fmt1 fs}px\"" ++
      text cx (cy + 1.05 * fs) "stats" stats
        s!" fill=\"{st.ink}\"{mid} style=\"font-size:{fmt1 sfs}px\"", legend)
  else if textWidth it.name 9.5 <= w - 6.0 && h >= 16.0 then
    (box ++ text cx (cy + 3.5) "leaf-s" it.name mid, legend)
  else
    let (l, k) := legend.add entry
    if w >= 14.0 && h >= 13.0
    then (box ++ text cx (cy + 3.5) "stats" s!"{k}" s!" fill=\"{st.ink}\"{mid}", l)
    else (box, l)

/-- One subsystem panel with its leaves (or a compact one-line panel). -/
def panel (g : Group) (total : Nat) (r : Rect Group) (legend : Legend) : String × Legend := Id.run do
  let st := g.sub.style
  let pad := 4.0
  let (x, y, w, h) := (r.x + pad, r.y + pad, r.w - 2.0 * pad, r.h - 2.0 * pad)
  if w < 8.0 || h < 8.0 then return ("", legend)
  let full := s!"{st.emoji} {st.title}"
  -- Narrow panels keep just the emoji so the title never spills out.
  let name := if textWidth full 14.0 + 28.0 <= w then full else st.emoji
  let share := s!"{commas g.size} · {fmt1 (pct g.size total)}%"
  let mut s := rect x y w h 14.0 st.panel st.accent 2.0 " filter=\"url(#soft)\""
  -- Too short for header + leaves: one centred line.
  if h < headerH + 30.0 then
    let line := s!"{name} · {fmt1 (pct g.size total)}%"
    s := s ++ text (x + w / 2.0) (y + h / 2.0 + 5.0) "head" line
      s!" fill=\"{st.ink}\" text-anchor=\"middle\""
    return (s, legend)
  s := s ++ rect (x + 5.0) (y + 5.0) (w - 10.0) (headerH - 4.0) 10.0 "#ffffff" st.accent 1.0
  s := s ++ text (x + 14.0) (y + 24.0) "head" name s!" fill=\"{st.ink}\""
  if textWidth name 14.0 + textWidth share 14.0 + 40.0 <= w then
    s := s ++ text (x + w - 14.0) (y + 24.0) "head" share s!" fill=\"{st.accent}\" text-anchor=\"end\""
  let rects := squarify g.items (·.size.toFloat) (x + 6.0) (y + headerH + 6.0) (w - 12.0) (h - headerH - 12.0)
  let mut l := legend
  for c in rects do
    let (svg, l') := leaf st c.item total c l
    s := s ++ svg
    l := l'
  return (s, l)

/-- Complete SVG document. -/
def renderSvg (groups : List Group) (total modules insts : Nat) (missing : List String) : String := Id.run do
  -- First pass with an empty legend sizes the legend; the second pass lays
  -- out the map above it.  Legend content depends only on the map height,
  -- which is fixed after the first pass, so two passes are enough.
  let layout (mapH : Float) : String × Legend := Id.run do
    let rects := squarify groups (·.size.toFloat) margin mapTop (canvasW - 2.0 * margin) mapH
    let mut s := ""
    let mut l : Legend := {}
    for r in rects do
      let (svg, l') := panel r.item total r l
      s := s ++ svg
      l := l'
    return (s, l)
  let fullH := canvasH - mapTop - 40.0
  let (_, l0) := layout fullH
  let legendH (l : Legend) := if l.entries.isEmpty then 0.0 else l.lines.length.toFloat * 16.0 + 14.0
  let mapH := fullH - legendH l0 - (if l0.entries.isEmpty then 0.0 else 8.0)
  let (body, legend) := layout mapH

  let mut s := s!"<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"0 0 {fmt1 canvasW} {fmt1 canvasH}\" " ++
    s!"width=\"{fmt1 canvasW}\" height=\"{fmt1 canvasH}\">\n"
  s := s ++ defsBlock
  s := s ++ rect 0.0 0.0 canvasW canvasH 18.0 "url(#bg)" "#f3d9e6" 1.5
  s := s ++ header total modules insts
  s := s ++ body

  let lines := legend.lines
  if !lines.isEmpty then
    let ly := mapTop + mapH + 8.0
    s := s ++ rect margin ly (canvasW - 2.0 * margin) (legendH legend) 10.0 "#ffffff" "#f3d9e6" 1.0
    for (line, i) in lines.zipIdx do
      let lead := if i == 0 then "(◕ᴗ◕✿) tiny units: " else ""
      s := s ++ text (margin + 12.0) (ly + 18.0 + i.toFloat * 16.0) "legend" (lead ++ line)

  let note := if missing.isEmpty then "" else
    s!" · not counted (behavioural, not a gate netlist): {String.intercalate ", " missing}"
  s := s ++ text margin (canvasH - 14.0) "foot"
    s!"area ∝ DSL gates of the module and everything it instantiates{note}"
  s := s ++ text (canvasW - margin) (canvasH - 14.0) "foot"
    "drawn by Lean ✿ same bytes on every machine ✿ ayaya~" " text-anchor=\"end\""
  s ++ "</svg>\n"

/-! ## JSON (consumed by the Pages hub) -/

/-- Levels of instance hierarchy below each subsystem in the hub JSON. -/
def jsonDepth : Nat := 3

def jsonSize (j : Json) : Nat := (j.getObjValAs? Nat "size").toOption.getD 0

def sortBySize (js : List Json) : List Json :=
  js.toArray.qsort (fun a b => jsonSize a > jsonSize b) |>.toList

def node (name : String) (size : Nat) (kids : List Json) : Json :=
  let base := [("name", toJson name), ("size", toJson size)]
  Json.mkObj (if kids.isEmpty then base else base ++ [("children", Json.arr (sortBySize kids).toArray)])

/-- Subtree of module `mod`, `depth` levels deep.  The module's own gates are a
    "direct logic" child so every level sums to its parent. -/
def instJson (reg : Std.HashMap String Circuit) (sizes : Std.HashMap String Nat) :
    Nat → String → String → Json
  | 0, name, mod => node name (sizes.getD mod 0) []
  | d + 1, name, mod =>
    let size := sizes.getD mod 0
    match reg.get? mod with
    | none => node name size []
    | some c =>
      let live := c.instances.filter (sizes.getD ·.moduleName 0 > 0)
      let kids := live.map fun k => instJson reg sizes d (label k) k.moduleName
      let own := size - live.foldl (· + sizes.getD ·.moduleName 0) 0
      let kids := if own > 0 && !kids.isEmpty then kids ++ [node "direct logic" own []] else kids
      node name size kids

/-- Subsystem → instance hierarchy of `top`, unmerged and unfolded. -/
def hierarchyJson (circuits : List Circuit) (top : Circuit) (total : Nat) : Json :=
  let sizes := hierSizes circuits
  let reg : Std.HashMap String Circuit :=
    circuits.foldl (fun m c => if m.contains c.name then m else m.insert c.name c) {}
  let group (sub : Subsystem) : Json :=
    let insts := top.instances.filter (classify ·.instName == sub)
    let kids := insts.map fun i => instJson reg sizes jsonDepth (label i) i.moduleName
    let kids := if sub == .glue then node "Top-level glue" top.gates.length [] :: kids else kids
    let kids := kids.filter (jsonSize · > 0)
    let size := kids.foldl (· + jsonSize ·) 0
    Json.mkObj [
      ("name", toJson sub.style.title), ("color", toJson sub.style.panel),
      ("size", toJson size), ("children", Json.arr (sortBySize kids).toArray)]
  let groups := sortBySize ((subsystemOrder.map group).filter (jsonSize · > 0))
  Json.mkObj [
    ("name", toJson s!"{top.name} — Lean RTL"), ("short", toJson "Lean RTL"),
    ("size", toJson total), ("unit", toJson "gates"),
    ("children", Json.arr groups.toArray)]

/-! ## Entry point -/

def svgPath : System.FilePath := "docs/architecture-treemap.svg"
def svgCopyPath : System.FilePath := "output/architecture-treemap.svg"
def jsonPath : System.FilePath := "output/architecture-hierarchy.json"

/-- Write the treemap SVG (docs/ copy is committed, output/ copy feeds Pages)
    and the hierarchy JSON. -/
def generate (circuits : List Circuit) (top : Circuit) : IO Unit := do
  let (groups, total) := buildGroups circuits top
  let svg := renderSvg groups total circuits.length top.instances.length (uncounted circuits top)
  for p in [svgPath, svgCopyPath, jsonPath] do
    if let some dir := p.parent then IO.FS.createDirAll dir
  IO.FS.writeFile svgPath svg
  IO.FS.writeFile svgCopyPath svg
  IO.FS.writeFile jsonPath ((hierarchyJson circuits top total).pretty ++ "\n")
  IO.println s!"✓ Architecture treemap: {svgPath} ({commas total} gates)"

end Shoumei.Codegen.ArchitectureDiagram
