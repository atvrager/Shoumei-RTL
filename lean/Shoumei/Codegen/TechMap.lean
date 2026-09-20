/-
Codegen/TechMap.lean - PDK technology mapper

Peepholes the ordered gate list into library cells:

  OR(g, AND(p, q))            -> ao21           (3 gates -> 1 cell)
  OR(AND(a,b), AND(c,d))      -> ao22
  XOR(XOR(a,b),ci)+carry      -> fa(a,b,ci)     (5 gates -> 1 cell)
  XOR(a,b)+AND(a,b)           -> ha(a,b)
  MUX                         -> mux2, or `assign` where the PDK has no mux cell

A peephole only fires when every intermediate wire it removes is read nowhere
else (exactly one load, and not a circuit output), so dropping it cannot change
any observable value.  Where a PDK lacks a non-inverting AND-OR cell (GF180),
`ao21`/`ao22` fall back to `aoi21`+`inv` / `aoi22`+`inv` -- still fewer cells
than the three or four gates they replace.
-/

import Shoumei.DSL
import Shoumei.Codegen.CellLibrary
import Shoumei.Codegen.CellLibs.Library
import Shoumei.Codegen.CellNetlist

namespace Shoumei.Codegen

open Shoumei
open Shoumei.Components

/-- A cell before drive-strength assignment. -/
structure PendingCell where
  function : CellFunction
  inputs   : List Wire
  outputs  : List Wire
  deriving Repr

/-- Combinational expression of a wire: a leaf (primary input / constant) or a
    gate applied to wires. -/
inductive Expr where
  | leaf (w : Wire)
  | gate (gt : GateType) (args : List Wire)
  deriving Repr

/-- Sanitize a wire name for use in an instance name. -/
private def instBase (w : Wire) : String :=
  w.name.replace "[" "_" |>.replace "]" "" |>.replace "." "_"

/-- Node table, structural key index, and load counts for a circuit. -/
structure Analysis where
  nodes : Std.HashMap String Expr
  byKey : Std.HashMap (GateType × List String) String
  loads : Std.HashMap String Nat

def analyze (c : Circuit) : Analysis := Id.run do
  let mut nodes : Std.HashMap String Expr := {}
  let mut byKey : Std.HashMap (GateType × List String) String := {}
  let mut loads : Std.HashMap String Nat := {}
  for g in c.gates do
    if g.gateType.isDFF then continue
    nodes := nodes.insert g.output.name (.gate g.gateType g.inputs)
    for i in g.inputs do loads := loads.insert i.name (loads.getD i.name 0 + 1)
    match g.inputs with
    | [a, b] =>
        byKey := byKey.insert (g.gateType, [a.name, b.name]) g.output.name
        byKey := byKey.insert (g.gateType, [b.name, a.name]) g.output.name
    | _ => pure ()
  for w in c.outputs do loads := loads.insert w.name (loads.getD w.name 0 + 1)
  for inst in c.instances do
    for (_, w) in inst.portMap do loads := loads.insert w.name (loads.getD w.name 0 + 1)
  return { nodes, byKey, loads }

/-- Result of peephole matching: wires consumed by a pattern, the cells to emit
    keyed by the gate output that triggers them, and any introduced wires. -/
structure MatchResult where
  absorbed : Std.HashSet String
  cellAt   : Std.HashMap String (List PendingCell)
  extra    : List Wire

/-- Match the patterns.  Pass order matters: full adders claim their wires
    first, then half adders, then AND-OR composites. -/
def matchPatterns (pdk : PDK) (c : Circuit) (a : Analysis) : MatchResult := Id.run do
  let lib := libraryFor pdk
  let hasFa := (lib.find .fa 1).isSome
  let hasHa := (lib.find .ha 1).isSome
  let hasAo21 := (lib.find .ao21 1).isSome
  let hasAo22 := (lib.find .ao22 1).isSome
  let isOut (n : String) : Bool := c.outputs.any (fun o => o.name == n)
  let load (n : String) : Nat := a.loads.getD n 0
  let mut absorbed : Std.HashSet String := {}
  let mut cellAt : Std.HashMap String (List PendingCell) := {}
  let mut extra : List Wire := []
  let claimed (n : String) : Bool := absorbed.contains n || cellAt.contains n

  -- Pass A: full adders (only where the library has a non-inverting one).
  for g in c.gates do
    if g.gateType.isDFF then continue
    let w := g.output
    if !hasFa || claimed w.name then continue
    match a.nodes.get? w.name with
    | some (.gate .XOR [x, ci]) =>
        if claimed x.name || isOut x.name then continue
        match a.nodes.get? x.name with
        | some (.gate .XOR [p, q]) =>
            match a.byKey.get? (.AND, [p.name, q.name]), a.byKey.get? (.AND, [ci.name, x.name]) with
            | some c1, some c2 =>
                if c1 ≠ c2 && c1 ≠ w.name && c2 ≠ w.name &&
                   !claimed c1 && !claimed c2 && !isOut c1 && !isOut c2 &&
                   load c1 == 1 && load c2 == 1 && load x.name == 2 then
                  match a.byKey.get? (.OR, [c1, c2]) with
                  | some cout =>
                      if !claimed cout then
                        absorbed := absorbed.insert x.name |>.insert c1 |>.insert c2 |>.insert cout
                        cellAt := cellAt.insert w.name
                          [{ function := .fa, inputs := [p, q, ci], outputs := [w, Wire.mk cout] }]
                  | none => pure ()
            | _, _ => pure ()
        | _ => pure ()
    | _ => pure ()

  -- Pass B: half adders (XOR(a,b) + AND(a,b)).
  for g in c.gates do
    if g.gateType.isDFF then continue
    let w := g.output
    if !hasHa || claimed w.name then continue
    if g.gateType == .AND then
      match g.inputs with
      | [p, q] =>
          match a.byKey.get? (.XOR, [p.name, q.name]) with
          | some x =>
              if !claimed x && !isOut x && load w.name ≤ 1 then
                absorbed := absorbed.insert w.name
                cellAt := cellAt.insert x
                  [{ function := .ha, inputs := [p, q], outputs := [Wire.mk x, w] }]
          | none => pure ()
      | _ => pure ()

  -- Pass C: AND-OR composites.
  for g in c.gates do
    if g.gateType.isDFF then continue
    let w := g.output
    if claimed w.name then continue
    if g.gateType == .OR then
      match g.inputs with
      | [i0, i1] =>
          let andOf (n : String) : Option (Wire × Wire) :=
            match a.nodes.get? n with
            | some (.gate .AND [p, q]) => some (p, q)
            | _ => none
          -- OR(g, AND(p,q)) with the AND read only here.
          let ao21 :=
            match andOf i0.name, andOf i1.name with
            | some (p, q), none =>
                if !claimed i0.name && !isOut i0.name && load i0.name == 1 then
                  some (p, q, i1, i0)
                else none
            | none, some (p, q) =>
                if !claimed i1.name && !isOut i1.name && load i1.name == 1 then
                  some (p, q, i0, i1)
                else none
            | _, _ => none
          -- OR(AND(a,b), AND(c,d)).
          let ao22 :=
            match andOf i0.name, andOf i1.name with
            | some (p, q), some (r, s) =>
                if !claimed i0.name && !claimed i1.name &&
                   !isOut i0.name && !isOut i1.name &&
                   load i0.name == 1 && load i1.name == 1 then
                  some (p, q, r, s)
                else none
            | _, _ => none
          match ao22, ao21 with
          | some (p, q, r, s), _ =>
              absorbed := absorbed.insert i0.name |>.insert i1.name
              if hasAo22 then
                cellAt := cellAt.insert w.name
                  [{ function := .ao22, inputs := [p, q, r, s], outputs := [w] }]
              else
                let mid := Wire.mk (w.name ++ "_aoin")
                extra := extra ++ [mid]
                cellAt := cellAt.insert w.name
                  [{ function := .aoi22, inputs := [p, q, r, s], outputs := [mid] },
                   { function := .inv, inputs := [mid], outputs := [w] }]
          | none, some (p, q, g0, pg) =>
              absorbed := absorbed.insert pg.name
              if hasAo21 then
                cellAt := cellAt.insert w.name
                  [{ function := .ao21, inputs := [p, q, g0], outputs := [w] }]
              else
                let mid := Wire.mk (w.name ++ "_aoin")
                extra := extra ++ [mid]
                cellAt := cellAt.insert w.name
                  [{ function := .aoi21, inputs := [p, q, g0], outputs := [mid] },
                   { function := .inv, inputs := [mid], outputs := [w] }]
          | none, none => pure ()
      | _ => pure ()

  return { absorbed, cellAt, extra }

/-- One-to-one mapping of a single gate to a cell. -/
private def oneToOne (g : Gate) : Option PendingCell :=
  let fn : Option CellFunction :=
    match g.gateType with
    | .AND => some .and2
    | .OR  => some .or2
    | .XOR => some .xor2
    | .NOT => some .inv
    | .BUF => some .buf
    | .MUX => some .mux2
    | _    => none
  fn.map fun f => { function := f, inputs := g.inputs, outputs := [g.output] }

/-- Peephole the ordered gate list into library cells. -/
def techMap (pdk : PDK) (c : Circuit) : CellNetlist :=
  let lib := libraryFor pdk
  let a := analyze c
  let m := matchPatterns pdk c a
  let pendings : List PendingCell :=
    (c.gates.filterMap fun g =>
      if g.gateType.isDFF then none
      else if m.absorbed.contains g.output.name then none
      else match m.cellAt.get? g.output.name with
           | some cells => some cells
           | none => (oneToOne g).map (fun pc => [pc])).flatten
  let cells := pendings.enum.map fun (idx, pc) =>
    let fanout := (pc.outputs.map (fun w => a.loads.getD w.name 0)).foldl max 0
    let drive := lib.driveFor fanout
    { cell := lib.find pc.function drive
      instName := s!"u_{instBase (pc.outputs.headD (Wire.mk "g"))}_{idx}"
      inputs := pc.inputs
      outputs := pc.outputs }
  { name := c.name
    pdk := pdk
    circuit := c
    inputs := c.inputs
    outputs := c.outputs
    cells := cells
    extraWires := m.extra }

end Shoumei.Codegen