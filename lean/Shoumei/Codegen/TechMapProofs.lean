/-
Codegen/TechMapProofs.lean - Lean tier of the technology-mapping proof

Two layers:

1. **Peephole lemmas.**  Each rewrite the mapper performs replaces a small
   gate sub-graph with a cell whose `CellFunction.model` is fixed.  The lemmas
   below show the cell's Boolean function is exactly the sub-graph's, so the
   rewrite is value-preserving.

2. **End-to-end checks.**  For the adders, every input is enumerated at the
   small widths on both PDKs and the mapped netlist's sum is compared against
   Nat arithmetic -- the whole mapping (peephole choice, drive assignment,
   pin order, fallbacks) is exercised at once.

The Yosys miter check (`verification/techmap-equiv.sh`) is the independent
cross-check that the *emitted text* matches, using cell models translated from
the PDK Liberty rather than from these tables.
-/

import Shoumei.Codegen.TechMap
import Shoumei.Circuits.Combinational.PrefixAdderProofs
import Std.Data.HashMap

namespace Shoumei.Codegen

open Shoumei
open Shoumei.Components
open Shoumei.Circuits.Combinational

/-! ## 1. Peephole lemmas -/

/-- `OR(g, AND(p,q))` is exactly the `ao21` cell. -/
theorem peephole_ao21 (p q g : Bool) :
    CellFunction.model .ao21 [p, q, g] = [g || (p && q)] := by
  cases p <;> cases q <;> cases g <;> rfl

/-- `OR(AND(a,b), AND(c,d))` is exactly the `ao22` cell. -/
theorem peephole_ao22 (a b c d : Bool) :
    CellFunction.model .ao22 [a, b, c, d] = [(a && b) || (c && d)] := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

/-- `aoi21` followed by `inv` is the non-inverting AND-OR (the GF180 fallback). -/
theorem peephole_aoi21_inv (p q g : Bool) :
    (CellFunction.model .inv (CellFunction.model .aoi21 [p, q, g])) = [g || (p && q)] := by
  cases p <;> cases q <;> cases g <;> rfl

/-- `aoi22` followed by `inv` is the non-inverting AND-OR. -/
theorem peephole_aoi22_inv (a b c d : Bool) :
    (CellFunction.model .inv (CellFunction.model .aoi22 [a, b, c, d]))
      = [(a && b) || (c && d)] := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

/-- `XOR(a,b)` + `AND(a,b)` is exactly the `ha` cell (`[sum, carry]`). -/
theorem peephole_ha (a b : Bool) :
    CellFunction.model .ha [a, b] = [xor a b, a && b] := by
  cases a <;> cases b <;> rfl

/-- `XOR(XOR(a,b),ci)` + `OR(AND(a,b), AND(ci, XOR(a,b)))` is the `fa` cell. -/
theorem peephole_fa (a b ci : Bool) :
    CellFunction.model .fa [a, b, ci]
      = [xor (xor a b) ci, (a && b) || (ci && xor a b)] := by
  cases a <;> cases b <;> cases ci <;> rfl

/-- A library multiplexer is the DSL `MUX`. -/
theorem peephole_mux2 (i0 i1 s : Bool) :
    CellFunction.model .mux2 [i0, i1, s] = [if s then i1 else i0] := by
  cases i0 <;> cases i1 <;> cases s <;> rfl

/-! ## 2. End-to-end checks over the mapped adders -/

/-- A mapped netlist compiled to integer wire indices. -/
structure NetPlan where
  ops    : Array (Option CellFunction × List Nat × List Nat)
  size   : Nat
  cinIdx : Option Nat
  oneIdx : Nat
  sumIdx : List Nat

/-- Wire indices: `a_i` = i, `b_i` = width+i, then `cin`, `one`, `zero`, then
    one index per cell output in order. -/
def buildNetPlan (n : CellNetlist) (width : Nat) : NetPlan := Id.run do
  let hasCin := n.circuit.inputs.any (fun w => w.name == "cin")
  let cinBase := 2 * width
  let oneIdx := cinBase + (if hasCin then 1 else 0)
  let mut idx : Std.HashMap String Nat := {}
  for i in List.range width do
    idx := idx.insert s!"a_{i}" i
    idx := idx.insert s!"b_{i}" (width + i)
  if hasCin then idx := idx.insert "cin" cinBase
  idx := idx.insert "one" oneIdx
  idx := idx.insert "zero" (oneIdx + 1)
  let mut next := oneIdx + 2
  let mut ops : Array (Option CellFunction × List Nat × List Nat) := #[]
  for ci in n.cells do
    let mut oi : List Nat := []
    for w in ci.outputs do
      oi := oi ++ [next]
      idx := idx.insert w.name next
      next := next + 1
    ops := ops.push (ci.cell.map (·.function),
                     ci.inputs.map (fun w => idx.getD w.name 0), oi)
  let sumIdx := (List.range width).map (fun i => idx.getD s!"sum_{i}" 0)
  return { ops, size := next, cinIdx := if hasCin then some cinBase else none, oneIdx, sumIdx }

def runNetPlan (p : NetPlan) (width : Nat) (cin : Bool) (a b : Nat) : Nat := Id.run do
  let mut arr := Array.replicate p.size false
  for i in List.range width do
    arr := arr.set! i (((a >>> i) &&& 1) == 1)
    arr := arr.set! (width + i) (((b >>> i) &&& 1) == 1)
  if let some ci := p.cinIdx then arr := arr.set! ci cin
  arr := arr.set! p.oneIdx true
  for (fn, ins, outs) in p.ops do
    let vals := ins.map (fun k => arr.getD k false)
    let res := match fn with
      | some f => f.model vals
      | none   => CellFunction.model .mux2 vals
    for (o, v) in outs.zip res do
      arr := arr.set! o v
  return bitsToNat (p.sumIdx.map (fun k => arr.getD k false))

/-- Exhaustively compare a mapped adder against Nat arithmetic. -/
def checkMapped (pdk : PDK) (tree : PrefixTree) (width : Nat) (cin : CinMode) : Bool :=
  let p := buildNetPlan (techMap pdk (mkPrefixAdderCircuit tree width cin)) width
  (List.range (2 ^ width)).all fun a =>
    (List.range (2 ^ width)).all fun b =>
      (match cin with | .input => [false, true] | _ => [false]).all fun ci =>
        runNetPlan p width ci a b == expectedSum cin ci a b % 2 ^ width

/-- Every prefix adder maps correctly at width 4 on both PDKs. -/
theorem techMap_adders_correct :
    ([PDK.asap7, PDK.gf180mcu].all fun pdk =>
      allTrees.all fun t => allCins.all fun ci => checkMapped pdk t 4 ci) = true := by
  native_decide

end Shoumei.Codegen