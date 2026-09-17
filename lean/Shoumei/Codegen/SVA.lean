/-
Codegen/SVA.lean - SystemVerilog Assertions (SVA) Generator

Translates formal temporal properties proven in Lean into IEEE 1800-2017
SystemVerilog Assertions (`assert property`).

Enclosed under `ifndef SYNTHESIS to guarantee zero overhead during ASIC/FPGA
synthesis while providing runtime assertion checks in Verilator/VCS and formal
verification in SymbiYosys/JasperGold/VC Formal.
-/

import Shoumei.DSL

namespace Shoumei.Codegen.SVA

open Shoumei

/-- Generate a single SVA property string. -/
def generateProperty (clk rst : String) (prop : SVAProperty) (idx : Nat) : String :=
  let clkExpr := s!"@(posedge {clk})"
  let disableExpr := s!"disable iff ({rst})"
  match prop with
  | .Always w expected =>
      let expr := if expected then w else s!"!{w}"
      s!"  // Formal Property: {w} is invariant\n" ++
      s!"  property p_always_{idx};\n" ++
      s!"    {clkExpr} {disableExpr} {expr};\n" ++
      s!"  endproperty\n" ++
      s!"  assert_always_{idx}: assert property (p_always_{idx});\n"

  | .HandshakeStable valid ready data =>
      s!"  // Formal Property: Decoupled handshake stability\n" ++
      s!"  property p_handshake_stable_{idx};\n" ++
      s!"    {clkExpr} {disableExpr}\n" ++
      s!"    ({valid} && !{ready}) |=> ({valid} && $stable({data}));\n" ++
      s!"  endproperty\n" ++
      s!"  assert_handshake_stable_{idx}: assert property (p_handshake_stable_{idx});\n"

  | .ImpliesNext ante anteVal conseq conseqVal =>
      let anteExpr := if anteVal then ante else s!"!{ante}"
      let conseqExpr := if conseqVal then conseq else s!"!{conseq}"
      s!"  // Formal Property: {ante} implies next {conseq}\n" ++
      s!"  property p_implies_next_{idx};\n" ++
      s!"    {clkExpr} {disableExpr}\n" ++
      s!"    ({anteExpr}) |=> ({conseqExpr});\n" ++
      s!"  endproperty\n" ++
      s!"  assert_implies_next_{idx}: assert property (p_implies_next_{idx});\n"

  | .ImpliesOverlap ante anteVal conseq conseqVal =>
      let anteExpr := if anteVal then ante else s!"!{ante}"
      let conseqExpr := if conseqVal then conseq else s!"!{conseq}"
      s!"  // Formal Property: {ante} implies {conseq}\n" ++
      s!"  property p_implies_overlap_{idx};\n" ++
      s!"    {clkExpr} {disableExpr}\n" ++
      s!"    ({anteExpr}) |-> ({conseqExpr});\n" ++
      s!"  endproperty\n" ++
      s!"  assert_implies_overlap_{idx}: assert property (p_implies_overlap_{idx});\n"

  | .FullNotReady count cap ready =>
      s!"  // Formal Property: Full queue backpressures enqueue\n" ++
      s!"  property p_full_not_ready_{idx};\n" ++
      s!"    {clkExpr} {disableExpr}\n" ++
      s!"    ({count} == {cap}) |-> !{ready};\n" ++
      s!"  endproperty\n" ++
      s!"  assert_full_not_ready_{idx}: assert property (p_full_not_ready_{idx});\n"

  | .EmptyNotValid count valid =>
      s!"  // Formal Property: Empty queue does not assert valid\n" ++
      s!"  property p_empty_not_valid_{idx};\n" ++
      s!"    {clkExpr} {disableExpr}\n" ++
      s!"    ({count} == 0) |-> !{valid};\n" ++
      s!"  endproperty\n" ++
      s!"  assert_empty_not_valid_{idx}: assert property (p_empty_not_valid_{idx});\n"

/-- Emit all formal SVA assertions for a circuit if any exist. -/
def emitSVA (c : Circuit) (clockWires resetWires : List Wire) : String :=
  if c.svaProperties.isEmpty then ""
  else
    let clk := clockWires.head?.map (·.name) |>.getD "clock"
    let rst := resetWires.head?.map (·.name) |>.getD "reset"
    let props := c.svaProperties.enum.map (fun (idx, p) => generateProperty clk rst p idx)
    let body := String.intercalate "\n" props
    s!"`ifndef SYNTHESIS\n" ++
    s!"  // --------------------------------------------------------------------------\n" ++
    s!"  // Formal Properties (proven in Lean theorem prover)\n" ++
    s!"  // --------------------------------------------------------------------------\n" ++
    body ++ "\n" ++
    s!"`endif\n"

end Shoumei.Codegen.SVA
