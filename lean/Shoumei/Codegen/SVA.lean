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
def generateProperty (clk rst : String) (hasClock : Bool) (prop : SVAProperty) (idx : Nat) : String :=
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

  | .CapacityBound count cap =>
      s!"  // Formal Property: Occupancy never exceeds capacity\n" ++
      s!"  property p_capacity_bound_{idx};\n" ++
      s!"    {clkExpr} {disableExpr}\n" ++
      s!"    ({count} <= {cap});\n" ++
      s!"  endproperty\n" ++
      s!"  assert_capacity_bound_{idx}: assert property (p_capacity_bound_{idx});\n"

  | .Conservation enqValid enqReady deqValid deqReady count =>
      s!"  // Formal Monitor: Ghost transaction counters for conservation\n" ++
      s!"  int unsigned ghost_enqs_{idx};\n" ++
      s!"  int unsigned ghost_deqs_{idx};\n\n" ++
      s!"  always_ff @(posedge {clk}) begin\n" ++
      s!"    if ({rst}) begin\n" ++
      s!"      ghost_enqs_{idx} <= 0;\n" ++
      s!"      ghost_deqs_{idx} <= 0;\n" ++
      s!"    end else begin\n" ++
      s!"      if ({enqValid} && {enqReady}) ghost_enqs_{idx} <= ghost_enqs_{idx} + 1;\n" ++
      s!"      if ({deqValid} && {deqReady}) ghost_deqs_{idx} <= ghost_deqs_{idx} + 1;\n" ++
      s!"    end\n" ++
      s!"  end\n\n" ++
      s!"  // Formal Property: Exact conservation of items (count = enqs - deqs)\n" ++
      s!"  property p_conservation_{idx};\n" ++
      s!"    {clkExpr} {disableExpr}\n" ++
      s!"    ({count} == (ghost_enqs_{idx} - ghost_deqs_{idx}));\n" ++
      s!"  endproperty\n" ++
      s!"  assert_conservation_{idx}: assert property (p_conservation_{idx});\n"

  | .ResetClears qBus =>
      s!"  // Formal Property: Synchronous reset clears register\n" ++
      s!"  property p_reset_clears_{idx};\n" ++
      s!"    {clkExpr} {rst} |=> ({qBus} == '0);\n" ++
      s!"  endproperty\n" ++
      s!"  assert_reset_clears_{idx}: assert property (p_reset_clears_{idx});\n"

  | .DataCapture dBus qBus =>
      s!"  // Formal Property: Active clock edge latches data\n" ++
      s!"  property p_data_capture_{idx};\n" ++
      s!"    {clkExpr} {disableExpr}\n" ++
      s!"    1'b1 |=> ({qBus} == $past({dBus}));\n" ++
      s!"  endproperty\n" ++
      s!"  assert_data_capture_{idx}: assert property (p_data_capture_{idx});\n"

  | .EnableHolds enWire qBus =>
      s!"  // Formal Property: Clock enable low holds data\n" ++
      s!"  property p_enable_holds_{idx};\n" ++
      s!"    {clkExpr} {disableExpr}\n" ++
      s!"    !{enWire} |=> ({qBus} == $past({qBus}));\n" ++
      s!"  endproperty\n" ++
      s!"  assert_enable_holds_{idx}: assert property (p_enable_holds_{idx});\n"

  | .EnableCapture enWire dBus qBus =>
      s!"  // Formal Property: Clock enable high latches data\n" ++
      s!"  property p_enable_capture_{idx};\n" ++
      s!"    {clkExpr} {disableExpr}\n" ++
      s!"    {enWire} |=> ({qBus} == $past({dBus}));\n" ++
      s!"  endproperty\n" ++
      s!"  assert_enable_capture_{idx}: assert property (p_enable_capture_{idx});\n"

  | .LatencyCapture dBus qBus cycles =>
      s!"  // Formal Property: Multi-cycle pipeline latency (Z^-{cycles})\n" ++
      s!"  property p_latency_capture_{idx};\n" ++
      s!"    {clkExpr} {disableExpr}\n" ++
      s!"    (!{rst} [* {cycles}]) |-> ({qBus} == $past({dBus}, {cycles}));\n" ++
      s!"  endproperty\n" ++
      s!"  assert_latency_capture_{idx}: assert property (p_latency_capture_{idx});\n"

  | .DecoupledEquiv valA rdyA dataA valB rdyB dataB =>
      s!"  // Formal Property: Decoupled transaction equivalence\n" ++
      s!"  property p_decoupled_equiv_{idx};\n" ++
      s!"    {clkExpr} {disableExpr}\n" ++
      s!"    ({valA} && {rdyA} && {valB} && {rdyB}) |-> ({dataA} == {dataB});\n" ++
      s!"  endproperty\n" ++
      s!"  assert_decoupled_equiv_{idx}: assert property (p_decoupled_equiv_{idx});\n"

  | .LogicOp aBus bBus opBus resBus =>
      if hasClock then
        s!"  // Formal Property: LogicUnit functional truth table (clocked)\n" ++
        s!"  property p_logic_and_{idx};\n" ++
        s!"    {clkExpr} {disableExpr}\n" ++
        s!"    ({opBus} == 2'b00) |-> ({resBus} == ({aBus} & {bBus}));\n" ++
        s!"  endproperty\n" ++
        s!"  assert_logic_and_{idx}: assert property (p_logic_and_{idx});\n\n" ++
        s!"  property p_logic_or_{idx};\n" ++
        s!"    {clkExpr} {disableExpr}\n" ++
        s!"    ({opBus} == 2'b01) |-> ({resBus} == ({aBus} | {bBus}));\n" ++
        s!"  endproperty\n" ++
        s!"  assert_logic_or_{idx}: assert property (p_logic_or_{idx});\n\n" ++
        s!"  property p_logic_xor_{idx};\n" ++
        s!"    {clkExpr} {disableExpr}\n" ++
        s!"    ({opBus}[1] == 1'b1) |-> ({resBus} == ({aBus} ^ {bBus}));\n" ++
        s!"  endproperty\n" ++
        s!"  assert_logic_xor_{idx}: assert property (p_logic_xor_{idx});\n"
      else
        s!"  // Formal Property: LogicUnit functional truth table (combinational)\n" ++
        s!"  always_comb begin\n" ++
        s!"    if ({opBus} == 2'b00) assert_logic_and_{idx}: assert ({resBus} == ({aBus} & {bBus}));\n" ++
        s!"    if ({opBus} == 2'b01) assert_logic_or_{idx}: assert ({resBus} == ({aBus} | {bBus}));\n" ++
        s!"    if ({opBus}[1] == 1'b1) assert_logic_xor_{idx}: assert ({resBus} == ({aBus} ^ {bBus}));\n" ++
        s!"  end\n"

/-- Emit all formal SVA assertions for a circuit if any exist. -/
def emitSVA (c : Circuit) (clockWires resetWires : List Wire) : String :=
  if c.svaProperties.isEmpty then ""
  else
    let hasClock := !clockWires.isEmpty
    let clk := clockWires.head?.map (·.name) |>.getD "clock"
    let rst := resetWires.head?.map (·.name) |>.getD "reset"
    let props := c.svaProperties.enum.map (fun (idx, p) => generateProperty clk rst hasClock p idx)
    let body := String.intercalate "\n" props
    s!"`ifdef FORMAL\n" ++
    s!"  `define SHOUMEI_FORMAL_ASSERT\n" ++
    s!"`elsif SYNTHESIS\n" ++
    s!"  // Synthesis without FORMAL: exclude assertions\n" ++
    s!"`else\n" ++
    s!"  `define SHOUMEI_FORMAL_ASSERT\n" ++
    s!"`endif\n\n" ++
    s!"`ifdef SHOUMEI_FORMAL_ASSERT\n" ++
    s!"  // --------------------------------------------------------------------------\n" ++
    s!"  // Formal Properties (proven in Lean theorem prover)\n" ++
    s!"  // --------------------------------------------------------------------------\n" ++
    body ++ "\n" ++
    s!"  `undef SHOUMEI_FORMAL_ASSERT\n" ++
    s!"`endif\n"

end Shoumei.Codegen.SVA
