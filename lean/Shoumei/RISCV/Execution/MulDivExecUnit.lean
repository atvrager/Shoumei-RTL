/-
RISCV/Execution/MulDivExecUnit.lean - M-Extension Execution Unit

Wraps PipelinedMultiplier (3-cycle) and Divider32 (32-cycle) into a single
execution unit for M-extension multiply/divide operations.

Architecture:
- op[2] selects between multiplier (0) and divider (1)
  MUL=0, MULH=1, MULHSU=2, MULHU=3 → multiplier (op[2]=0)
  DIV=4, DIVU=5, REM=6, REMU=7     → divider (op[2]=1)
- Output MUX selects result from whichever unit produces valid_out
- busy signal reflects divider busy state (multiplier is pipelined, always ready)

Inputs: a[31:0], b[31:0], op[2:0], dest_tag[5:0], valid_in, clock, reset, zero, one
Outputs: result[31:0], tag_out[5:0], valid_out, busy
-/

import Shoumei.RISCV.ISA
import Shoumei.RISCV.Execution.Dispatch
import Shoumei.Circuits.Combinational.Multiplier
import Shoumei.Circuits.Sequential.Divider

namespace Shoumei.RISCV.Execution

open Shoumei
open Shoumei.RISCV
open Shoumei.Circuits.Combinational
open Shoumei.Circuits.Sequential

/-! ## Behavioral Model -/

/-- Combined MulDiv execution state.

    Tracks both the pipelined multiplier and sequential divider state. -/
structure MulDivExecState where
  /-- Pipelined multiplier state (3 pipeline stages) -/
  mulState : MulPipelineState
  /-- Sequential divider state (32-cycle FSM) -/
  divState : DividerState
  deriving Repr

/-- Initial (reset) state for MulDiv execution unit. -/
def MulDivExecState.init : MulDivExecState :=
  { mulState := MulPipelineState.init
    divState := {} }

/-- Step the MulDiv execution unit by one clock cycle.

    Routes operations based on opTypeToMulDivOpcode encoding:
    - Opcodes 0-3 (MUL, MULH, MULHSU, MULHU): multiplier
    - Opcodes 4-7 (DIV, DIVU, REM, REMU): divider

    Returns updated state and optional CDB broadcast result. -/
def mulDivStep
    (state : MulDivExecState)
    (a b : UInt32)
    (tag : Fin 64)
    (op : Nat)
    (valid : Bool)
    : MulDivExecState × Option (Fin 64 × UInt32) :=

  let is_div := op >= 4

  -- Step multiplier (always advances pipeline, even with invalid input)
  let mul_valid := valid && !is_div
  let (newMulState, mulResult) :=
    mulPipelineStep state.mulState a b tag op mul_valid

  -- Step divider
  let (newDivState, divResult) :=
    if valid && is_div && !state.divState.busy then
      -- Start new division
      let initState := dividerStart a b tag op
      dividerStep initState
    else
      -- Continue existing division (or idle)
      dividerStep state.divState

  -- Select result (multiplier or divider, only one can be valid at a time)
  let result := match divResult with
    | some r => some r
    | none => mulResult

  let newState := { mulState := newMulState, divState := newDivState }
  (newState, result)

/-- Whether the MulDiv unit is busy (cannot accept new divide operations). -/
def MulDivExecState.busy (state : MulDivExecState) : Bool :=
  state.divState.busy

/-! ## Structural Circuit -/

/-- Build MulDiv Execution Unit structural circuit.

    **Architecture:**
    - PipelinedMultiplier instance for MUL/MULH/MULHSU/MULHU
    - Divider32 instance for DIV/DIVU/REM/REMU
    - op[2] routes to multiplier (0) or divider (1)
    - Output MUX selects result from whichever unit produces valid

    **Inputs (76):**
    - a[31:0]: First operand
    - b[31:0]: Second operand
    - op[2:0]: MulDiv operation encoding
    - dest_tag[5:0]: Physical register tag for CDB broadcast
    - valid_in: New operation request
    - clock, reset: Sequential control
    - zero, one: Constant inputs

    **Outputs (40):**
    - result[31:0]: Computation result
    - tag_out[5:0]: Pass-through destination tag
    - valid_out: Result ready for CDB broadcast
    - busy: Cannot accept new divide operation

    **Instances:**
    - PipelinedMultiplier: 3-stage pipelined unsigned multiplier
    - Divider32: 32-cycle restoring divider
-/
def mkMulDivExecUnit : Circuit :=
  -- Inputs
  let a := makeIndexedWires "a" 32
  let b := makeIndexedWires "b" 32
  let op := makeIndexedWires "op" 3
  let dest_tag := makeIndexedWires "dest_tag" 6
  let valid_in := Wire.mk "valid_in"
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let zero := Wire.mk "zero"
  let one := Wire.mk "one"

  -- Outputs
  let result := makeIndexedWires "result" 32
  let tag_out := makeIndexedWires "tag_out" 6
  let valid_out := Wire.mk "valid_out"
  let busy := Wire.mk "busy"

  -- ========================================================================
  -- Routing: op[2] selects mul (0) vs div (1)
  -- ========================================================================
  let is_div := op[2]!  -- op[2] is already a wire
  let is_mul := Wire.mk "is_mul"
  let mul_valid := Wire.mk "mul_valid"
  let div_start := Wire.mk "div_start"

  let route_gates := [
    Gate.mkNOT is_div is_mul,
    Gate.mkAND valid_in is_mul mul_valid,
    Gate.mkAND valid_in is_div div_start
  ]

  -- ========================================================================
  -- PipelinedMultiplier instance
  -- ========================================================================
  let mul_result := makeIndexedWires "mul_result" 32
  let mul_tag_out := makeIndexedWires "mul_tag_out" 6
  let mul_valid_out := Wire.mk "mul_valid_out"

  let mul_inst : CircuitInstance := {
    moduleName := "PipelinedMultiplier"
    instName := "u_mul"
    portMap :=
      (a.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
      (b.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w))) ++
      (op.enum.map (fun ⟨i, w⟩ => (s!"op_{i}", w))) ++
      (dest_tag.enum.map (fun ⟨i, w⟩ => (s!"dest_tag_{i}", w))) ++
      [("valid_in", mul_valid),
       ("clock", clock),
       ("reset", reset),
       ("zero", zero)] ++
      (mul_result.enum.map (fun ⟨i, w⟩ => (s!"result_{i}", w))) ++
      (mul_tag_out.enum.map (fun ⟨i, w⟩ => (s!"tag_out_{i}", w))) ++
      [("valid_out", mul_valid_out)]
  }

  -- ========================================================================
  -- Divider32 instance
  -- ========================================================================
  let div_result := makeIndexedWires "div_result" 32
  let div_tag_out := makeIndexedWires "div_tag_out" 6
  let div_valid_out := Wire.mk "div_valid_out"
  let div_busy := Wire.mk "div_busy"

  let div_inst : CircuitInstance := {
    moduleName := "Divider32"
    instName := "u_div"
    portMap :=
      (a.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
      (b.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w))) ++
      (op.enum.map (fun ⟨i, w⟩ => (s!"op_{i}", w))) ++
      (dest_tag.enum.map (fun ⟨i, w⟩ => (s!"dest_tag_{i}", w))) ++
      [("start", div_start),
       ("clock", clock),
       ("reset", reset),
       ("one", one)] ++
      (div_result.enum.map (fun ⟨i, w⟩ => (s!"result_{i}", w))) ++
      (div_tag_out.enum.map (fun ⟨i, w⟩ => (s!"tag_out_{i}", w))) ++
      [("valid_out", div_valid_out),
       ("busy", div_busy)]
  }

  -- ========================================================================
  -- Output MUX: select between multiplier and divider results
  -- div_valid_out selects divider output; otherwise multiplier output
  -- ========================================================================
  let result_mux_gates := (List.range 32).map (fun i =>
    Gate.mkMUX (mul_result[i]!) (div_result[i]!) div_valid_out (result[i]!)
  )

  let tag_mux_gates := (List.range 6).map (fun i =>
    Gate.mkMUX (mul_tag_out[i]!) (div_tag_out[i]!) div_valid_out (tag_out[i]!)
  )

  -- valid_out = mul_valid_out OR div_valid_out
  let valid_gate := [Gate.mkOR mul_valid_out div_valid_out valid_out]

  -- busy = div_busy (multiplier is pipelined, always accepts)
  let busy_gate := [Gate.mkBUF div_busy busy]

  -- ========================================================================
  -- Assemble
  -- ========================================================================
  let all_gates :=
    route_gates ++
    result_mux_gates ++
    tag_mux_gates ++
    valid_gate ++
    busy_gate

  { name := "MulDivExecUnit"
    inputs := a ++ b ++ op ++ dest_tag ++ [valid_in, clock, reset, zero, one]
    outputs := result ++ tag_out ++ [valid_out, busy]
    gates := all_gates
    instances := [mul_inst, div_inst]
    -- V2 codegen annotations
    signalGroups := [
      { name := "a", width := 32, wires := a },
      { name := "b", width := 32, wires := b },
      { name := "op", width := 3, wires := op },
      { name := "dest_tag", width := 6, wires := dest_tag },
      { name := "result", width := 32, wires := result },
      { name := "tag_out", width := 6, wires := tag_out },
      { name := "mul_result", width := 32, wires := mul_result },
      { name := "mul_tag_out", width := 6, wires := mul_tag_out },
      { name := "div_result", width := 32, wires := div_result },
      { name := "div_tag_out", width := 6, wires := div_tag_out }
    ]
  }

/-- Convenience alias for the MulDiv execution unit circuit. -/
def mulDivExecUnit : Circuit := mkMulDivExecUnit

end Shoumei.RISCV.Execution
