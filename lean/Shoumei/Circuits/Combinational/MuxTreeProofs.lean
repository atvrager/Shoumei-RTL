/-
Circuits/Combinational/MuxTreeProofs.lean - Formal Verification for N-to-1 Multiplexer Trees

Comprehensive 4-level formal verification hierarchy (L0-L3):
- L0: Structural properties (gate counts, port widths, concrete instances)
- L1: Functional truth table (exhaustive 4:1 check, single-bit symbolic evaluation, operation modes)
- L2: Hardware soundness invariants (wire preservation, combinational-only gates, driver uniqueness nodup, zero-DFF statelessness)
- L3: Information flow non-interference and temporal memoryless refinement
-/

import Shoumei.DSL
import Shoumei.Semantics
import Shoumei.Reflection.CompileCircuit
import Shoumei.Temporal.Trace
import Shoumei.Circuits.Combinational.MuxTree

namespace Shoumei.Circuits.Combinational

open Shoumei
open Shoumei.Reflection
open Shoumei.Temporal

/-! ## L0: Structural Proofs -/

/-! ### Mux2x8 (2:1 MUX, 8 bits) -/

theorem mux2x8_structure :
  mkMux2x8.inputs.length = 17 ∧
  mkMux2x8.outputs.length = 8 := by native_decide

theorem mux2x8_gate_count :
  mkMux2x8.gates.length = 32 := by native_decide

theorem mux2x8_formula :
  -- Formula: (n-1) * width * 4 = (2-1) * 8 * 4 = 32
  mkMux2x8.gates.length = (2 - 1) * 8 * 4 := by native_decide

/-! ### Mux4x8 (4:1 MUX, 8 bits) -/

theorem mux4x8_structure :
  mkMux4x8.inputs.length = 34 ∧
  mkMux4x8.outputs.length = 8 := by native_decide

theorem mux4x8_gate_count :
  mkMux4x8.gates.length = 96 := by native_decide

theorem mux4x8_formula :
  -- Formula: (n-1) * width * 4 = (4-1) * 8 * 4 = 96
  mkMux4x8.gates.length = (4 - 1) * 8 * 4 := by native_decide

/-! ### Mux4x32 (4:1 MUX, 32 bits) -/

theorem mux4x32_structure :
  mkMux4x32.inputs.length = 130 ∧
  mkMux4x32.outputs.length = 32 := by native_decide

theorem mux4x32_gate_count :
  mkMux4x32.gates.length = 384 := by native_decide

theorem mux4x32_formula :
  mkMux4x32.gates.length = (4 - 1) * 32 * 4 := by native_decide

/-! ### Mux32x6 (32:1 MUX, 6 bits) - For RAT read ports -/

theorem mux32x6_structure :
  mkMux32x6.inputs.length = 197 ∧
  mkMux32x6.outputs.length = 6 := by native_decide

theorem mux32x6_gate_count :
  mkMux32x6.gates.length = 744 := by native_decide

theorem mux32x6_formula :
  -- Formula: (n-1) * width * 4 = (32-1) * 6 * 4 = 744
  mkMux32x6.gates.length = (32 - 1) * 6 * 4 := by native_decide

theorem mux32x6_inputs_breakdown :
  -- 32 inputs * 6 bits + 5 select bits = 192 + 5 = 197
  mkMux32x6.inputs.length = 32 * 6 + 5 := by native_decide

/-! ### Mux64x32 (64:1 MUX, 32 bits) - For PhysRegFile read ports -/

theorem mux64x32_structure :
  mkMux64x32.inputs.length = 2054 ∧
  mkMux64x32.outputs.length = 32 := by native_decide

theorem mux64x32_gate_count :
  mkMux64x32.gates.length = 8064 := by native_decide

theorem mux64x32_formula :
  -- Formula: (n-1) * width * 4 = (64-1) * 32 * 4 = 8064
  mkMux64x32.gates.length = (64 - 1) * 32 * 4 := by native_decide

theorem mux64x32_inputs_breakdown :
  -- 64 inputs * 32 bits + 6 select bits = 2048 + 6 = 2054
  mkMux64x32.inputs.length = 64 * 32 + 6 := by native_decide

/-! ### General Determinism Properties -/

theorem mux2x8_deterministic :
  ∀ g ∈ mkMux2x8.gates, g.inputs.length > 0 := by native_decide

theorem mux4x8_deterministic :
  ∀ g ∈ mkMux4x8.gates, g.inputs.length > 0 := by native_decide

theorem mux32x6_deterministic :
  ∀ g ∈ mkMux32x6.gates, g.inputs.length > 0 := by native_decide

theorem mux64x32_deterministic :
  ∀ g ∈ mkMux64x32.gates, g.inputs.length > 0 := by native_decide

/-! ## L1: Functional Correctness Proofs -/

/-- Operation mode: sel=0 selects in0. -/
theorem mux2_sel_false (in0 in1 : Bool) : mux2 false in0 in1 = in0 := rfl

/-- Operation mode: sel=1 selects in1. -/
theorem mux2_sel_true (in0 in1 : Bool) : mux2 true in0 in1 = in1 := rfl

/-- **Theorem (L1 Single-Bit Semantic Evaluation)**:
    Evaluating the 4 gates of mkMux2Bit produces mux2(sel, in0, in1) on the output wire. -/
theorem evalGates_mux2Bit_result (pfx : String) (idx : Nat) (in0 in1 sel out : Wire) (env : Env)
    (h_and0_and1 : (Wire.mk s!"and0_{pfx}_{idx}" == Wire.mk s!"and1_{pfx}_{idx}") = false)
    (h_in0_not  : (in0 == Wire.mk s!"not_sel_{pfx}_{idx}") = false)
    (h_in1_not  : (in1 == Wire.mk s!"not_sel_{pfx}_{idx}") = false)
    (h_in1_and0 : (in1 == Wire.mk s!"and0_{pfx}_{idx}") = false)
    (h_sel_not  : (sel == Wire.mk s!"not_sel_{pfx}_{idx}") = false)
    (h_sel_and0 : (sel == Wire.mk s!"and0_{pfx}_{idx}") = false) :
    evalGates (mkMux2Bit pfx idx in0 in1 sel out) env out =
    mux2 (env sel) (env in0) (env in1) := by
  dsimp [mkMux2Bit, evalGates, evalGate, Gate.mkNOT, Gate.mkAND, Gate.mkOR, updateEnv, mux2]
  simp [h_and0_and1, h_in0_not, h_in1_not, h_in1_and0, h_sel_not, h_sel_and0]
  cases env sel <;> cases env in0 <;> cases env in1 <;> rfl

/-- 4:1 1-bit Mux circuit instance for exhaustive verification. -/
def mkMux4x1 : Circuit := mkMuxTree 4 1

/-- Helper: Construct input WireMap for 4:1 1-bit MUX. -/
def makeMux4x1WireMap (in0 in1 in2 in3 sel0 sel1 : Bool) : WireMap :=
  [
    (Wire.mk "in0_0", in0),
    (Wire.mk "in1_0", in1),
    (Wire.mk "in2_0", in2),
    (Wire.mk "in3_0", in3),
    (Wire.mk "sel_0", sel0),
    (Wire.mk "sel_1", sel1)
  ]

/-- Expected selection function for 4:1 multiplexer. -/
def expectedMux4 (in0 in1 in2 in3 sel0 sel1 : Bool) : Bool :=
  match sel1, sel0 with
  | false, false => in0
  | false, true  => in1
  | true,  false => in2
  | true,  true  => in3

/-- Check that 4:1 MUX computes expected selection for given inputs. -/
def checkMux4x1 (in0 in1 in2 in3 sel0 sel1 : Bool) : Bool :=
  let m := makeMux4x1WireMap in0 in1 in2 in3 sel0 sel1
  let res := compileCircuit mkMux4x1 m
  let out := res.lookup (Wire.mk "out_0")
  out == expectedMux4 in0 in1 in2 in3 sel0 sel1

/-- Exhaustive check across all 64 input combinations for 4:1 MUX. -/
def checkMux4x1All : Bool :=
  let bools := [false, true]
  bools.all fun in0 => bools.all fun in1 => bools.all fun in2 => bools.all fun in3 =>
  bools.all fun sel0 => bools.all fun sel1 =>
    checkMux4x1 in0 in1 in2 in3 sel0 sel1

/-- **Theorem (L1 Exhaustive Functional Truth)**:
    4:1 Multiplexer correctly routes the selected input to the output across all 64 input combinations. -/
theorem mux4x1_exhaustive_correct : checkMux4x1All = true := by
  native_decide

/-- Bridge theorem connecting compileCircuit to evalCircuit for mkMux4x1. -/
theorem evalCircuit_mux4x1_agrees_compileCircuit (initMap : WireMap) (inputEnv : Env)
    (h : ∀ w, initMap.lookup w = inputEnv w) (w : Wire) :
    evalCircuit mkMux4x1 inputEnv w = (compileCircuit mkMux4x1 initMap).lookup w := by
  rw [compileCircuit_correct mkMux4x1 initMap inputEnv h w]

/-- **Theorem (L1 Subtree Composition)**:
    A 2:1 multiplexer combining the results of a left subtree and a right subtree
    routes leftOut when MSB is false, and rightOut when MSB is true. -/
theorem mux_subtree_composition (leftOut rightOut topSel : Bool) :
    mux2 topSel leftOut rightOut = (if topSel then rightOut else leftOut) := rfl

/-! ## L2: Inductive Invariants & Hardware Soundness -/

/-- **Theorem (L2 Wire Preservation Invariant)**:
    Evaluating mkMux2Bit preserves every wire disjoint from its internal nets and output. -/
theorem evalGates_mux2Bit_preserves (pfx : String) (idx : Nat) (in0 in1 sel out : Wire)
    (env : Env) (w : Wire)
    (h_not : (w == Wire.mk s!"not_sel_{pfx}_{idx}") = false)
    (h_and0 : (w == Wire.mk s!"and0_{pfx}_{idx}") = false)
    (h_and1 : (w == Wire.mk s!"and1_{pfx}_{idx}") = false)
    (h_out : (w == out) = false) :
    evalGates (mkMux2Bit pfx idx in0 in1 sel out) env w = env w := by
  dsimp [mkMux2Bit, evalGates, evalGate, Gate.mkNOT, Gate.mkAND, Gate.mkOR, updateEnv]
  simp [h_not, h_and0, h_and1, h_out]

/-- **Theorem (L2 Combinational Purity Invariant)**:
    Every gate in mkMux2Bit is strictly combinational. -/
theorem mux2Bit_gate_type_invariant (pfx : String) (idx : Nat) (in0 in1 sel out : Wire) :
    ∀ g ∈ mkMux2Bit pfx idx in0 in1 sel out, g.gateType.isCombinational = true := by
  intro g hg
  dsimp [mkMux2Bit] at hg
  simp only [List.mem_cons, List.not_mem_nil] at hg
  rcases hg with rfl | rfl | rfl | rfl | h_false
  · rfl
  · rfl
  · rfl
  · rfl
  · cases h_false

/-- **Theorem (L2 Driver Uniqueness Invariant - 2x8)**:
    Every gate in mkMux2x8 drives a unique, non-overlapping output wire. -/
theorem mux2x8_nodup_drivers :
    ((mkMux2x8).gates.map Gate.output).Nodup := by
  native_decide

/-- **Theorem (L2 Driver Uniqueness Invariant - 4x8)**:
    Every gate in mkMux4x8 drives a unique, non-overlapping output wire. -/
theorem mux4x8_nodup_drivers :
    ((mkMux4x8).gates.map Gate.output).Nodup := by
  native_decide

/-- **Theorem (L2 Driver Uniqueness Invariant - 4x32)**:
    Every gate in mkMux4x32 drives a unique, non-overlapping output wire. -/
theorem mux4x32_nodup_drivers :
    ((mkMux4x32).gates.map Gate.output).Nodup := by
  native_decide

/-- **Theorem (L2 Stateless / Zero DFF Invariant - 2x8)**:
    mkMux2x8 contains zero sequential flip-flops. -/
theorem mux2x8_no_dff : getDFFOutputs mkMux2x8 = [] := by
  native_decide

/-- **Theorem (L2 Stateless / Zero DFF Invariant - 4x8)**:
    mkMux4x8 contains zero sequential flip-flops. -/
theorem mux4x8_no_dff : getDFFOutputs mkMux4x8 = [] := by
  native_decide

/-- **Theorem (L2 Stateless / Zero DFF Invariant - 4x32)**:
    mkMux4x32 contains zero sequential flip-flops. -/
theorem mux4x32_no_dff : getDFFOutputs mkMux4x32 = [] := by
  native_decide

/-- **Theorem (L2 Combinational Memoryless Evaluation Invariant)**:
    In any multiplexer circuit with zero flip-flops, the combinational environment
    produced by evalCycleSequential is strictly a function of the cycle inputs,
    completely independent of register state history. -/
theorem mux_evalCycleSequential_memoryless (c : Circuit) (s1 s2 : State) (inp : Env)
    (h_no_dff : getDFFOutputs c = []) :
    (evalCycleSequential c s1 inp).2 = (evalCycleSequential c s2 inp).2 := by
  dsimp [evalCycleSequential]
  rw [h_no_dff]
  have h_env : mergeStateIntoEnv s1 inp [] = mergeStateIntoEnv s2 inp [] := by
    funext w
    simp [mergeStateIntoEnv]
  rw [h_env]

/-! ## L3: Information Flow Non-Interference & Temporal Refinement -/

/-- **Theorem (L3 Information Flow Non-Interference - sel=0)**:
    When sel is false, the multiplexer output depends strictly on in0.
    Arbitrary variation on in1 has zero impact on the evaluated output. -/
theorem mux2Bit_sel0_non_interference (pfx : String) (idx : Nat) (in0 in1 sel out : Wire)
    (env1 env2 : Env)
    (h_sel1 : env1 sel = false)
    (h_sel2 : env2 sel = false)
    (h_in0 : env1 in0 = env2 in0)
    (h_and0_and1 : (Wire.mk s!"and0_{pfx}_{idx}" == Wire.mk s!"and1_{pfx}_{idx}") = false)
    (h_in0_not  : (in0 == Wire.mk s!"not_sel_{pfx}_{idx}") = false)
    (h_in1_not  : (in1 == Wire.mk s!"not_sel_{pfx}_{idx}") = false)
    (h_in1_and0 : (in1 == Wire.mk s!"and0_{pfx}_{idx}") = false)
    (h_sel_not  : (sel == Wire.mk s!"not_sel_{pfx}_{idx}") = false)
    (h_sel_and0 : (sel == Wire.mk s!"and0_{pfx}_{idx}") = false) :
    evalGates (mkMux2Bit pfx idx in0 in1 sel out) env1 out =
    evalGates (mkMux2Bit pfx idx in0 in1 sel out) env2 out := by
  have e1 := evalGates_mux2Bit_result pfx idx in0 in1 sel out env1
    h_and0_and1 h_in0_not h_in1_not h_in1_and0 h_sel_not h_sel_and0
  have e2 := evalGates_mux2Bit_result pfx idx in0 in1 sel out env2
    h_and0_and1 h_in0_not h_in1_not h_in1_and0 h_sel_not h_sel_and0
  rw [e1, e2]
  dsimp [mux2]
  rw [h_sel1, h_sel2, h_in0]
  rfl

/-- **Theorem (L3 Information Flow Non-Interference - sel=1)**:
    When sel is true, the multiplexer output depends strictly on in1.
    Arbitrary variation on in0 has zero impact on the evaluated output. -/
theorem mux2Bit_sel1_non_interference (pfx : String) (idx : Nat) (in0 in1 sel out : Wire)
    (env1 env2 : Env)
    (h_sel1 : env1 sel = true)
    (h_sel2 : env2 sel = true)
    (h_in1 : env1 in1 = env2 in1)
    (h_and0_and1 : (Wire.mk s!"and0_{pfx}_{idx}" == Wire.mk s!"and1_{pfx}_{idx}") = false)
    (h_in0_not  : (in0 == Wire.mk s!"not_sel_{pfx}_{idx}") = false)
    (h_in1_not  : (in1 == Wire.mk s!"not_sel_{pfx}_{idx}") = false)
    (h_in1_and0 : (in1 == Wire.mk s!"and0_{pfx}_{idx}") = false)
    (h_sel_not  : (sel == Wire.mk s!"not_sel_{pfx}_{idx}") = false)
    (h_sel_and0 : (sel == Wire.mk s!"and0_{pfx}_{idx}") = false) :
    evalGates (mkMux2Bit pfx idx in0 in1 sel out) env1 out =
    evalGates (mkMux2Bit pfx idx in0 in1 sel out) env2 out := by
  have e1 := evalGates_mux2Bit_result pfx idx in0 in1 sel out env1
    h_and0_and1 h_in0_not h_in1_not h_in1_and0 h_sel_not h_sel_and0
  have e2 := evalGates_mux2Bit_result pfx idx in0 in1 sel out env2
    h_and0_and1 h_in0_not h_in1_not h_in1_and0 h_sel_not h_sel_and0
  rw [e1, e2]
  dsimp [mux2]
  rw [h_sel1, h_sel2, h_in1]
  rfl

/-- **Theorem (L3 Temporal Memoryless Trace Refinement)**:
    Across arbitrary execution traces, the combinational environment at cycle t
    is completely invariant under the multiplexer's internal state history:
    two traces with identical cycle inputs produce identical environments at cycle t,
    regardless of initial states or past execution sequences. -/
theorem mux_trace_temporal_memoryless
    (c : Circuit) (h_no_dff : getDFFOutputs c = [])
    (s0_1 s0_2 : State) (inputs : Nat → Env) (tr1 tr2 : Trace)
    (h_exec1 : Trace.IsExecutionOf c s0_1 inputs tr1)
    (h_exec2 : Trace.IsExecutionOf c s0_2 inputs tr2)
    (t : Nat) :
    tr1.envAt t = tr2.envAt t := by
  have h1 := (h_exec1.2 t).1
  have h2 := (h_exec2.2 t).1
  rw [h1, h2]
  exact mux_evalCycleSequential_memoryless c (tr1.stateAt t) (tr2.stateAt t) (inputs t) h_no_dff

/-- **Theorem (L3 Temporal Memoryless Refinement on mkMux4x8)**:
    Two arbitrary execution traces of mkMux4x8 under identical input streams
    evaluate to identical combinational environments at all cycles t,
    discharging the memoryless trace refinement property. -/
theorem mux4x8_trace_refinement
    (s0_1 s0_2 : State) (inputs : Nat → Env) (tr1 tr2 : Trace)
    (h_exec1 : Trace.IsExecutionOf mkMux4x8 s0_1 inputs tr1)
    (h_exec2 : Trace.IsExecutionOf mkMux4x8 s0_2 inputs tr2)
    (t : Nat) :
    tr1.envAt t = tr2.envAt t := by
  exact mux_trace_temporal_memoryless mkMux4x8 mux4x8_no_dff s0_1 s0_2 inputs tr1 tr2 h_exec1 h_exec2 t

end Shoumei.Circuits.Combinational
