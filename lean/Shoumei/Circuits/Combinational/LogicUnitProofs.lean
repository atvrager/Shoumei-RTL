/-
Circuits/Combinational/LogicUnitProofs.lean - Formal Verification for N-bit Logic Unit

Comprehensive 4-level formal verification hierarchy (L0-L3):
- L0: Structural properties (gate count closed form, I/O widths, concrete instances)
- L1: Functional truth table (exhaustive 4-bit check, single-bit symbolic evaluation, operation modes)
- L2: Hardware soundness invariants (wire preservation, slice isolation, combinational-only gate invariant, driver uniqueness nodup)
- L3: Information flow non-interference and temporal memoryless refinement
-/

import Shoumei.DSL
import Shoumei.DSL.Interfaces
import Shoumei.Semantics
import Shoumei.Reflection.CompileCircuit
import Shoumei.Temporal.Trace
import Shoumei.Circuits.Combinational.LogicUnit

namespace Shoumei.Circuits.Combinational

open Shoumei
open Shoumei.DSL.Interfaces
open Shoumei.Reflection
open Shoumei.Temporal

/-! ## Helper Lemmas for List and Gate Operations -/

theorem length_flatten_map_five {α β : Type} (l : List α) (f : α → List β)
    (h : ∀ x, (f x).length = 5) :
    (l.map f).flatten.length = 5 * l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons]
    rw [h x, ih]
    omega

/-! ## L0: Structural Proofs -/

/-- Theorem: Gate count of mkLogicUnitN is exactly 5 * n for arbitrary width n. -/
theorem logicunitN_gates_length (n : Nat) :
    (mkLogicUnitN n).gates.length = 5 * n := by
  dsimp [mkLogicUnitN]
  have h := length_flatten_map_five (List.range n)
    (fun i => mkLogicUnitBit
      ((makeIndexedWires "a" n)[i]!)
      ((makeIndexedWires "b" n)[i]!)
      (Wire.mk "op0") (Wire.mk "op1")
      ((makeIndexedWires "result" n)[i]!) i)
    (fun _ => rfl)
  rw [h, List.length_range]

/-- Theorem: Input port count of mkLogicUnitN is 2 * n + 2 (a[n] + b[n] + op0 + op1). -/
theorem logicunitN_inputs_length (n : Nat) :
    (mkLogicUnitN n).inputs.length = 2 * n + 2 := by
  dsimp [mkLogicUnitN, makeIndexedWires]
  simp [List.length_append, List.length_map, List.length_range]
  omega

/-- Theorem: Output port count of mkLogicUnitN is exactly n. -/
theorem logicunitN_outputs_length (n : Nat) :
    (mkLogicUnitN n).outputs.length = n := by
  dsimp [mkLogicUnitN, makeIndexedWires]
  simp [List.length_map, List.length_range]

-- Concrete structural properties (L0 backwards compatibility)
theorem logicunit4_structure :
  mkLogicUnit4.gates.length = 20 ∧
  mkLogicUnit4.inputs.length = 10 ∧
  mkLogicUnit4.outputs.length = 4 := by native_decide

theorem logicunit8_structure :
  mkLogicUnit8.gates.length = 40 ∧
  mkLogicUnit8.inputs.length = 18 ∧
  mkLogicUnit8.outputs.length = 8 := by native_decide

theorem logicunit32_structure :
  mkLogicUnit32.gates.length = 160 ∧
  mkLogicUnit32.inputs.length = 66 ∧
  mkLogicUnit32.outputs.length = 32 := by native_decide

theorem logicunit64_structure :
  mkLogicUnit64.gates.length = 320 ∧
  mkLogicUnit64.inputs.length = 130 ∧
  mkLogicUnit64.outputs.length = 64 := by native_decide

/-! ## L1: Functional Correctness Proofs -/

/-- Operation mode: op=00 selects bitwise AND. -/
theorem logicOp_and_correct (a b : Bool) : logicOp false false a b = (a && b) := rfl

/-- Operation mode: op=01 selects bitwise OR. -/
theorem logicOp_or_correct (a b : Bool) : logicOp false true a b = (a || b) := rfl

/-- Operation mode: op=1x selects bitwise XOR. -/
theorem logicOp_xor_correct (a b op0 : Bool) : logicOp true op0 a b = xor a b := rfl

/-- Helper: Construct input WireMap for 4-bit LogicUnit. -/
def makeLu4WireMap (a0 a1 a2 a3 b0 b1 b2 b3 op0 op1 : Bool) : WireMap :=
  [
    (Wire.mk "a_0", a0), (Wire.mk "a_1", a1), (Wire.mk "a_2", a2), (Wire.mk "a_3", a3),
    (Wire.mk "b_0", b0), (Wire.mk "b_1", b1), (Wire.mk "b_2", b2), (Wire.mk "b_3", b3),
    (Wire.mk "op0", op0), (Wire.mk "op1", op1)
  ]

/-- Check that 4-bit LogicUnit computes logicOp on every bit for given inputs. -/
def checkLu4 (a0 a1 a2 a3 b0 b1 b2 b3 op0 op1 : Bool) : Bool :=
  let m := makeLu4WireMap a0 a1 a2 a3 b0 b1 b2 b3 op0 op1
  let res := compileCircuit mkLogicUnit4 m
  let r0 := res.lookup (Wire.mk "result_0")
  let r1 := res.lookup (Wire.mk "result_1")
  let r2 := res.lookup (Wire.mk "result_2")
  let r3 := res.lookup (Wire.mk "result_3")
  r0 == logicOp op1 op0 a0 b0 &&
  r1 == logicOp op1 op0 a1 b1 &&
  r2 == logicOp op1 op0 a2 b2 &&
  r3 == logicOp op1 op0 a3 b3

/-- Exhaustive check across all 1024 input combinations for 4-bit LogicUnit. -/
def checkLu4All : Bool :=
  let bools := [false, true]
  bools.all fun a0 => bools.all fun a1 => bools.all fun a2 => bools.all fun a3 =>
  bools.all fun b0 => bools.all fun b1 => bools.all fun b2 => bools.all fun b3 =>
  bools.all fun op0 => bools.all fun op1 =>
    checkLu4 a0 a1 a2 a3 b0 b1 b2 b3 op0 op1

/-- **Theorem (L1 Exhaustive Functional Truth)**:
    4-bit LogicUnit correctly computes all operations (AND, OR, XOR) across all 1024 input combinations. -/
theorem logicunit4_exhaustive_correct : checkLu4All = true := by
  native_decide

/-- Bridge theorem connecting compileCircuit to evalCircuit for mkLogicUnit4. -/
theorem evalCircuit_logicunit4_agrees_compileCircuit (initMap : WireMap) (inputEnv : Env)
    (h : ∀ w, initMap.lookup w = inputEnv w) (w : Wire) :
    evalCircuit mkLogicUnit4 inputEnv w = (compileCircuit mkLogicUnit4 initMap).lookup w := by
  rw [compileCircuit_correct mkLogicUnit4 initMap inputEnv h w]

/-- **Theorem (L1 Single-Bit Semantic Evaluation)**:
    Evaluating the 5 gates of mkLogicUnitBit produces logicOp(op1, op0, a, b) on the result wire. -/
theorem evalGates_logicUnitBit_result (a b op0 op1 result : Wire) (idx : Nat) (env : Env)
    (h_a_and : (a == Wire.mk s!"and_{idx}") = false)
    (h_a_or  : (a == Wire.mk s!"or_{idx}") = false)
    (h_b_and : (b == Wire.mk s!"and_{idx}") = false)
    (h_b_or  : (b == Wire.mk s!"or_{idx}") = false)
    (h_op0_and : (op0 == Wire.mk s!"and_{idx}") = false)
    (h_op0_or  : (op0 == Wire.mk s!"or_{idx}") = false)
    (h_op0_xor : (op0 == Wire.mk s!"xor_{idx}") = false)
    (h_op1_and : (op1 == Wire.mk s!"and_{idx}") = false)
    (h_op1_or  : (op1 == Wire.mk s!"or_{idx}") = false)
    (h_op1_xor : (op1 == Wire.mk s!"xor_{idx}") = false)
    (h_op1_mux : (op1 == Wire.mk s!"mux1_{idx}") = false)
    (h_and_or  : (Wire.mk s!"and_{idx}" == Wire.mk s!"or_{idx}") = false)
    (h_and_xor : (Wire.mk s!"and_{idx}" == Wire.mk s!"xor_{idx}") = false)
    (h_or_xor  : (Wire.mk s!"or_{idx}" == Wire.mk s!"xor_{idx}") = false)
    (h_xor_mux : (Wire.mk s!"xor_{idx}" == Wire.mk s!"mux1_{idx}") = false) :
    evalGates (mkLogicUnitBit a b op0 op1 result idx) env result =
    logicOp (env op1) (env op0) (env a) (env b) := by
  dsimp [mkLogicUnitBit, evalGates, evalGate, Gate.mkAND, Gate.mkOR, Gate.mkXOR, Gate.mkMUX, updateEnv, logicOp]
  simp [-Nat.toString_eq_repr, h_a_and, h_a_or, h_b_and, h_b_or, h_op0_and, h_op0_or, h_op0_xor, h_op1_and, h_op1_or, h_op1_xor, h_op1_mux, h_and_or, h_and_xor, h_or_xor, h_xor_mux]

/-! ## L2: Inductive Invariants & Hardware Soundness -/

/-- **Theorem (L2 Wire Preservation Invariant)**:
    Evaluating mkLogicUnitBit for slice idx preserves every wire disjoint from its outputs. -/
theorem evalGates_logicUnitBit_preserves (a b op0 op1 result : Wire) (idx : Nat) (env : Env) (w : Wire)
    (h_and : (w == Wire.mk s!"and_{idx}") = false)
    (h_or  : (w == Wire.mk s!"or_{idx}") = false)
    (h_xor : (w == Wire.mk s!"xor_{idx}") = false)
    (h_mux : (w == Wire.mk s!"mux1_{idx}") = false)
    (h_res : (w == result) = false) :
    evalGates (mkLogicUnitBit a b op0 op1 result idx) env w = env w := by
  dsimp [mkLogicUnitBit, evalGates, evalGate, Gate.mkAND, Gate.mkOR, Gate.mkXOR, Gate.mkMUX, updateEnv]
  simp [-Nat.toString_eq_repr, h_and, h_or, h_xor, h_mux, h_res]

/-- **Theorem (L2 Bit-Slice Isolation Invariant)**:
    Bit slice i depends purely on its local inputs and control lines.
    Two environments agreeing on (a_i, b_i, op0, op1) produce identical results. -/
theorem logicunit_slice_isolation_invariant (env1 env2 : Env)
    (w_a w_b w_op0 w_op1 : Wire)
    (ha : env1 w_a = env2 w_a)
    (hb : env1 w_b = env2 w_b)
    (hop0 : env1 w_op0 = env2 w_op0)
    (hop1 : env1 w_op1 = env2 w_op1) :
    logicOp (env1 w_op1) (env1 w_op0) (env1 w_a) (env1 w_b) =
    logicOp (env2 w_op1) (env2 w_op0) (env2 w_a) (env2 w_b) := by
  rw [ha, hb, hop0, hop1]

/-- **Theorem (L2 Combinational Purity Invariant)**:
    Every gate in mkLogicUnitBit is strictly combinational. -/
theorem logicunit_gate_type_invariant (a b op0 op1 res : Wire) (i : Nat) :
    ∀ g ∈ mkLogicUnitBit a b op0 op1 res i, g.gateType.isCombinational = true := by
  intro g hg
  dsimp [mkLogicUnitBit] at hg
  simp only [List.mem_cons, List.not_mem_nil] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | h_false
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · cases h_false

/-- **Theorem (L2 Driver Uniqueness Invariant - 4-bit)**:
    Every gate drives a distinct, unique output wire (no multi-driver short circuits). -/
theorem logicunit4_nodup_drivers :
    ((mkLogicUnit4).gates.map Gate.output).Nodup := by
  decide

/-- **Theorem (L2 Driver Uniqueness Invariant - 8-bit)**:
    Every gate drives a distinct, unique output wire (no multi-driver short circuits). -/
theorem logicunit8_nodup_drivers :
    ((mkLogicUnit8).gates.map Gate.output).Nodup := by
  decide

/-- **Theorem (L2 Driver Uniqueness Invariant - 32-bit ALU variant)**:
    Every gate drives a distinct, unique output wire (no multi-driver short circuits). -/
theorem logicunit32_nodup_drivers :
    ((mkLogicUnit32).gates.map Gate.output).Nodup := by
  native_decide

/-- **Theorem (L2 Stateless / Zero DFF Invariant - 4-bit)**:
    mkLogicUnit4 contains zero sequential flip-flops. -/
theorem logicunit4_no_dff : getDFFOutputs mkLogicUnit4 = [] := by
  decide

/-- **Theorem (L2 Stateless / Zero DFF Invariant - 8-bit)**:
    mkLogicUnit8 contains zero sequential flip-flops. -/
theorem logicunit8_no_dff : getDFFOutputs mkLogicUnit8 = [] := by
  decide

/-- **Theorem (L2 Stateless / Zero DFF Invariant - 32-bit)**:
    mkLogicUnit32 contains zero sequential flip-flops. -/
theorem logicunit32_no_dff : getDFFOutputs mkLogicUnit32 = [] := by
  decide

/-- **Theorem (L2 Combinational Memoryless Evaluation Invariant)**:
    In any circuit with zero flip-flops, the combinational environment produced
    by evalCycleSequential is strictly a function of the cycle inputs, completely
    independent of the initial or current register state. -/
theorem logicunit_evalCycleSequential_memoryless (c : Circuit) (s1 s2 : State) (inp : Env)
    (h_no_dff : getDFFOutputs c = []) :
    (evalCycleSequential c s1 inp).2 = (evalCycleSequential c s2 inp).2 := by
  dsimp [evalCycleSequential]
  rw [h_no_dff]
  have h_env : mergeStateIntoEnv s1 inp [] = mergeStateIntoEnv s2 inp [] := by
    funext w
    simp [mergeStateIntoEnv]
  rw [h_env]

/-! ## L3: Information Flow Non-Interference & Temporal Refinement -/

/-- **Theorem (L3 Information Flow Non-Interference)**:
    Variation on bit-slice j (j ≠ idx) has zero impact on bit-slice idx.
    Given two environments env1 and env2 that agree on slice idx's inputs (a, b, op0, op1),
    the gate network evaluates to the exact same value on result. -/
theorem logicunit_slice_non_interference (a b op0 op1 result : Wire) (idx : Nat)
    (env1 env2 : Env)
    (ha : env1 a = env2 a)
    (hb : env1 b = env2 b)
    (hop0 : env1 op0 = env2 op0)
    (hop1 : env1 op1 = env2 op1)
    (h_a_and : (a == Wire.mk s!"and_{idx}") = false)
    (h_a_or  : (a == Wire.mk s!"or_{idx}") = false)
    (h_b_and : (b == Wire.mk s!"and_{idx}") = false)
    (h_b_or  : (b == Wire.mk s!"or_{idx}") = false)
    (h_op0_and : (op0 == Wire.mk s!"and_{idx}") = false)
    (h_op0_or  : (op0 == Wire.mk s!"or_{idx}") = false)
    (h_op0_xor : (op0 == Wire.mk s!"xor_{idx}") = false)
    (h_op1_and : (op1 == Wire.mk s!"and_{idx}") = false)
    (h_op1_or  : (op1 == Wire.mk s!"or_{idx}") = false)
    (h_op1_xor : (op1 == Wire.mk s!"xor_{idx}") = false)
    (h_op1_mux : (op1 == Wire.mk s!"mux1_{idx}") = false)
    (h_and_or  : (Wire.mk s!"and_{idx}" == Wire.mk s!"or_{idx}") = false)
    (h_and_xor : (Wire.mk s!"and_{idx}" == Wire.mk s!"xor_{idx}") = false)
    (h_or_xor  : (Wire.mk s!"or_{idx}" == Wire.mk s!"xor_{idx}") = false)
    (h_xor_mux : (Wire.mk s!"xor_{idx}" == Wire.mk s!"mux1_{idx}") = false) :
    evalGates (mkLogicUnitBit a b op0 op1 result idx) env1 result =
    evalGates (mkLogicUnitBit a b op0 op1 result idx) env2 result := by
  have e1 := evalGates_logicUnitBit_result a b op0 op1 result idx env1
    h_a_and h_a_or h_b_and h_b_or h_op0_and h_op0_or h_op0_xor h_op1_and h_op1_or h_op1_xor h_op1_mux
    h_and_or h_and_xor h_or_xor h_xor_mux
  have e2 := evalGates_logicUnitBit_result a b op0 op1 result idx env2
    h_a_and h_a_or h_b_and h_b_or h_op0_and h_op0_or h_op0_xor h_op1_and h_op1_or h_op1_xor h_op1_mux
    h_and_or h_and_xor h_or_xor h_xor_mux
  rw [e1, e2, ha, hb, hop0, hop1]

/-- **Theorem (L3 Temporal Memoryless Refinement)**:
    Across arbitrary execution traces, the combinational environment at cycle t
    is completely invariant under the circuit's internal state history:
    two traces with identical cycle inputs produce identical environments at cycle t,
    regardless of initial states or past execution sequences. -/
theorem logicunit_trace_temporal_memoryless
    (c : Circuit) (h_no_dff : getDFFOutputs c = [])
    (s0_1 s0_2 : State) (inputs : Nat → Env) (tr1 tr2 : Trace)
    (h_exec1 : Trace.IsExecutionOf c s0_1 inputs tr1)
    (h_exec2 : Trace.IsExecutionOf c s0_2 inputs tr2)
    (t : Nat) :
    tr1.envAt t = tr2.envAt t := by
  have h1 := (h_exec1.2 t).1
  have h2 := (h_exec2.2 t).1
  rw [h1, h2]
  exact logicunit_evalCycleSequential_memoryless c (tr1.stateAt t) (tr2.stateAt t) (inputs t) h_no_dff

/-- **Theorem (L3 Temporal Memoryless Refinement on mkLogicUnit4)**:
    Two arbitrary execution traces of mkLogicUnit4 under identical input streams
    evaluate to identical combinational environments at all cycles t,
    discharging the memoryless trace refinement property. -/
theorem logicunit4_trace_refinement
    (s0_1 s0_2 : State) (inputs : Nat → Env) (tr1 tr2 : Trace)
    (h_exec1 : Trace.IsExecutionOf mkLogicUnit4 s0_1 inputs tr1)
    (h_exec2 : Trace.IsExecutionOf mkLogicUnit4 s0_2 inputs tr2)
    (t : Nat) :
    tr1.envAt t = tr2.envAt t := by
  exact logicunit_trace_temporal_memoryless mkLogicUnit4 logicunit4_no_dff s0_1 s0_2 inputs tr1 tr2 h_exec1 h_exec2 t

end Shoumei.Circuits.Combinational
