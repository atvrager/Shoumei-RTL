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
import Shoumei.Reflection.SymbolicCompile
import Shoumei.Reflection.BitVecPacking

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

def mux4x32SymInit (s0 s1 : Bool) : SymWireMap :=
  (List.range 32).map (fun i => (Wire.mk s!"in0_{i}", BoolExpr.var i)) ++
  (List.range 32).map (fun i => (Wire.mk s!"in1_{i}", BoolExpr.var (32 + i))) ++
  (List.range 32).map (fun i => (Wire.mk s!"in2_{i}", BoolExpr.var (64 + i))) ++
  (List.range 32).map (fun i => (Wire.mk s!"in3_{i}", BoolExpr.var (96 + i))) ++
  [(Wire.mk "sel_0", BoolExpr.lit s0), (Wire.mk "sel_1", BoolExpr.lit s1)]

def mux4x32SymCompiled (s0 s1 : Bool) : SymWireMap :=
  symCompileGates mkMux4x32.gates (mux4x32SymInit s0 s1)

def mux4x32SymResult (s0 s1 : Bool) (i : Nat) : BoolExpr :=
  SymWireMap.lookup (mux4x32SymCompiled s0 s1) (Wire.mk s!"out_{i}")

def checkMuxSymMode (compiled : SymWireMap) (base : Nat) : Bool :=
  (List.range 32).all fun i =>
    decide ((SymWireMap.lookup compiled (Wire.mk s!"out_{i}")).constFold = .var (base + i))

theorem checkMuxSymMode_iff (compiled : SymWireMap) (base : Nat)
    (h : checkMuxSymMode compiled base = true) (i : Nat) (hi : i < 32) :
    (SymWireMap.lookup compiled (Wire.mk s!"out_{i}")).constFold = .var (base + i) := by
  dsimp [checkMuxSymMode] at h
  have h1 := (List.all_eq_true.mp h) i (List.mem_range.mpr hi)
  exact of_decide_eq_true h1

theorem mux4x32_sym_check_00 : checkMuxSymMode (mux4x32SymCompiled false false) 0 = true := by
  native_decide

theorem mux4x32_sym_check_10 : checkMuxSymMode (mux4x32SymCompiled true false) 32 = true := by
  native_decide

theorem mux4x32_sym_check_01 : checkMuxSymMode (mux4x32SymCompiled false true) 64 = true := by
  native_decide

theorem mux4x32_sym_check_11 : checkMuxSymMode (mux4x32SymCompiled true true) 96 = true := by
  native_decide

theorem mux4x32_sym_00 (i : Fin 32) :
    (mux4x32SymResult false false i.val).constFold = .var i.val := by
  have h := checkMuxSymMode_iff _ 0 mux4x32_sym_check_00 i.val i.isLt
  simpa [mux4x32SymResult] using h

theorem mux4x32_sym_10 (i : Fin 32) :
    (mux4x32SymResult true false i.val).constFold = .var (32 + i.val) :=
  checkMuxSymMode_iff _ 32 mux4x32_sym_check_10 i.val i.isLt

theorem mux4x32_sym_01 (i : Fin 32) :
    (mux4x32SymResult false true i.val).constFold = .var (64 + i.val) :=
  checkMuxSymMode_iff _ 64 mux4x32_sym_check_01 i.val i.isLt

theorem mux4x32_sym_11 (i : Fin 32) :
    (mux4x32SymResult true true i.val).constFold = .var (96 + i.val) :=
  checkMuxSymMode_iff _ 96 mux4x32_sym_check_11 i.val i.isLt

/-! ## Symbolic-to-Concrete Bridge for Mux4x32 -/

def makeMux4x32InitMap (in0 in1 in2 in3 : BitVec 32) (sel0 sel1 : Bool) : WireMap :=
  bitVecToBindings "in0" 32 in0 ++
  bitVecToBindings "in1" 32 in1 ++
  bitVecToBindings "in2" 32 in2 ++
  bitVecToBindings "in3" 32 in3 ++
  [(Wire.mk "sel_0", sel0), (Wire.mk "sel_1", sel1)]

def mux4x32Assign (in0 in1 in2 in3 : BitVec 32) : Nat → Bool :=
  fun i =>
    if i < 32 then in0.getLsbD i
    else if i < 64 then in1.getLsbD (i - 32)
    else if i < 96 then in2.getLsbD (i - 64)
    else in3.getLsbD (i - 96)

private theorem sym_lookup_eval_list (xs : List (Wire × BoolExpr))
    (assign : Nat → Bool) (w : Wire) :
    (SymWireMap.lookup xs w).eval assign =
    WireMap.lookup (xs.map (fun p => (p.1, p.2.eval assign))) w := by
  induction xs with
  | nil =>
    simp [SymWireMap.lookup, WireMap.lookup, List.find?, BoolExpr.eval]
  | cons hd tl ih =>
    obtain ⟨w', e⟩ := hd
    unfold SymWireMap.lookup WireMap.lookup
    simp only [List.map, List.find?]
    cases hbeq : (w' == w) with
    | true => simp
    | false =>
      exact ih

private theorem sym_init_chunk_eq (wfn : Nat → Wire) (pfx : String) (offset : Nat)
    (assign : Nat → Bool) (bv : BitVec 32)
    (h : ∀ i < 32, assign (offset + i) = bv.getLsbD i)
    (hw : ∀ i < 32, wfn i = Wire.mk s!"{pfx}_{i}" := by intros; rfl) :
    ((List.range 32).map (fun i => (wfn i, BoolExpr.var (offset + i)))).map
      (fun p => (p.1, p.2.eval assign)) =
    bitVecToBindings pfx 32 bv := by
  simp only [bitVecToBindings, List.map_map]
  rw [List.map_eq_map_iff]
  intro i hi
  have hi' := List.mem_range.mp hi
  simp [BoolExpr.eval, hw i hi', h i hi']

private theorem sym_init_chunk0_eq (wfn : Nat → Wire) (pfx : String)
    (assign : Nat → Bool) (bv : BitVec 32)
    (h : ∀ i < 32, assign i = bv.getLsbD i)
    (hw : ∀ i < 32, wfn i = Wire.mk s!"{pfx}_{i}" := by intros; rfl) :
    ((List.range 32).map (fun i => (wfn i, BoolExpr.var i))).map
      (fun p => (p.1, p.2.eval assign)) =
    bitVecToBindings pfx 32 bv := by
  simp only [bitVecToBindings, List.map_map]
  rw [List.map_eq_map_iff]
  intro i hi
  have hi' := List.mem_range.mp hi
  simp [BoolExpr.eval, hw i hi', h i hi']

theorem mux4x32SymInit_correct (in0 in1 in2 in3 : BitVec 32) (sel0 sel1 : Bool) :
    ∀ w, (SymWireMap.lookup (mux4x32SymInit sel0 sel1) w).eval (mux4x32Assign in0 in1 in2 in3) =
         WireMap.lookup (makeMux4x32InitMap in0 in1 in2 in3 sel0 sel1) w := by
  intro w
  rw [sym_lookup_eval_list]
  suffices h : (mux4x32SymInit sel0 sel1).map (fun p => (p.1, p.2.eval (mux4x32Assign in0 in1 in2 in3))) =
               makeMux4x32InitMap in0 in1 in2 in3 sel0 sel1 by rw [h]
  dsimp only [mux4x32SymInit, makeMux4x32InitMap]
  simp only [List.map_append]
  rw [sym_init_chunk0_eq _ "in0" _ in0 (fun i hi => by simp [mux4x32Assign, hi]),
      sym_init_chunk_eq _ "in1" 32 _ in1 (fun i hi => by
        simp [mux4x32Assign, show ¬(32 + i < 32) by omega, show 32 + i < 64 by omega, show 32 + i - 32 = i by omega]),
      sym_init_chunk_eq _ "in2" 64 _ in2 (fun i hi => by
        simp [mux4x32Assign, show ¬(64 + i < 32) by omega, show ¬(64 + i < 64) by omega, show 64 + i < 96 by omega, show 64 + i - 64 = i by omega]),
      sym_init_chunk_eq _ "in3" 96 _ in3 (fun i hi => by
        simp [mux4x32Assign, show ¬(96 + i < 32) by omega, show ¬(96 + i < 64) by omega, show ¬(96 + i < 96) by omega, show 96 + i - 96 = i by omega])]
  rfl

def readSymResultAsNat (assign : Nat → Bool) (getExpr : Nat → BoolExpr) : Nat → Nat
  | 0 => 0
  | n + 1 =>
    let bit := if (getExpr n).eval assign then 1 else 0
    bit * (2 ^ n) + readSymResultAsNat assign getExpr n

theorem readSymResultAsNat_correct (assign : Nat → Bool) (m : WireMap)
    (name : String) (getExpr : Nat → BoolExpr)
    (h : ∀ i, (getExpr i).eval assign = m.lookup (Wire.mk s!"{name}_{i}"))
    (n : Nat) :
    readSymResultAsNat assign getExpr n = readWiresAsNatMap m name n := by
  induction n with
  | zero => simp [readSymResultAsNat, readWiresAsNatMap]
  | succ k ih =>
    simp only [readSymResultAsNat, readWiresAsNatMap]
    rw [h k, ih]

private theorem readSymResultAsNat_bound (assign : Nat → Bool) (f : Nat → BoolExpr) (n : Nat) :
    readSymResultAsNat assign f n < 2 ^ n := by
  induction n with
  | zero => simp [readSymResultAsNat]
  | succ k ih => simp only [readSymResultAsNat]; split <;> simp <;> omega

private theorem readSymResultAsNat_testBit (assign : Nat → Bool) (f : Nat → BoolExpr)
    (n i : Nat) (hi : i < n) :
    (readSymResultAsNat assign f n).testBit i = (f i).eval assign := by
  induction n with
  | zero => omega
  | succ k ih =>
    simp only [readSymResultAsNat]
    have hbound := readSymResultAsNat_bound assign f k
    by_cases hik : i = k
    · subst hik
      split <;> rename_i heval <;> simp
      · rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hbound]; simp [heval]
      · rw [Nat.testBit_lt_two_pow hbound]; simp [heval]
    · have hik' : i < k := by omega
      split <;> simp
      · rw [Nat.testBit_two_pow_add_gt (by omega)]; exact ih hik'
      · exact ih hik'

def evalMux4x32 (in0 in1 in2 in3 : BitVec 32) (sel0 sel1 : Bool) : BitVec 32 :=
  readResultBitVecMap (compileCircuit mkMux4x32 (makeMux4x32InitMap in0 in1 in2 in3 sel0 sel1)) "out" 32

def mux4x32Spec (in0 in1 in2 in3 : BitVec 32) (sel0 sel1 : Bool) : BitVec 32 :=
  match sel1, sel0 with
  | false, false => in0
  | false, true  => in1
  | true,  false => in2
  | true,  true  => in3

theorem symCompileCircuit_correct (c : Circuit) (sm : SymWireMap) (m : WireMap)
    (assign : Nat → Bool)
    (h : ∀ w, (sm.lookup w).eval assign = m.lookup w) :
    ∀ w, ((symCompileGates c.gates sm).lookup w).eval assign =
         (compileCircuit c m).lookup w := by
  intro w
  simp only [compileCircuit]
  exact symCompileGates_correct c.gates sm m assign h w

theorem evalMux4x32_eq_sym (in0 in1 in2 in3 : BitVec 32) (sel0 sel1 : Bool) :
    evalMux4x32 in0 in1 in2 in3 sel0 sel1 =
    BitVec.ofNat 32 (readSymResultAsNat (mux4x32Assign in0 in1 in2 in3) (fun i => mux4x32SymResult sel0 sel1 i) 32) := by
  dsimp [evalMux4x32, readResultBitVecMap]
  apply congrArg (BitVec.ofNat 32)
  symm
  apply readSymResultAsNat_correct
  intro i
  have h_comp := symCompileCircuit_correct mkMux4x32 (mux4x32SymInit sel0 sel1)
    (makeMux4x32InitMap in0 in1 in2 in3 sel0 sel1) (mux4x32Assign in0 in1 in2 in3)
    (mux4x32SymInit_correct in0 in1 in2 in3 sel0 sel1)
    (Wire.mk s!"out_{i}")
  exact h_comp

theorem evalMux4x32_correct (in0 in1 in2 in3 : BitVec 32) (sel0 sel1 : Bool) :
    evalMux4x32 in0 in1 in2 in3 sel0 sel1 = mux4x32Spec in0 in1 in2 in3 sel0 sel1 := by
  rw [evalMux4x32_eq_sym]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_ofNat, readSymResultAsNat_testBit _ _ 32 i hi]
  simp only [hi, decide_true, Bool.true_and]
  dsimp [mux4x32Spec]
  cases sel1 <;> cases sel0
  · -- false, false -> in0
    have hcf := mux4x32_sym_00 ⟨i, hi⟩
    rw [← BoolExpr.constFold_correct, hcf]
    simp [BoolExpr.eval, mux4x32Assign, hi]
  · -- true, false -> in1 (sel0=true, sel1=false)
    have hcf := mux4x32_sym_10 ⟨i, hi⟩
    rw [← BoolExpr.constFold_correct, hcf]
    simp [BoolExpr.eval, mux4x32Assign, hi,
          show ¬(32 + i < 32) from by omega,
          show 32 + i < 64 from by omega,
          show 32 + i - 32 = i from by omega]
  · -- false, true -> in2 (sel0=false, sel1=true)
    have hcf := mux4x32_sym_01 ⟨i, hi⟩
    rw [← BoolExpr.constFold_correct, hcf]
    simp [BoolExpr.eval, mux4x32Assign, hi,
          show ¬(64 + i < 32) from by omega,
          show ¬(64 + i < 64) from by omega,
          show 64 + i < 96 from by omega,
          show 64 + i - 64 = i from by omega]
  · -- true, true -> in3 (sel0=true, sel1=true)
    have hcf := mux4x32_sym_11 ⟨i, hi⟩
    rw [← BoolExpr.constFold_correct, hcf]
    simp [BoolExpr.eval, mux4x32Assign, hi,
          show ¬(96 + i < 32) from by omega,
          show ¬(96 + i < 64) from by omega,
          show ¬(96 + i < 96) from by omega,
          show 96 + i - 96 = i from by omega]

/-! ## Word-level Refinement for the Flat 8:1 Mux (Mux8x32) -/

/-- Word-level reference specification for an 8:1 multiplexer. -/
def mux8x32Spec (inputs : Fin 8 → BitVec 32) (sel0 sel1 sel2 : Bool) : BitVec 32 :=
  match sel2, sel1, sel0 with
  | false, false, false => inputs 0
  | false, false, true  => inputs 1
  | false, true,  false => inputs 2
  | false, true,  true  => inputs 3
  | true,  false, false => inputs 4
  | true,  false, true  => inputs 5
  | true,  true,  false => inputs 6
  | true,  true,  true  => inputs 7

def mux8x32SymInit (s0 s1 s2 : Bool) : SymWireMap :=
  (List.range 32).map (fun i => (Wire.mk s!"in0_{i}", BoolExpr.var i)) ++
  (List.range 32).map (fun i => (Wire.mk s!"in1_{i}", BoolExpr.var (32 + i))) ++
  (List.range 32).map (fun i => (Wire.mk s!"in2_{i}", BoolExpr.var (64 + i))) ++
  (List.range 32).map (fun i => (Wire.mk s!"in3_{i}", BoolExpr.var (96 + i))) ++
  (List.range 32).map (fun i => (Wire.mk s!"in4_{i}", BoolExpr.var (128 + i))) ++
  (List.range 32).map (fun i => (Wire.mk s!"in5_{i}", BoolExpr.var (160 + i))) ++
  (List.range 32).map (fun i => (Wire.mk s!"in6_{i}", BoolExpr.var (192 + i))) ++
  (List.range 32).map (fun i => (Wire.mk s!"in7_{i}", BoolExpr.var (224 + i))) ++
  [(Wire.mk "sel_0", BoolExpr.lit s0), (Wire.mk "sel_1", BoolExpr.lit s1), (Wire.mk "sel_2", BoolExpr.lit s2)]

def mux8x32SymCompiled (s0 s1 s2 : Bool) : SymWireMap :=
  symCompileGates mkMux8x32.gates (mux8x32SymInit s0 s1 s2)

def mux8x32SymResult (s0 s1 s2 : Bool) (i : Nat) : BoolExpr :=
  SymWireMap.lookup (mux8x32SymCompiled s0 s1 s2) (Wire.mk s!"out_{i}")

theorem mux8x32_sym_check_000 : checkMuxSymMode (mux8x32SymCompiled false false false) 0 = true := by
  native_decide

theorem mux8x32_sym_check_100 : checkMuxSymMode (mux8x32SymCompiled true false false) 32 = true := by
  native_decide

theorem mux8x32_sym_check_010 : checkMuxSymMode (mux8x32SymCompiled false true false) 64 = true := by
  native_decide

theorem mux8x32_sym_check_110 : checkMuxSymMode (mux8x32SymCompiled true true false) 96 = true := by
  native_decide

theorem mux8x32_sym_check_001 : checkMuxSymMode (mux8x32SymCompiled false false true) 128 = true := by
  native_decide

theorem mux8x32_sym_check_101 : checkMuxSymMode (mux8x32SymCompiled true false true) 160 = true := by
  native_decide

theorem mux8x32_sym_check_011 : checkMuxSymMode (mux8x32SymCompiled false true true) 192 = true := by
  native_decide

theorem mux8x32_sym_check_111 : checkMuxSymMode (mux8x32SymCompiled true true true) 224 = true := by
  native_decide

theorem mux8x32_sym_000 (i : Fin 32) :
    (mux8x32SymResult false false false i.val).constFold = .var i.val := by
  have h := checkMuxSymMode_iff _ 0 mux8x32_sym_check_000 i.val i.isLt
  simpa [mux8x32SymResult] using h

theorem mux8x32_sym_100 (i : Fin 32) :
    (mux8x32SymResult true false false i.val).constFold = .var (32 + i.val) :=
  checkMuxSymMode_iff _ 32 mux8x32_sym_check_100 i.val i.isLt

theorem mux8x32_sym_010 (i : Fin 32) :
    (mux8x32SymResult false true false i.val).constFold = .var (64 + i.val) :=
  checkMuxSymMode_iff _ 64 mux8x32_sym_check_010 i.val i.isLt

theorem mux8x32_sym_110 (i : Fin 32) :
    (mux8x32SymResult true true false i.val).constFold = .var (96 + i.val) :=
  checkMuxSymMode_iff _ 96 mux8x32_sym_check_110 i.val i.isLt

theorem mux8x32_sym_001 (i : Fin 32) :
    (mux8x32SymResult false false true i.val).constFold = .var (128 + i.val) :=
  checkMuxSymMode_iff _ 128 mux8x32_sym_check_001 i.val i.isLt

theorem mux8x32_sym_101 (i : Fin 32) :
    (mux8x32SymResult true false true i.val).constFold = .var (160 + i.val) :=
  checkMuxSymMode_iff _ 160 mux8x32_sym_check_101 i.val i.isLt

theorem mux8x32_sym_011 (i : Fin 32) :
    (mux8x32SymResult false true true i.val).constFold = .var (192 + i.val) :=
  checkMuxSymMode_iff _ 192 mux8x32_sym_check_011 i.val i.isLt

theorem mux8x32_sym_111 (i : Fin 32) :
    (mux8x32SymResult true true true i.val).constFold = .var (224 + i.val) :=
  checkMuxSymMode_iff _ 224 mux8x32_sym_check_111 i.val i.isLt

def makeMux8x32InitMap (inputs : Fin 8 → BitVec 32) (sel0 sel1 sel2 : Bool) : WireMap :=
  bitVecToBindings "in0" 32 (inputs 0) ++
  bitVecToBindings "in1" 32 (inputs 1) ++
  bitVecToBindings "in2" 32 (inputs 2) ++
  bitVecToBindings "in3" 32 (inputs 3) ++
  bitVecToBindings "in4" 32 (inputs 4) ++
  bitVecToBindings "in5" 32 (inputs 5) ++
  bitVecToBindings "in6" 32 (inputs 6) ++
  bitVecToBindings "in7" 32 (inputs 7) ++
  [(Wire.mk "sel_0", sel0), (Wire.mk "sel_1", sel1), (Wire.mk "sel_2", sel2)]

def mux8x32Assign (inputs : Fin 8 → BitVec 32) : Nat → Bool :=
  fun i =>
    if i < 32 then (inputs 0).getLsbD i
    else if i < 64 then (inputs 1).getLsbD (i - 32)
    else if i < 96 then (inputs 2).getLsbD (i - 64)
    else if i < 128 then (inputs 3).getLsbD (i - 96)
    else if i < 160 then (inputs 4).getLsbD (i - 128)
    else if i < 192 then (inputs 5).getLsbD (i - 160)
    else if i < 224 then (inputs 6).getLsbD (i - 192)
    else (inputs 7).getLsbD (i - 224)

theorem mux8x32SymInit_correct (inputs : Fin 8 → BitVec 32) (sel0 sel1 sel2 : Bool) :
    ∀ w, (SymWireMap.lookup (mux8x32SymInit sel0 sel1 sel2) w).eval (mux8x32Assign inputs) =
         WireMap.lookup (makeMux8x32InitMap inputs sel0 sel1 sel2) w := by
  intro w
  rw [sym_lookup_eval_list]
  suffices h : (mux8x32SymInit sel0 sel1 sel2).map (fun p => (p.1, p.2.eval (mux8x32Assign inputs))) =
               makeMux8x32InitMap inputs sel0 sel1 sel2 by rw [h]
  dsimp only [mux8x32SymInit, makeMux8x32InitMap]
  simp only [List.map_append]
  rw [sym_init_chunk0_eq _ "in0" _ (inputs 0) (fun i hi => by simp [mux8x32Assign, hi]),
      sym_init_chunk_eq _ "in1" 32 _ (inputs 1) (fun i hi => by
        simp [mux8x32Assign, show ¬(32 + i < 32) by omega, show 32 + i < 64 by omega, show 32 + i - 32 = i by omega]),
      sym_init_chunk_eq _ "in2" 64 _ (inputs 2) (fun i hi => by
        simp [mux8x32Assign, show ¬(64 + i < 32) by omega, show ¬(64 + i < 64) by omega, show 64 + i < 96 by omega, show 64 + i - 64 = i by omega]),
      sym_init_chunk_eq _ "in3" 96 _ (inputs 3) (fun i hi => by
        simp [mux8x32Assign, show ¬(96 + i < 32) by omega, show ¬(96 + i < 64) by omega, show ¬(96 + i < 96) by omega, show 96 + i < 128 by omega, show 96 + i - 96 = i by omega]),
      sym_init_chunk_eq _ "in4" 128 _ (inputs 4) (fun i hi => by
        simp [mux8x32Assign, show ¬(128 + i < 32) by omega, show ¬(128 + i < 64) by omega, show ¬(128 + i < 96) by omega, show ¬(128 + i < 128) by omega, show 128 + i < 160 by omega, show 128 + i - 128 = i by omega]),
      sym_init_chunk_eq _ "in5" 160 _ (inputs 5) (fun i hi => by
        simp [mux8x32Assign, show ¬(160 + i < 32) by omega, show ¬(160 + i < 64) by omega, show ¬(160 + i < 96) by omega, show ¬(160 + i < 128) by omega, show ¬(160 + i < 160) by omega, show 160 + i < 192 by omega, show 160 + i - 160 = i by omega]),
      sym_init_chunk_eq _ "in6" 192 _ (inputs 6) (fun i hi => by
        simp [mux8x32Assign, show ¬(192 + i < 32) by omega, show ¬(192 + i < 64) by omega, show ¬(192 + i < 96) by omega, show ¬(192 + i < 128) by omega, show ¬(192 + i < 160) by omega, show ¬(192 + i < 192) by omega, show 192 + i < 224 by omega, show 192 + i - 192 = i by omega]),
      sym_init_chunk_eq _ "in7" 224 _ (inputs 7) (fun i hi => by
        simp [mux8x32Assign, show ¬(224 + i < 32) by omega, show ¬(224 + i < 64) by omega, show ¬(224 + i < 96) by omega, show ¬(224 + i < 128) by omega, show ¬(224 + i < 160) by omega, show ¬(224 + i < 192) by omega, show ¬(224 + i < 224) by omega, show 224 + i - 224 = i by omega])]
  rfl

def evalMux8x32 (inputs : Fin 8 → BitVec 32) (sel0 sel1 sel2 : Bool) : BitVec 32 :=
  readResultBitVecMap (compileCircuit mkMux8x32 (makeMux8x32InitMap inputs sel0 sel1 sel2)) "out" 32

theorem evalMux8x32_eq_sym (inputs : Fin 8 → BitVec 32) (sel0 sel1 sel2 : Bool) :
    evalMux8x32 inputs sel0 sel1 sel2 =
    BitVec.ofNat 32 (readSymResultAsNat (mux8x32Assign inputs) (fun i => mux8x32SymResult sel0 sel1 sel2 i) 32) := by
  dsimp [evalMux8x32, readResultBitVecMap]
  apply congrArg (BitVec.ofNat 32)
  symm
  apply readSymResultAsNat_correct
  intro i
  exact symCompileCircuit_correct mkMux8x32 (mux8x32SymInit sel0 sel1 sel2)
    (makeMux8x32InitMap inputs sel0 sel1 sel2) (mux8x32Assign inputs)
    (mux8x32SymInit_correct inputs sel0 sel1 sel2) (Wire.mk s!"out_{i}")

theorem evalMux8x32_correct (inputs : Fin 8 → BitVec 32) (sel0 sel1 sel2 : Bool) :
    evalMux8x32 inputs sel0 sel1 sel2 = mux8x32Spec inputs sel0 sel1 sel2 := by
  rw [evalMux8x32_eq_sym]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_ofNat, readSymResultAsNat_testBit _ _ 32 i hi]
  simp only [hi, decide_true, Bool.true_and]
  dsimp [mux8x32Spec]
  cases sel2 <;> cases sel1 <;> cases sel0
  · rw [← BoolExpr.constFold_correct, mux8x32_sym_000 ⟨i, hi⟩]
    simp [BoolExpr.eval, mux8x32Assign, hi]
  · rw [← BoolExpr.constFold_correct, mux8x32_sym_100 ⟨i, hi⟩]
    simp [BoolExpr.eval, mux8x32Assign, hi,
      show ¬(32 + i < 32) from by omega, show 32 + i < 64 from by omega,
      show 32 + i - 32 = i from by omega]
  · rw [← BoolExpr.constFold_correct, mux8x32_sym_010 ⟨i, hi⟩]
    simp [BoolExpr.eval, mux8x32Assign, hi,
      show ¬(64 + i < 32) from by omega, show ¬(64 + i < 64) from by omega,
      show 64 + i < 96 from by omega, show 64 + i - 64 = i from by omega]
  · rw [← BoolExpr.constFold_correct, mux8x32_sym_110 ⟨i, hi⟩]
    simp [BoolExpr.eval, mux8x32Assign, hi,
      show ¬(96 + i < 32) from by omega, show ¬(96 + i < 64) from by omega,
      show ¬(96 + i < 96) from by omega, show 96 + i < 128 from by omega,
      show 96 + i - 96 = i from by omega]
  · rw [← BoolExpr.constFold_correct, mux8x32_sym_001 ⟨i, hi⟩]
    simp [BoolExpr.eval, mux8x32Assign, hi,
      show ¬(128 + i < 32) from by omega, show ¬(128 + i < 64) from by omega,
      show ¬(128 + i < 96) from by omega, show ¬(128 + i < 128) from by omega,
      show 128 + i < 160 from by omega, show 128 + i - 128 = i from by omega]
  · rw [← BoolExpr.constFold_correct, mux8x32_sym_101 ⟨i, hi⟩]
    simp [BoolExpr.eval, mux8x32Assign, hi,
      show ¬(160 + i < 32) from by omega, show ¬(160 + i < 64) from by omega,
      show ¬(160 + i < 96) from by omega, show ¬(160 + i < 128) from by omega,
      show ¬(160 + i < 160) from by omega, show 160 + i < 192 from by omega,
      show 160 + i - 160 = i from by omega]
  · rw [← BoolExpr.constFold_correct, mux8x32_sym_011 ⟨i, hi⟩]
    simp [BoolExpr.eval, mux8x32Assign, hi,
      show ¬(192 + i < 32) from by omega, show ¬(192 + i < 64) from by omega,
      show ¬(192 + i < 96) from by omega, show ¬(192 + i < 128) from by omega,
      show ¬(192 + i < 160) from by omega, show ¬(192 + i < 192) from by omega,
      show 192 + i < 224 from by omega, show 192 + i - 192 = i from by omega]
  · rw [← BoolExpr.constFold_correct, mux8x32_sym_111 ⟨i, hi⟩]
    simp [BoolExpr.eval, mux8x32Assign, hi,
      show ¬(224 + i < 32) from by omega, show ¬(224 + i < 64) from by omega,
      show ¬(224 + i < 96) from by omega, show ¬(224 + i < 128) from by omega,
      show ¬(224 + i < 160) from by omega, show ¬(224 + i < 192) from by omega,
      show ¬(224 + i < 224) from by omega, show 224 + i - 224 = i from by omega]

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
