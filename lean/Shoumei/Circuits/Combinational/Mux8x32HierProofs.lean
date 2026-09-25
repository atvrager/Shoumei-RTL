/-
Circuits/Combinational/Mux8x32HierProofs.lean - Hierarchical Mux8x32 Word-Level Proof

Proves that the emitted hierarchical 8:1 32-bit multiplexer
`mkMux8x32Hierarchical` (`mkMux8xNHierarchical 32`, composed of two `Mux4x32`
instances plus select buffers and top 2:1 MUX gates) satisfies the word-level
routing specification `mux8x32Spec` over `evalHier`.
-/

import Shoumei.Circuits.Combinational.MuxTreeProofs

namespace Shoumei.Circuits.Combinational

open Shoumei
open Shoumei.DSL.PortResolve
open Shoumei.Semantics
open Shoumei.Semantics.Hierarchical
open Shoumei.Reflection

/-- Registry containing the flat `Mux4x32` child module. -/
def regMux8x32 : ModuleRegistry := [("Mux4x32", mkMux4x32)]

/-- Depth-1 flattened circuit of `mkMux8x32Hierarchical`. -/
def mkMux8x32HierFlat : Circuit :=
  flattenAllFuel regMux8x32 mkMux8x32Hierarchical 1

def mux8x32HierSymCompiled (s0 s1 s2 : Bool) : SymWireMap :=
  symCompileGates mkMux8x32HierFlat.gates (mux8x32SymInit s0 s1 s2)

def mux8x32HierSymResult (s0 s1 s2 : Bool) (i : Nat) : BoolExpr :=
  SymWireMap.lookup (mux8x32HierSymCompiled s0 s1 s2) (Wire.mk s!"out_{i}")

theorem mux8x32Hier_sym_check_000 : checkMuxSymMode (mux8x32HierSymCompiled false false false) 0 = true := by
  native_decide

theorem mux8x32Hier_sym_check_100 : checkMuxSymMode (mux8x32HierSymCompiled true false false) 32 = true := by
  native_decide

theorem mux8x32Hier_sym_check_010 : checkMuxSymMode (mux8x32HierSymCompiled false true false) 64 = true := by
  native_decide

theorem mux8x32Hier_sym_check_110 : checkMuxSymMode (mux8x32HierSymCompiled true true false) 96 = true := by
  native_decide

theorem mux8x32Hier_sym_check_001 : checkMuxSymMode (mux8x32HierSymCompiled false false true) 128 = true := by
  native_decide

theorem mux8x32Hier_sym_check_101 : checkMuxSymMode (mux8x32HierSymCompiled true false true) 160 = true := by
  native_decide

theorem mux8x32Hier_sym_check_011 : checkMuxSymMode (mux8x32HierSymCompiled false true true) 192 = true := by
  native_decide

theorem mux8x32Hier_sym_check_111 : checkMuxSymMode (mux8x32HierSymCompiled true true true) 224 = true := by
  native_decide

theorem mux8x32Hier_sym_000 (i : Fin 32) :
    (mux8x32HierSymResult false false false i.val).constFold = .var i.val := by
  have h := checkMuxSymMode_iff _ 0 mux8x32Hier_sym_check_000 i.val i.isLt
  simpa [mux8x32HierSymResult] using h

theorem mux8x32Hier_sym_100 (i : Fin 32) :
    (mux8x32HierSymResult true false false i.val).constFold = .var (32 + i.val) :=
  checkMuxSymMode_iff _ 32 mux8x32Hier_sym_check_100 i.val i.isLt

theorem mux8x32Hier_sym_010 (i : Fin 32) :
    (mux8x32HierSymResult false true false i.val).constFold = .var (64 + i.val) :=
  checkMuxSymMode_iff _ 64 mux8x32Hier_sym_check_010 i.val i.isLt

theorem mux8x32Hier_sym_110 (i : Fin 32) :
    (mux8x32HierSymResult true true false i.val).constFold = .var (96 + i.val) :=
  checkMuxSymMode_iff _ 96 mux8x32Hier_sym_check_110 i.val i.isLt

theorem mux8x32Hier_sym_001 (i : Fin 32) :
    (mux8x32HierSymResult false false true i.val).constFold = .var (128 + i.val) :=
  checkMuxSymMode_iff _ 128 mux8x32Hier_sym_check_001 i.val i.isLt

theorem mux8x32Hier_sym_101 (i : Fin 32) :
    (mux8x32HierSymResult true false true i.val).constFold = .var (160 + i.val) :=
  checkMuxSymMode_iff _ 160 mux8x32Hier_sym_check_101 i.val i.isLt

theorem mux8x32Hier_sym_011 (i : Fin 32) :
    (mux8x32HierSymResult false true true i.val).constFold = .var (192 + i.val) :=
  checkMuxSymMode_iff _ 192 mux8x32Hier_sym_check_011 i.val i.isLt

theorem mux8x32Hier_sym_111 (i : Fin 32) :
    (mux8x32HierSymResult true true true i.val).constFold = .var (224 + i.val) :=
  checkMuxSymMode_iff _ 224 mux8x32Hier_sym_check_111 i.val i.isLt

def evalMux8x32HierFlat (inputs : Fin 8 → BitVec 32) (sel0 sel1 sel2 : Bool) : BitVec 32 :=
  readResultBitVecMap (compileCircuit mkMux8x32HierFlat (makeMux8x32InitMap inputs sel0 sel1 sel2)) "out" 32

theorem evalMux8x32HierFlat_eq_sym (inputs : Fin 8 → BitVec 32) (sel0 sel1 sel2 : Bool) :
    evalMux8x32HierFlat inputs sel0 sel1 sel2 =
    BitVec.ofNat 32 (readSymResultAsNat (mux8x32Assign inputs) (fun i => mux8x32HierSymResult sel0 sel1 sel2 i) 32) := by
  dsimp [evalMux8x32HierFlat, readResultBitVecMap]
  apply congrArg (BitVec.ofNat 32)
  symm
  apply readSymResultAsNat_correct
  intro i
  exact symCompileCircuit_correct mkMux8x32HierFlat (mux8x32SymInit sel0 sel1 sel2)
    (makeMux8x32InitMap inputs sel0 sel1 sel2) (mux8x32Assign inputs)
    (mux8x32SymInit_correct inputs sel0 sel1 sel2) (Wire.mk s!"out_{i}")

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

theorem evalMux8x32HierFlat_correct (inputs : Fin 8 → BitVec 32) (sel0 sel1 sel2 : Bool) :
    evalMux8x32HierFlat inputs sel0 sel1 sel2 = mux8x32Spec inputs sel0 sel1 sel2 := by
  rw [evalMux8x32HierFlat_eq_sym]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_ofNat, readSymResultAsNat_testBit _ _ 32 i hi]
  simp only [hi, decide_true, Bool.true_and]
  dsimp [mux8x32Spec]
  cases sel2 <;> cases sel1 <;> cases sel0
  · rw [← BoolExpr.constFold_correct, mux8x32Hier_sym_000 ⟨i, hi⟩]
    simp [BoolExpr.eval, mux8x32Assign, hi]
  · rw [← BoolExpr.constFold_correct, mux8x32Hier_sym_100 ⟨i, hi⟩]
    simp [BoolExpr.eval, mux8x32Assign, hi,
      show ¬(32 + i < 32) from by omega, show 32 + i < 64 from by omega,
      show 32 + i - 32 = i from by omega]
  · rw [← BoolExpr.constFold_correct, mux8x32Hier_sym_010 ⟨i, hi⟩]
    simp [BoolExpr.eval, mux8x32Assign, hi,
      show ¬(64 + i < 32) from by omega, show ¬(64 + i < 64) from by omega,
      show 64 + i < 96 from by omega, show 64 + i - 64 = i from by omega]
  · rw [← BoolExpr.constFold_correct, mux8x32Hier_sym_110 ⟨i, hi⟩]
    simp [BoolExpr.eval, mux8x32Assign, hi,
      show ¬(96 + i < 32) from by omega, show ¬(96 + i < 64) from by omega,
      show ¬(96 + i < 96) from by omega, show 96 + i < 128 from by omega,
      show 96 + i - 96 = i from by omega]
  · rw [← BoolExpr.constFold_correct, mux8x32Hier_sym_001 ⟨i, hi⟩]
    simp [BoolExpr.eval, mux8x32Assign, hi,
      show ¬(128 + i < 32) from by omega, show ¬(128 + i < 64) from by omega,
      show ¬(128 + i < 96) from by omega, show ¬(128 + i < 128) from by omega,
      show 128 + i < 160 from by omega, show 128 + i - 128 = i from by omega]
  · rw [← BoolExpr.constFold_correct, mux8x32Hier_sym_101 ⟨i, hi⟩]
    simp [BoolExpr.eval, mux8x32Assign, hi,
      show ¬(160 + i < 32) from by omega, show ¬(160 + i < 64) from by omega,
      show ¬(160 + i < 96) from by omega, show ¬(160 + i < 128) from by omega,
      show ¬(160 + i < 160) from by omega, show 160 + i < 192 from by omega,
      show 160 + i - 160 = i from by omega]
  · rw [← BoolExpr.constFold_correct, mux8x32Hier_sym_011 ⟨i, hi⟩]
    simp [BoolExpr.eval, mux8x32Assign, hi,
      show ¬(192 + i < 32) from by omega, show ¬(192 + i < 64) from by omega,
      show ¬(192 + i < 96) from by omega, show ¬(192 + i < 128) from by omega,
      show ¬(192 + i < 160) from by omega, show ¬(192 + i < 192) from by omega,
      show 192 + i < 224 from by omega, show 192 + i - 192 = i from by omega]
  · rw [← BoolExpr.constFold_correct, mux8x32Hier_sym_111 ⟨i, hi⟩]
    simp [BoolExpr.eval, mux8x32Assign, hi,
      show ¬(224 + i < 32) from by omega, show ¬(224 + i < 64) from by omega,
      show ¬(224 + i < 96) from by omega, show ¬(224 + i < 128) from by omega,
      show ¬(224 + i < 160) from by omega, show ¬(224 + i < 192) from by omega,
      show ¬(224 + i < 224) from by omega, show 224 + i - 224 = i from by omega]

/-! ## Flattener Soundness Bridge for `mkMux8x32Hierarchical` -/

theorem mux8x32Hier_wellwired : WellWired regMux8x32 mkMux8x32Hierarchical = true := by
  native_decide

theorem mux8x32Hier_fresh_check : flattenFreshCheck regMux8x32 mkMux8x32Hierarchical = true := by
  native_decide

theorem mux8x32Hier_children_check : childrenOKCheck regMux8x32 mkMux8x32Hierarchical = true := by
  native_decide

theorem mux8x32Hier_evalHier_eq_flat (env : Env) :
    ∀ w ∈ mkMux8x32Hierarchical.outputs,
      evalHier regMux8x32 2 mkMux8x32Hierarchical env w =
      evalCircuit mkMux8x32HierFlat env w :=
  flatten_sound_depth1 regMux8x32 mkMux8x32Hierarchical
    mux8x32Hier_wellwired
    (FlattenFresh_of_check regMux8x32 mkMux8x32Hierarchical mux8x32Hier_fresh_check)
    (ChildrenOK_of_check regMux8x32 mkMux8x32Hierarchical mux8x32Hier_children_check)
    env

theorem mux8x32Hier_out_mem_check :
    (List.range 32).all (fun k => mkMux8x32Hierarchical.outputs.any (· == Wire.mk s!"{"out"}_{k}")) = true := by
  native_decide

theorem mux8x32Hier_out_mem (k : Nat) (hk : k < 32) :
    Wire.mk s!"{"out"}_{k}" ∈ mkMux8x32Hierarchical.outputs :=
  mem_of_any_eq_true _ _ ((List.all_eq_true.mp mux8x32Hier_out_mem_check) k (List.mem_range.mpr hk))

theorem readWiresAsNat_evalHier_mux8x32Hier (m : WireMap) (env : Env)
    (h_comp : ∀ w, (compileCircuit mkMux8x32HierFlat m).lookup w = evalCircuit mkMux8x32HierFlat env w) :
    ∀ k ≤ 32,
      readWiresAsNat (evalHier regMux8x32 2 mkMux8x32Hierarchical env) "out" k =
      readWiresAsNatMap (compileCircuit mkMux8x32HierFlat m) "out" k
  | 0, _ => rfl
  | k + 1, hk => by
    dsimp [readWiresAsNat, readWiresAsNatMap]
    have h_out := mux8x32Hier_evalHier_eq_flat env (Wire.mk s!"{"out"}_{k}")
      (mux8x32Hier_out_mem k (by omega))
    rw [h_out, ← h_comp (Wire.mk s!"{"out"}_{k}")]
    rw [readWiresAsNat_evalHier_mux8x32Hier m env h_comp k (by omega)]

end Shoumei.Circuits.Combinational
