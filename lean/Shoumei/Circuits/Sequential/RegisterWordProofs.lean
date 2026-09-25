/-
Circuits/Sequential/RegisterWordProofs.lean - Word-Level Register Proofs

Proves that flat `mkRegisterN n` (for `n = 8, 32, 64`) and hierarchical
`mkRegisterNHierarchical 160` (`Register160` = `Register64` + `Register64` +
`Register32`) implement the word-level synchronous register specification
`registerNBehavior n : Behavior (BitVec n) (BitVec n × Bool) (BitVec n)`.
-/

import Shoumei.DSL.PortResolve
import Shoumei.Semantics
import Shoumei.Semantics.Hierarchical
import Shoumei.Verification.Implements
import Shoumei.Circuits.Sequential.Register
import Shoumei.Reflection.BitVecPacking

namespace Shoumei.Circuits.Sequential

open Shoumei
open Shoumei.DSL.PortResolve
open Shoumei.Semantics
open Shoumei.Semantics.Hierarchical
open Shoumei.Verification
open Shoumei.Reflection

/-! ## Bit-level to `BitVec` Reconstruction Helpers -/

/-- Reconstruct a `Nat` from `n` Boolean bits `f 0, ..., f (n - 1)` (LSB first). -/
def bitsToNat (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => (if f n then 1 else 0) * (2 ^ n) + bitsToNat f n

/-- Construct a `BitVec n` from a bit-index function `f : Nat → Bool`. -/
def ofBitFn (n : Nat) (f : Nat → Bool) : BitVec n :=
  BitVec.ofNat n (bitsToNat f n)

theorem bitsToNat_bound (f : Nat → Bool) (n : Nat) :
    bitsToNat f n < 2 ^ n := by
  induction n with
  | zero => simp [bitsToNat]
  | succ k ih => simp only [bitsToNat]; split <;> simp <;> omega

theorem bitsToNat_testBit (f : Nat → Bool) (n i : Nat) (hi : i < n) :
    (bitsToNat f n).testBit i = f i := by
  induction n with
  | zero => omega
  | succ k ih =>
    simp only [bitsToNat]
    have hbound := bitsToNat_bound f k
    by_cases hik : i = k
    · subst hik
      split <;> rename_i heval <;> simp
      · rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hbound]; simp [heval]
      · rw [Nat.testBit_lt_two_pow hbound]; simp [heval]
    · have hik' : i < k := by omega
      split <;> simp
      · rw [Nat.testBit_two_pow_add_gt (by omega)]; exact ih hik'
      · exact ih hik'

@[simp] theorem getLsbD_ofBitFn (n : Nat) (f : Nat → Bool) (i : Nat) (hi : i < n) :
    (ofBitFn n f).getLsbD i = f i := by
  dsimp [ofBitFn]
  rw [BitVec.getLsbD_ofNat, bitsToNat_testBit f n i hi]
  simp [hi]

theorem ofBitFn_ext {n : Nat} {f : Nat → Bool} {bv : BitVec n}
    (h : ∀ i : Fin n, f i.val = bv.getLsbD i.val) :
    ofBitFn n f = bv := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_ofBitFn n f i hi]
  exact h ⟨i, hi⟩

theorem readWiresAsNat_eq_bitsToNat (env : Env) (name : String) (n : Nat) :
    readWiresAsNat env name n = bitsToNat (fun i => env (Wire.mk s!"{name}_{i}")) n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    dsimp [readWiresAsNat, bitsToNat]
    rw [ih]

theorem readResultBitVec_eq_ofBitFn (name : String) (n : Nat) (env : Env) :
    readResultBitVec name n env = ofBitFn n (fun i => env (Wire.mk s!"{name}_{i}")) := by
  dsimp [readResultBitVec, ofBitFn]
  rw [readWiresAsNat_eq_bitsToNat]

/-! ## Word-Level Synchronous Register Specification -/

/-- Word-level `n`-bit synchronous register behavior:
    - `init`: `0#n`
    - `step`: synchronous active-high reset to `0#n`, otherwise capture `d`
    - `out`: current register state `s` -/
def registerNBehavior (n : Nat) : Behavior (BitVec n) (BitVec n × Bool) (BitVec n) where
  init := 0#n
  step := fun _ (d, rst) => if rst then 0#n else d
  out  := fun s _ => s

theorem registerN_non_vacuous (n : Nat) (hn : 0 < n) :
    NonVacuousBehavior (registerNBehavior n) := by
  refine ⟨0#n, BitVec.ofNat n 1, (0#n, false), (0#n, false), ?_⟩
  intro h
  have hbit := congrArg (fun bv => bv.getLsbD 0) h
  simp [registerNBehavior, hn] at hbit

/-- Encode `(d, rst)` into a circuit input `Env`. -/
def registerNEncI {n : Nat} (i : BitVec n × Bool) : Env :=
  let (d, rst) := i
  fun w =>
    if w == Wire.mk "reset" then rst
    else if w == Wire.mk "clock" then true
    else match (List.range n).find? (fun j => Wire.mk s!"{"d"}_{j}" == w) with
      | some j => d.getLsbD j
      | none => false

/-- Abstract state of a flat `n`-bit register (`q_0 .. q_{n-1}`). -/
def regNAbsS (n : Nat) (s : State) : BitVec n :=
  readResultBitVec "q" n s

/-- Decode output of an `n`-bit register (`q_0 .. q_{n-1}`). -/
def regNDecO (n : Nat) (env : Env) : BitVec n :=
  readResultBitVec "q" n env

/-! ## Structural Evaluation Lemmas for `mkRegisterN` -/

theorem zipWith_map {α β γ δ : Type} (f : β → γ → δ) (g : α → β) (h : α → γ) (l : List α) :
    List.zipWith f (l.map g) (l.map h) = l.map (fun x => f (g x) (h x)) := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    dsimp [List.zipWith]
    rw [ih]

theorem mkRegisterN_gates (n : Nat) :
    (mkRegisterN n).gates =
    (List.range n).map (fun j =>
      Gate.mkDFF (Wire.mk s!"{"d"}_{j}") (Wire.mk "clock") (Wire.mk "reset") (Wire.mk s!"{"q"}_{j}")) := by
  dsimp [mkRegisterN, makeIndexedWires]
  exact zipWith_map _ _ _ (List.range n)

theorem getDFFOutputs_mkRegisterN (n : Nat) :
    getDFFOutputs (mkRegisterN n) = (List.range n).map (fun j => Wire.mk s!"{"q"}_{j}") := by
  dsimp [getDFFOutputs]
  rw [mkRegisterN_gates]
  generalize List.range n = js
  induction js with
  | nil => rfl
  | cons j tl ih =>
    simp only [List.map_cons, List.filter_cons, Gate.mkDFF, GateType.isDFF, ↓reduceIte]
    exact congrArg (_ :: ·) ih

theorem foldl_comb_mkRegisterN (n : Nat) (env₀ : Env) :
    (mkRegisterN n).gates.foldl (fun env gate =>
      if gate.gateType.isCombinational then
        updateEnv env gate.output (evalGate gate env)
      else env) env₀ = env₀ := by
  rw [mkRegisterN_gates]
  generalize List.range n = js
  induction js generalizing env₀ with
  | nil => rfl
  | cons j tl ih =>
    simp only [List.map_cons, List.foldl_cons, Gate.mkDFF, GateType.isCombinational, Bool.false_eq_true, ↓reduceIte]
    exact ih env₀

theorem filterMap_dff_mkRegisterN (n : Nat) (combEnv : Env) :
    (mkRegisterN n).gates.filterMap (fun gate =>
      if gate.gateType.isDFF then
        some (gate.output, evalDFF gate combEnv)
      else none) =
    (List.range n).map (fun j =>
      (Wire.mk s!"{"q"}_{j}",
       if combEnv (Wire.mk "reset") then false else combEnv (Wire.mk s!"{"d"}_{j}"))) := by
  rw [mkRegisterN_gates]
  generalize List.range n = js
  induction js with
  | nil => rfl
  | cons j tl ih =>
    simp only [List.map_cons, List.filterMap_cons, Gate.mkDFF, GateType.isDFF, evalDFF, ↓reduceIte]
    exact congrArg (_ :: ·) ih

theorem evalCycleSequential_mkRegisterN (n : Nat) (s : State) (inEnv : Env) :
    evalCycleSequential (mkRegisterN n) s inEnv =
    (updateState s ((List.range n).map (fun j =>
      (Wire.mk s!"{"q"}_{j}",
       if mergeStateIntoEnv s inEnv (getDFFOutputs (mkRegisterN n)) (Wire.mk "reset")
       then false
       else mergeStateIntoEnv s inEnv (getDFFOutputs (mkRegisterN n)) (Wire.mk s!"{"d"}_{j}")))),
     mergeStateIntoEnv s inEnv (getDFFOutputs (mkRegisterN n))) := by
  dsimp [evalCycleSequential]
  rw [foldl_comb_mkRegisterN, filterMap_dff_mkRegisterN]

theorem updateState_map (l : List α) (s : State) (k : α → Wire) (v : α → Bool) (w : Wire) :
    updateState s (l.map (fun x => (k x, v x))) w =
    match l.find? (fun x => k x == w) with
    | some x => v x
    | none => s w := by
  dsimp [updateState]
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    dsimp [List.find?]
    cases (k hd == w) with
    | true => rfl
    | false => exact ih

/-- Decidable structural check on `mkRegisterN n` wire names:
    - `"reset"` is not a DFF output
    - For every `i < n`:
      - `q_i` is a DFF output and resolves to index `i` in `q_0..q_{n-1}`
      - `d_i` is not a DFF output, not `"reset"`, not `"clock"`, and resolves to index `i` in `d_0..d_{n-1}` -/
def checkFlatRegWires (n : Nat) : Bool :=
  let dffs := getDFFOutputs (mkRegisterN n)
  !dffs.contains (Wire.mk "reset") &&
  (List.range n).all (fun i =>
    dffs.contains (Wire.mk s!"{"q"}_{i}") &&
    !dffs.contains (Wire.mk s!"{"d"}_{i}") &&
    !(Wire.mk s!"{"d"}_{i}" == Wire.mk "reset") &&
    !(Wire.mk s!"{"d"}_{i}" == Wire.mk "clock") &&
    ((List.range n).find? (fun j => Wire.mk s!"{"q"}_{j}" == Wire.mk s!"{"q"}_{i}") == some i) &&
    ((List.range n).find? (fun j => Wire.mk s!"{"d"}_{j}" == Wire.mk s!"{"d"}_{i}") == some i))

theorem regN_init_agree (n : Nat) :
    regNAbsS n initState = (registerNBehavior n).init := by
  dsimp [regNAbsS, registerNBehavior]
  rw [readResultBitVec_eq_ofBitFn]
  apply ofBitFn_ext
  intro i
  simp [initState]

theorem regN_out_agree (n : Nat) (h_check : checkFlatRegWires n = true)
    (s : State) (i : BitVec n × Bool) :
    regNDecO n (evalCycleSequential (mkRegisterN n) s (registerNEncI i)).2 =
    (registerNBehavior n).out (regNAbsS n s) i := by
  dsimp [regNDecO, regNAbsS, registerNBehavior]
  rw [evalCycleSequential_mkRegisterN, readResultBitVec_eq_ofBitFn, readResultBitVec_eq_ofBitFn]
  apply ofBitFn_ext
  intro idx
  rw [getLsbD_ofBitFn n _ idx.val idx.isLt]
  dsimp [checkFlatRegWires] at h_check
  rw [Bool.and_eq_true, List.all_eq_true] at h_check
  have h_idx := h_check.2 idx.val (List.mem_range.mpr idx.isLt)
  simp only [Bool.and_eq_true] at h_idx
  have h_q_in : (getDFFOutputs (mkRegisterN n)).contains (Wire.mk s!"{"q"}_{idx.val}") = true :=
    h_idx.1.1.1.1.1
  dsimp [mergeStateIntoEnv]
  rw [h_q_in]
  rfl

theorem regN_step_agree (n : Nat) (h_check : checkFlatRegWires n = true)
    (s : State) (i : BitVec n × Bool) :
    regNAbsS n (evalCycleSequential (mkRegisterN n) s (registerNEncI i)).1 =
    (registerNBehavior n).step (regNAbsS n s) i := by
  obtain ⟨d, rst⟩ := i
  dsimp [regNAbsS, registerNBehavior]
  rw [evalCycleSequential_mkRegisterN, readResultBitVec_eq_ofBitFn]
  apply ofBitFn_ext
  intro idx
  dsimp only
  rw [updateState_map]
  dsimp [checkFlatRegWires] at h_check
  rw [Bool.and_eq_true, List.all_eq_true] at h_check
  have h_rst_not_dff : (getDFFOutputs (mkRegisterN n)).contains (Wire.mk "reset") = false := by
    cases h : (getDFFOutputs (mkRegisterN n)).contains (Wire.mk "reset") with
    | false => rfl
    | true => rw [h] at h_check; cases h_check.1
  have h_idx := h_check.2 idx.val (List.mem_range.mpr idx.isLt)
  simp only [Bool.and_eq_true, beq_iff_eq] at h_idx
  have h_d_not_dff : (getDFFOutputs (mkRegisterN n)).contains (Wire.mk s!"{"d"}_{idx.val}") = false := by
    cases h : (getDFFOutputs (mkRegisterN n)).contains (Wire.mk s!"{"d"}_{idx.val}") with
    | false => rfl
    | true => rw [h] at h_idx; cases h_idx.1.1.1.1.2
  have h_d_not_rst : (Wire.mk s!"{"d"}_{idx.val}" == Wire.mk "reset") = false := by
    cases h : (Wire.mk s!"{"d"}_{idx.val}" == Wire.mk "reset") with
    | false => rfl
    | true => rw [h] at h_idx; cases h_idx.1.1.1.2
  have h_d_not_clk : (Wire.mk s!"{"d"}_{idx.val}" == Wire.mk "clock") = false := by
    cases h : (Wire.mk s!"{"d"}_{idx.val}" == Wire.mk "clock") with
    | false => rfl
    | true => rw [h] at h_idx; cases h_idx.1.1.2
  have h_find_q : (List.range n).find? (fun j => Wire.mk s!"{"q"}_{j}" == Wire.mk s!"{"q"}_{idx.val}") = some idx.val :=
    h_idx.1.2
  have h_find_d : (List.range n).find? (fun j => Wire.mk s!"{"d"}_{j}" == Wire.mk s!"{"d"}_{idx.val}") = some idx.val :=
    h_idx.2
  rw [h_find_q]
  dsimp only [mergeStateIntoEnv]
  rw [h_rst_not_dff, h_d_not_dff]
  dsimp only [Bool.false_eq_true, ↓reduceIte, registerNEncI]
  have h_rst_self : (Wire.mk "reset" == Wire.mk "reset") = true := rfl
  rw [h_rst_self, h_d_not_rst, h_d_not_clk, h_find_d]
  cases rst <;> simp

/-! ## Concrete Flat Register Proofs (`Register8`, `Register32`, `Register64`) -/

theorem checkFlatRegWires_8 : checkFlatRegWires 8 = true := by native_decide
theorem checkFlatRegWires_32 : checkFlatRegWires 32 = true := by native_decide
theorem checkFlatRegWires_64 : checkFlatRegWires 64 = true := by native_decide

theorem register8_implements :
    Implements [] 1 mkRegister8 (registerNBehavior 8) (regNAbsS 8) registerNEncI (regNDecO 8) (fun _ => True) :=
  implements_of_flat_trivial [] 0 mkRegister8 rfl
    (registerNBehavior 8) (regNAbsS 8) registerNEncI (regNDecO 8)
    (regN_init_agree 8)
    (regN_step_agree 8 checkFlatRegWires_8)
    (regN_out_agree 8 checkFlatRegWires_8)

theorem register32_implements :
    Implements [] 1 mkRegister32 (registerNBehavior 32) (regNAbsS 32) registerNEncI (regNDecO 32) (fun _ => True) :=
  implements_of_flat_trivial [] 0 mkRegister32 rfl
    (registerNBehavior 32) (regNAbsS 32) registerNEncI (regNDecO 32)
    (regN_init_agree 32)
    (regN_step_agree 32 checkFlatRegWires_32)
    (regN_out_agree 32 checkFlatRegWires_32)

theorem register64_implements :
    Implements [] 1 mkRegister64 (registerNBehavior 64) (regNAbsS 64) registerNEncI (regNDecO 64) (fun _ => True) :=
  implements_of_flat_trivial [] 0 mkRegister64 rfl
    (registerNBehavior 64) (regNAbsS 64) registerNEncI (regNDecO 64)
    (regN_init_agree 64)
    (regN_step_agree 64 checkFlatRegWires_64)
    (regN_out_agree 64 checkFlatRegWires_64)

/-! ## Hierarchical `Register160` (`64 + 64 + 32`) Word-Level Proof -/

/-- Minimal registry for `Register160` (`Register64` and `Register32`). -/
def regReg160 : ModuleRegistry :=
  [("Register64", mkRegisterN 64), ("Register32", mkRegisterN 32)]

/-- Scoped child state wire corresponding to bit `i < 160` of `mkRegister160Hierarchical`. -/
def reg160HierStateWire (i : Nat) : Wire :=
  if i < 64 then Wire.mk s!"reg_0_to_63/q_{i}"
  else if i < 128 then Wire.mk s!"reg_64_to_127/q_{i - 64}"
  else Wire.mk s!"reg_128_to_159/q_{i - 128}"

/-- Word-level state abstraction for `mkRegister160Hierarchical` across its 3 child instances. -/
def reg160HierAbsS (s : State) : BitVec 160 :=
  ofBitFn 160 (fun i => s (reg160HierStateWire i))

theorem reg160Hier_init_agree :
    reg160HierAbsS initState = (registerNBehavior 160).init := by
  dsimp [reg160HierAbsS, registerNBehavior]
  apply ofBitFn_ext
  intro i
  simp [initState]

/-- Apply a list of `(Option Wire, Bool)` updates to an environment `env`. -/
def applyEnvUpdates (env : Env) (updates : List (Option Wire × Bool)) : Env :=
  updates.foldl (fun e p =>
    match p.1 with
    | some pw => updateEnv e pw p.2
    | none => e) env

theorem applyEnvUpdates_append (env : Env) (u₁ u₂ : List (Option Wire × Bool)) :
    applyEnvUpdates env (u₁ ++ u₂) = applyEnvUpdates (applyEnvUpdates env u₁) u₂ := by
  dsimp [applyEnvUpdates]
  rw [List.foldl_append]

theorem applyEnvUpdates_map (l : List α) (k : α → Option Wire) (v : α → Bool) (env : Env) (w : Wire) :
    applyEnvUpdates env (l.map (fun x => (k x, v x))) w =
    match l.reverse.find? (fun x => k x == some w) with
    | some x => v x
    | none => env w := by
  dsimp [applyEnvUpdates]
  induction l generalizing env with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons, List.foldl_cons, List.reverse_cons, List.find?_append]
    rw [ih]
    cases tl.reverse.find? (fun x => k x == some w) with
    | some x => rfl
    | none =>
      dsimp [List.find?]
      cases h_k : k hd with
      | none => rfl
      | some pw =>
        dsimp [updateEnv]
        have h_beq : (pw == w) = (w == pw) := by
          cases h1 : (w == pw) with
          | true => rw [wire_beq_eq w pw h1, wire_beq_self]
          | false =>
            cases h2 : (pw == w) with
            | false => rfl
            | true =>
              rw [wire_beq_eq pw w h2, wire_beq_self] at h1
              cases h1
        change (if (w == pw) = true then v hd else env w) =
          match (match pw == w with | true => some hd | false => none) with
          | some x => v x
          | none => env w
        rw [h_beq]
        cases (w == pw) <;> rfl

theorem allDFFWires_mkRegisterN (reg : ModuleRegistry) (n : Nat) :
    allDFFWires reg 1 (mkRegisterN n) = (List.range n).map (fun j => Wire.mk s!"{"q"}_{j}") := by
  dsimp [allDFFWires, allDFFWiresAux]
  have h_inst : (mkRegisterN n).instances = [] := rfl
  rw [h_inst, getDFFOutputs_mkRegisterN]
  simp

theorem hierStepFold_mkRegisterN (reg : ModuleRegistry) (inst : CircuitInstance)
    (nm : String) (n : Nat)
    (h_lookup : reg.find? (fun p => p.1 == inst.moduleName) = some (nm, mkRegisterN n))
    (h_check : checkFlatRegWires n = true)
    (s : State) (accUpdates : List (Wire × Bool)) (accEnv : Env) :
    hierStepFold (fun _ sub => evalCycleSequential sub) reg 1 s (accUpdates, accEnv) inst =
    (accUpdates ++ (List.range n).map (fun j =>
      (instScope inst.instName (Wire.mk s!"{"q"}_{j}"),
       if subInputEnv (mkRegisterN n) inst accEnv (Wire.mk "reset")
       then false
       else subInputEnv (mkRegisterN n) inst accEnv (Wire.mk s!"{"d"}_{j}"))),
     applyEnvUpdates accEnv ((List.range n).map (fun j =>
      (resolvePort (mkRegisterN n) inst (Wire.mk s!"{"q"}_{j}"),
       s (instScope inst.instName (Wire.mk s!"{"q"}_{j}")))))) := by
  dsimp only [hierStepFold]
  rw [h_lookup]
  dsimp only
  rw [allDFFWires_mkRegisterN, evalCycleSequential_mkRegisterN]
  dsimp only
  dsimp [checkFlatRegWires] at h_check
  rw [Bool.and_eq_true, List.all_eq_true] at h_check
  have h_rst_not_dff : (getDFFOutputs (mkRegisterN n)).contains (Wire.mk "reset") = false := by
    cases h : (getDFFOutputs (mkRegisterN n)).contains (Wire.mk "reset") with
    | false => rfl
    | true => rw [h] at h_check; cases h_check.1
  have h_scoped :
      ((List.range n).map (fun j => Wire.mk s!"{"q"}_{j}")).map (fun w =>
        (instScope inst.instName w,
         updateState (fun w => s (instScope inst.instName w))
           ((List.range n).map (fun j =>
             (Wire.mk s!"{"q"}_{j}",
              if mergeStateIntoEnv (fun w => s (instScope inst.instName w))
                   (subInputEnv (mkRegisterN n) inst accEnv) (getDFFOutputs (mkRegisterN n)) (Wire.mk "reset")
              then false
              else mergeStateIntoEnv (fun w => s (instScope inst.instName w))
                   (subInputEnv (mkRegisterN n) inst accEnv) (getDFFOutputs (mkRegisterN n)) (Wire.mk s!"{"d"}_{j}"))))
           w)) =
      (List.range n).map (fun j =>
        (instScope inst.instName (Wire.mk s!"{"q"}_{j}"),
         if subInputEnv (mkRegisterN n) inst accEnv (Wire.mk "reset")
         then false
         else subInputEnv (mkRegisterN n) inst accEnv (Wire.mk s!"{"d"}_{j}"))) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro j hj
    have h_j := h_check.2 j hj
    simp only [Bool.and_eq_true, beq_iff_eq] at h_j
    have h_d_not_dff : (getDFFOutputs (mkRegisterN n)).contains (Wire.mk s!"{"d"}_{j}") = false := by
      cases h : (getDFFOutputs (mkRegisterN n)).contains (Wire.mk s!"{"d"}_{j}") with
      | false => rfl
      | true => rw [h] at h_j; cases h_j.1.1.1.1.2
    have h_find_q : (List.range n).find? (fun k => Wire.mk s!"{"q"}_{k}" == Wire.mk s!"{"q"}_{j}") = some j :=
      h_j.1.2
    dsimp only [Function.comp]
    rw [updateState_map, h_find_q]
    dsimp only [mergeStateIntoEnv]
    rw [h_rst_not_dff, h_d_not_dff]
    rfl
  have h_env :
      (mkRegisterN n).outputs.foldl (fun e outWire =>
        match resolvePort (mkRegisterN n) inst outWire with
        | some pw =>
          updateEnv e pw
            (mergeStateIntoEnv (fun w => s (instScope inst.instName w))
              (subInputEnv (mkRegisterN n) inst accEnv) (getDFFOutputs (mkRegisterN n)) outWire)
        | none => e) accEnv =
      applyEnvUpdates accEnv ((List.range n).map (fun j =>
        (resolvePort (mkRegisterN n) inst (Wire.mk s!"{"q"}_{j}"),
         s (instScope inst.instName (Wire.mk s!"{"q"}_{j}"))))) := by
    change ((List.range n).map (fun j => Wire.mk s!"{"q"}_{j}")).foldl _ accEnv = _
    dsimp [applyEnvUpdates]
    rw [List.foldl_map, List.foldl_map]
    have h_congr : ∀ (js : List Nat), (∀ j ∈ js, j ∈ List.range n) → ∀ e,
        js.foldl (fun e j =>
          match resolvePort (mkRegisterN n) inst (Wire.mk s!"{"q"}_{j}") with
          | some pw =>
            updateEnv e pw
              (mergeStateIntoEnv (fun w => s (instScope inst.instName w))
                (subInputEnv (mkRegisterN n) inst accEnv) (getDFFOutputs (mkRegisterN n)) (Wire.mk s!"{"q"}_{j}"))
          | none => e) e =
        js.foldl (fun e j =>
          match resolvePort (mkRegisterN n) inst (Wire.mk s!"{"q"}_{j}") with
          | some pw => updateEnv e pw (s (instScope inst.instName (Wire.mk s!"{"q"}_{j}")))
          | none => e) e := by
      intro js h_sub e
      induction js generalizing e with
      | nil => rfl
      | cons j tl ih =>
        simp only [List.foldl_cons]
        have hj := h_sub j (List.Mem.head _)
        have h_tl : ∀ k ∈ tl, k ∈ List.range n := fun k hk => h_sub k (List.Mem.tail _ hk)
        have h_j := h_check.2 j hj
        simp only [Bool.and_eq_true] at h_j
        have h_q_in : (getDFFOutputs (mkRegisterN n)).contains (Wire.mk s!"{"q"}_{j}") = true :=
          h_j.1.1.1.1.1
        dsimp only [mergeStateIntoEnv]
        rw [h_q_in, if_pos rfl]
        exact ih h_tl _
    exact h_congr (List.range n) (fun _ h => h) accEnv
  exact Prod.ext (congrArg (accUpdates ++ ·) h_scoped) h_env

def defaultCircuitInstance : CircuitInstance :=
  { moduleName := "", instName := "", portMap := [] }

def inst160_0 : CircuitInstance := mkRegister160Hierarchical.instances.getD 0 defaultCircuitInstance
def inst160_1 : CircuitInstance := mkRegister160Hierarchical.instances.getD 1 defaultCircuitInstance
def inst160_2 : CircuitInstance := mkRegister160Hierarchical.instances.getD 2 defaultCircuitInstance

theorem reg160Hier_instances :
    mkRegister160Hierarchical.instances = [inst160_0, inst160_1, inst160_2] := by
  native_decide

theorem inst160_0_mod : inst160_0.moduleName = "Register64" := by native_decide
theorem inst160_1_mod : inst160_1.moduleName = "Register64" := by native_decide
theorem inst160_2_mod : inst160_2.moduleName = "Register32" := by native_decide

theorem lookup_inst160_0 :
    regReg160.find? (fun p => p.1 == inst160_0.moduleName) = some ("Register64", mkRegisterN 64) := by
  rw [inst160_0_mod]; rfl

theorem lookup_inst160_1 :
    regReg160.find? (fun p => p.1 == inst160_1.moduleName) = some ("Register64", mkRegisterN 64) := by
  rw [inst160_1_mod]; rfl

theorem lookup_inst160_2 :
    regReg160.find? (fun p => p.1 == inst160_2.moduleName) = some ("Register32", mkRegisterN 32) := by
  rw [inst160_2_mod]; rfl

def regSliceOutKey (p : CircuitInstance × Nat × Nat) : Option Wire :=
  resolvePort (mkRegisterN p.2.1) p.1 (Wire.mk s!"{"q"}_{p.2.2}")

def regSliceStateWire (p : CircuitInstance × Nat × Nat) : Wire :=
  instScope p.1.instName (Wire.mk s!"{"q"}_{p.2.2}")

def regSliceUpdFn (inEnv : Env) (p : CircuitInstance × Nat × Nat) : Wire × Bool :=
  (regSliceStateWire p,
   if subInputEnv (mkRegisterN p.2.1) p.1 inEnv (Wire.mk "reset")
   then false
   else subInputEnv (mkRegisterN p.2.1) p.1 inEnv (Wire.mk s!"{"d"}_{p.2.2}"))

def regSliceEnvFn (s : State) (p : CircuitInstance × Nat × Nat) : Option Wire × Bool :=
  (regSliceOutKey p, s (regSliceStateWire p))

def slices160_0 : List (CircuitInstance × Nat × Nat) :=
  (List.range 64).map (fun j => (inst160_0, 64, j))

def slices160_1 : List (CircuitInstance × Nat × Nat) :=
  (List.range 64).map (fun j => (inst160_1, 64, j))

def slices160_2 : List (CircuitInstance × Nat × Nat) :=
  (List.range 32).map (fun j => (inst160_2, 32, j))

def slices160 : List (CircuitInstance × Nat × Nat) :=
  slices160_0 ++ slices160_1 ++ slices160_2

theorem hierStepFold_mkRegisterN_inEnv (reg : ModuleRegistry) (inst : CircuitInstance)
    (nm : String) (n : Nat)
    (h_lookup : reg.find? (fun p => p.1 == inst.moduleName) = some (nm, mkRegisterN n))
    (h_check : checkFlatRegWires n = true)
    (xs : List (CircuitInstance × Nat × Nat))
    (h_disj_rst : (resolvePort (mkRegisterN n) inst (Wire.mk "reset")).all
      (fun pw => (xs.reverse.find? (fun p => regSliceOutKey p == some pw)).isNone) = true)
    (h_disj_d : (List.range n).all (fun j =>
      (resolvePort (mkRegisterN n) inst (Wire.mk s!"{"d"}_{j}")).all
        (fun pw => (xs.reverse.find? (fun p => regSliceOutKey p == some pw)).isNone)) = true)
    (s : State) (accUpdates : List (Wire × Bool)) (inEnv : Env) :
    hierStepFold (fun _ sub => evalCycleSequential sub) reg 1 s
      (accUpdates, applyEnvUpdates inEnv (xs.map (regSliceEnvFn s))) inst =
    (accUpdates ++ ((List.range n).map (fun j => (inst, n, j))).map (regSliceUpdFn inEnv),
     applyEnvUpdates inEnv ((xs ++ (List.range n).map (fun j => (inst, n, j))).map (regSliceEnvFn s))) := by
  let accEnv := applyEnvUpdates inEnv (xs.map (regSliceEnvFn s))
  rw [hierStepFold_mkRegisterN reg inst nm n h_lookup h_check s accUpdates accEnv]
  have h_rst_eq :
      subInputEnv (mkRegisterN n) inst accEnv (Wire.mk "reset") =
      subInputEnv (mkRegisterN n) inst inEnv (Wire.mk "reset") := by
    dsimp [subInputEnv]
    cases h_r : resolvePort (mkRegisterN n) inst (Wire.mk "reset") with
    | none => rfl
    | some pw =>
      rw [h_r] at h_disj_rst
      dsimp [Option.all] at h_disj_rst
      change applyEnvUpdates inEnv (xs.map (fun p => (regSliceOutKey p, s (regSliceStateWire p)))) pw = inEnv pw
      rw [applyEnvUpdates_map]
      cases h_f : xs.reverse.find? (fun p => regSliceOutKey p == some pw) with
      | none => rfl
      | some _ => rw [h_f] at h_disj_rst; cases h_disj_rst
  have h_upd_eq :
      (List.range n).map (fun j =>
        (instScope inst.instName (Wire.mk s!"{"q"}_{j}"),
         if subInputEnv (mkRegisterN n) inst accEnv (Wire.mk "reset")
         then false
         else subInputEnv (mkRegisterN n) inst accEnv (Wire.mk s!"{"d"}_{j}"))) =
      ((List.range n).map (fun j => (inst, n, j))).map (regSliceUpdFn inEnv) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro j hj
    dsimp only [Function.comp, regSliceUpdFn, regSliceStateWire]
    rw [h_rst_eq]
    have h_dj := (List.all_eq_true.mp h_disj_d) j hj
    have h_d_eq :
        subInputEnv (mkRegisterN n) inst accEnv (Wire.mk s!"{"d"}_{j}") =
        subInputEnv (mkRegisterN n) inst inEnv (Wire.mk s!"{"d"}_{j}") := by
      dsimp [subInputEnv]
      cases h_r : resolvePort (mkRegisterN n) inst (Wire.mk s!"{"d"}_{j}") with
      | none => rfl
      | some pw =>
        rw [h_r] at h_dj
        dsimp [Option.all] at h_dj
        change applyEnvUpdates inEnv (xs.map (fun p => (regSliceOutKey p, s (regSliceStateWire p)))) pw = inEnv pw
        rw [applyEnvUpdates_map]
        cases h_f : xs.reverse.find? (fun p => regSliceOutKey p == some pw) with
        | none => rfl
        | some _ => rw [h_f] at h_dj; cases h_dj
    rw [h_d_eq]
  have h_env_eq :
      applyEnvUpdates accEnv ((List.range n).map (fun j =>
        (resolvePort (mkRegisterN n) inst (Wire.mk s!"{"q"}_{j}"),
         s (instScope inst.instName (Wire.mk s!"{"q"}_{j}"))))) =
      applyEnvUpdates inEnv ((xs ++ (List.range n).map (fun j => (inst, n, j))).map (regSliceEnvFn s)) := by
    dsimp [accEnv, regSliceEnvFn]
    rw [List.map_append, applyEnvUpdates_append, List.map_map]
    rfl
  exact Prod.ext (congrArg (accUpdates ++ ·) h_upd_eq) h_env_eq

theorem disj_rst_0 :
    (resolvePort (mkRegisterN 64) inst160_0 (Wire.mk "reset")).all
      (fun pw => ([].reverse.find? (fun p => regSliceOutKey p == some pw)).isNone) = true := by
  native_decide

theorem disj_d_0 :
    (List.range 64).all (fun j =>
      (resolvePort (mkRegisterN 64) inst160_0 (Wire.mk s!"{"d"}_{j}")).all
        (fun pw => ([].reverse.find? (fun p => regSliceOutKey p == some pw)).isNone)) = true := by
  native_decide

theorem disj_rst_1 :
    (resolvePort (mkRegisterN 64) inst160_1 (Wire.mk "reset")).all
      (fun pw => (slices160_0.reverse.find? (fun p => regSliceOutKey p == some pw)).isNone) = true := by
  native_decide

theorem disj_d_1 :
    (List.range 64).all (fun j =>
      (resolvePort (mkRegisterN 64) inst160_1 (Wire.mk s!"{"d"}_{j}")).all
        (fun pw => (slices160_0.reverse.find? (fun p => regSliceOutKey p == some pw)).isNone)) = true := by
  native_decide

theorem disj_rst_2 :
    (resolvePort (mkRegisterN 32) inst160_2 (Wire.mk "reset")).all
      (fun pw => ((slices160_0 ++ slices160_1).reverse.find? (fun p => regSliceOutKey p == some pw)).isNone) = true := by
  native_decide

theorem disj_d_2 :
    (List.range 32).all (fun j =>
      (resolvePort (mkRegisterN 32) inst160_2 (Wire.mk s!"{"d"}_{j}")).all
        (fun pw => ((slices160_0 ++ slices160_1).reverse.find? (fun p => regSliceOutKey p == some pw)).isNone)) = true := by
  native_decide

theorem specParentStep_reg160_eq (s : State) (inEnv : Env) :
    specParentStep (fun sub sSub inEnv => evalCycleSequential sub sSub inEnv)
      regReg160 1 mkRegister160Hierarchical s inEnv =
    (updateState s (slices160.map (regSliceUpdFn inEnv)),
     applyEnvUpdates inEnv (slices160.map (regSliceEnvFn s))) := by
  have h_base :
      specParentStep (fun sub sSub inEnv => evalCycleSequential sub sSub inEnv)
        regReg160 1 mkRegister160Hierarchical s inEnv =
      let (subUpdates, env₂) :=
        mkRegister160Hierarchical.instances.foldl
          (hierStepFold (fun _ sub => evalCycleSequential sub) regReg160 1 s) ([], inEnv)
      (updateState s subUpdates, env₂) := rfl
  rw [h_base, reg160Hier_instances]
  simp only [List.foldl_cons, List.foldl_nil]
  have h0 := hierStepFold_mkRegisterN_inEnv regReg160 inst160_0 "Register64" 64
    lookup_inst160_0 checkFlatRegWires_64 [] disj_rst_0 disj_d_0 s [] inEnv
  change hierStepFold (fun _ sub => evalCycleSequential sub) regReg160 1 s ([], inEnv) inst160_0 =
    (slices160_0.map (regSliceUpdFn inEnv), applyEnvUpdates inEnv (slices160_0.map (regSliceEnvFn s))) at h0
  rw [h0]
  have h1 := hierStepFold_mkRegisterN_inEnv regReg160 inst160_1 "Register64" 64
    lookup_inst160_1 checkFlatRegWires_64 slices160_0 disj_rst_1 disj_d_1 s
    (slices160_0.map (regSliceUpdFn inEnv)) inEnv
  change hierStepFold (fun _ sub => evalCycleSequential sub) regReg160 1 s
    (slices160_0.map (regSliceUpdFn inEnv), applyEnvUpdates inEnv (slices160_0.map (regSliceEnvFn s))) inst160_1 =
    (slices160_0.map (regSliceUpdFn inEnv) ++ slices160_1.map (regSliceUpdFn inEnv),
     applyEnvUpdates inEnv ((slices160_0 ++ slices160_1).map (regSliceEnvFn s))) at h1
  rw [h1]
  have h2 := hierStepFold_mkRegisterN_inEnv regReg160 inst160_2 "Register32" 32
    lookup_inst160_2 checkFlatRegWires_32 (slices160_0 ++ slices160_1) disj_rst_2 disj_d_2 s
    (slices160_0.map (regSliceUpdFn inEnv) ++ slices160_1.map (regSliceUpdFn inEnv)) inEnv
  change hierStepFold (fun _ sub => evalCycleSequential sub) regReg160 1 s
    (slices160_0.map (regSliceUpdFn inEnv) ++ slices160_1.map (regSliceUpdFn inEnv),
     applyEnvUpdates inEnv ((slices160_0 ++ slices160_1).map (regSliceEnvFn s))) inst160_2 =
    (slices160_0.map (regSliceUpdFn inEnv) ++ slices160_1.map (regSliceUpdFn inEnv) ++ slices160_2.map (regSliceUpdFn inEnv),
     applyEnvUpdates inEnv (slices160.map (regSliceEnvFn s))) at h2
  rw [h2]
  simp only [slices160, List.map_append]

theorem opt_wire_beq_eq (o₁ o₂ : Option Wire) (h : (o₁ == o₂) = true) : o₁ = o₂ := by
  cases o₁ with
  | none => cases o₂ <;> first | rfl | cases h
  | some w₁ =>
    cases o₂ with
    | none => cases h
    | some w₂ => exact congrArg some (wire_beq_eq w₁ w₂ h)

/-- Decidable check for `Register160` output and state slice routing across all 160 bits. -/
def checkReg160Slices : Bool :=
  (List.range 160).all (fun i =>
    !(Wire.mk s!"{"d"}_{i}" == Wire.mk "reset") &&
    !(Wire.mk s!"{"d"}_{i}" == Wire.mk "clock") &&
    ((List.range 160).find? (fun j => Wire.mk s!"{"d"}_{j}" == Wire.mk s!"{"d"}_{i}") == some i) &&
    (match slices160.reverse.find? (fun p => regSliceOutKey p == some (Wire.mk s!"{"q"}_{i}")) with
     | some p => regSliceStateWire p == reg160HierStateWire i
     | none => false) &&
    (match slices160.find? (fun p => regSliceStateWire p == reg160HierStateWire i) with
     | some p =>
       (resolvePort (mkRegisterN p.2.1) p.1 (Wire.mk "reset") == some (Wire.mk "reset")) &&
       (resolvePort (mkRegisterN p.2.1) p.1 (Wire.mk s!"{"d"}_{p.2.2}") == some (Wire.mk s!"{"d"}_{i}"))
     | none => false))

theorem checkReg160Slices_ok : checkReg160Slices = true := by
  native_decide

theorem reg160Hier_out_agree (s : State) (i : BitVec 160 × Bool) :
    regNDecO 160
      (specParentStep (fun sub sSub inEnv => evalCycleSequential sub sSub inEnv)
        regReg160 1 mkRegister160Hierarchical s (registerNEncI i)).2 =
    (registerNBehavior 160).out (reg160HierAbsS s) i := by
  rw [specParentStep_reg160_eq]
  dsimp [regNDecO, reg160HierAbsS, registerNBehavior]
  rw [readResultBitVec_eq_ofBitFn]
  apply ofBitFn_ext
  intro idx
  rw [getLsbD_ofBitFn 160 _ idx.val idx.isLt]
  change applyEnvUpdates (registerNEncI i)
    (slices160.map (fun p => (regSliceOutKey p, s (regSliceStateWire p))))
    (Wire.mk s!"{"q"}_{idx.val}") = s (reg160HierStateWire idx.val)
  rw [applyEnvUpdates_map]
  have h_idx := (List.all_eq_true.mp checkReg160Slices_ok) idx.val (List.mem_range.mpr idx.isLt)
  simp only [Bool.and_eq_true] at h_idx
  have h_out := h_idx.1.2
  cases h_f : slices160.reverse.find? (fun p => regSliceOutKey p == some (Wire.mk s!"{"q"}_{idx.val}")) with
  | none => rw [h_f] at h_out; cases h_out
  | some p =>
    rw [h_f] at h_out
    exact congrArg s (wire_beq_eq _ _ h_out)

theorem reg160Hier_step_agree (s : State) (i : BitVec 160 × Bool) :
    reg160HierAbsS
      (specParentStep (fun sub sSub inEnv => evalCycleSequential sub sSub inEnv)
        regReg160 1 mkRegister160Hierarchical s (registerNEncI i)).1 =
    (registerNBehavior 160).step (reg160HierAbsS s) i := by
  obtain ⟨d, rst⟩ := i
  rw [specParentStep_reg160_eq]
  dsimp [reg160HierAbsS, registerNBehavior]
  apply ofBitFn_ext
  intro idx
  change updateState s (slices160.map (fun p =>
    (regSliceStateWire p,
     if subInputEnv (mkRegisterN p.2.1) p.1 (registerNEncI (d, rst)) (Wire.mk "reset")
     then false
     else subInputEnv (mkRegisterN p.2.1) p.1 (registerNEncI (d, rst)) (Wire.mk s!"{"d"}_{p.2.2}"))))
    (reg160HierStateWire idx.val) = (if rst then 0#160 else d).getLsbD idx.val
  rw [updateState_map]
  have h_idx := (List.all_eq_true.mp checkReg160Slices_ok) idx.val (List.mem_range.mpr idx.isLt)
  simp only [Bool.and_eq_true, beq_iff_eq] at h_idx
  have h_d_not_rst : (Wire.mk s!"{"d"}_{idx.val}" == Wire.mk "reset") = false := by
    cases h : (Wire.mk s!"{"d"}_{idx.val}" == Wire.mk "reset") with
    | false => rfl
    | true => rw [h] at h_idx; cases h_idx.1.1.1.1
  have h_d_not_clk : (Wire.mk s!"{"d"}_{idx.val}" == Wire.mk "clock") = false := by
    cases h : (Wire.mk s!"{"d"}_{idx.val}" == Wire.mk "clock") with
    | false => rfl
    | true => rw [h] at h_idx; cases h_idx.1.1.1.2
  have h_find_d : (List.range 160).find? (fun j => Wire.mk s!"{"d"}_{j}" == Wire.mk s!"{"d"}_{idx.val}") = some idx.val :=
    h_idx.1.1.2
  have h_st := h_idx.2
  cases h_f : slices160.find? (fun p => regSliceStateWire p == reg160HierStateWire idx.val) with
  | none => rw [h_f] at h_st; cases h_st
  | some p =>
    rw [h_f] at h_st
    simp only [Bool.and_eq_true] at h_st
    have h_st1 := opt_wire_beq_eq _ _ h_st.1
    have h_st2 := opt_wire_beq_eq _ _ h_st.2
    dsimp [subInputEnv]
    rw [h_st1, h_st2]
    dsimp [registerNEncI]
    rw [h_d_not_rst, h_d_not_clk, h_find_d]
    cases rst <;> simp

end Shoumei.Circuits.Sequential
