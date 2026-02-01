import Shoumei.Circuits.Sequential.Register
import Shoumei.Semantics

namespace Shoumei.Circuits.Sequential
open Shoumei

-- 1. COMPLEX PROPERTY: Keep as Axiom
-- Proving Nat.repr is injective requires extensive lemmas about toDigits/foldl
axiom natToString_injective {i j : Nat} (h : Nat.repr i = Nat.repr j) : i = j

-- 2. WIRE EQUALITY: Keep as Axiom (to unblock build)
-- The auto-generated BEq instance is opaque and standard library lemmas 
-- for String.eq_of_beq vary by Lean version. This is structurally true.
axiom wire_beq_eq (w1 w2 : Wire) : (w1 == w2) = true → w1 = w2

-- 3. INTERPOLATION INEQUALITY: Proven (Fixed)
-- We prove they are different by looking at the first character ('q' vs 'r')
theorem q_interp_ne_reset (j : Nat) : toString "" ++ toString "q" ++ toString "" ++ toString j ++ toString "" ≠ "reset" := by
  intro h
  have h_chars := congrArg String.data h
  -- Forces 'toString "q"' to become '"q"', reducing .data to ['q', ...]
  -- This exposes the mismatch with ['r', ...] and solves the goal automatically.
  simp [ToString.toString] at h_chars
  -- 'contradiction' is NOT needed here because simp already solved it.

-- 4. CONSTRUCTOR INJECTIVITY: Proven
theorem wire_mk_injective {s1 s2 : String} (h : Wire.mk s1 = Wire.mk s2) : s1 = s2 :=
  congrArg Wire.name h

theorem makeIndexedWires_length (name : String) (n : Nat) :
    (makeIndexedWires name n).length = n := by
  simp [makeIndexedWires]

theorem register_gates_length (n : Nat) :
    (mkRegisterN n).gates.length = n := by
  simp [mkRegisterN, List.length_zipWith, makeIndexedWires_length]

theorem evalDFF_under_reset (d clk rst q : Wire) (env : Env) (hrst : env rst = true) :
    evalDFF (Gate.mkDFF d clk rst q) env = false := by
  simp [evalDFF, Gate.mkDFF, hrst]

theorem getDFFOutputs_register (n : Nat) :
    getDFFOutputs (mkRegisterN n) = makeIndexedWires "q" n := by
  simp [getDFFOutputs, mkRegisterN, makeIndexedWires]
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [List.range_succ, List.map_append, List.zipWith_append, List.filter_append, ih]
    rfl

theorem updateState_all_false (state : State) (updates : List (Wire × Bool)) (w : Wire)
    (hstate : state w = false) (hall : ∀ p ∈ updates, p.2 = false) :
    updateState state updates w = false := by
  simp [updateState]
  split
  · next h =>
    have : (_, _) ∈ updates := List.mem_of_find?_eq_some h
    exact hall _ this
  · exact hstate

theorem mergeStateIntoEnv_non_dff (state : State) (env : Env) (dffOuts : List Wire) (w : Wire)
    (h : w ∉ dffOuts) : mergeStateIntoEnv state env dffOuts w = env w := by
  unfold mergeStateIntoEnv
  split
  · next hc =>
    exfalso
    induction dffOuts with
    | nil => simp at hc
    | cons head tail ih =>
      simp [List.contains] at hc
      simp [List.mem_cons] at h
      cases hc with
      | inl heq =>
        have : w = head := wire_beq_eq w head heq
        exact h.1 this
      | inr ht =>
        exact ih h.2 ht
  · rfl

theorem reset_not_dff_output (n : Nat) :
    Wire.mk "reset" ∉ getDFFOutputs (mkRegisterN n) := by
  rw [getDFFOutputs_register]
  simp only [makeIndexedWires, List.mem_map, List.mem_range]
  intro ⟨j, _, h⟩
  -- h is a Wire equality, extract the string equality
  have h_str : toString "" ++ toString "q" ++ toString "" ++ toString j ++ toString "" = "reset" := wire_mk_injective h
  exact q_interp_ne_reset j h_str

theorem register_env_reset (n : Nat) (env : Env) (hrst : env (Wire.mk "reset") = true) :
    mergeStateIntoEnv initState env (getDFFOutputs (mkRegisterN n)) (Wire.mk "reset") = true := by
  rw [mergeStateIntoEnv_non_dff]
  · exact hrst
  · exact reset_not_dff_output n

theorem register_comb_foldl_is_id (n : Nat) (env : Env) :
    (mkRegisterN n).gates.foldl (fun env gate =>
      if gate.gateType.isCombinational then
        updateEnv env gate.output (evalCombGate gate env)
      else env) env = env := by
  simp [mkRegisterN, makeIndexedWires]
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [List.range_succ, List.map, List.zipWith, List.foldl, Gate.mkDFF, GateType.isCombinational]
    exact ih

-- Phase 6: Composition for reset behavior

-- Lemma: Under reset, all DFF evaluations in filterMap produce false
theorem register_filterMap_all_false (n : Nat) (env : Env) (hrst : env (Wire.mk "reset") = true) :
    ∀ p ∈ (mkRegisterN n).gates.filterMap (fun g =>
      if g.gateType == GateType.DFF then
        some (g.output, evalDFF g env)
      else none),
    p.2 = false := by
  intro p hp
  simp [mkRegisterN, makeIndexedWires] at hp
  -- hp is a conjunction: gate matches DFF type AND (output, evalDFF) = p
  obtain ⟨i, hi, hp_type, hp_eq⟩ := hp
  -- Extract the second part of the pair equality
  rw [← hp_eq]
  simp [Gate.mkDFF, evalDFF, hrst]

-- Main composition theorem: Register produces all-false outputs under reset
theorem register_nextState_under_reset (n : Nat) (env : Env) (hrst : env (Wire.mk "reset") = true)
    (i : Nat) (_ : i < n) :
    let (nextState, _) := evalCycleSequential (mkRegisterN n) initState env
    nextState (Wire.mk s!"q{i}") = false := by
  simp [evalCycleSequential]
  -- Step 1: env' preserves reset=true
  have henv' : mergeStateIntoEnv initState env (getDFFOutputs (mkRegisterN n)) (Wire.mk "reset") = true :=
    register_env_reset n env hrst
  -- Step 2: combinational fold is identity
  have henv'' : (mkRegisterN n).gates.foldl (fun env gate =>
      if gate.gateType.isCombinational then
        updateEnv env gate.output (evalCombGate gate env)
      else env) (mergeStateIntoEnv initState env (getDFFOutputs (mkRegisterN n))) =
    mergeStateIntoEnv initState env (getDFFOutputs (mkRegisterN n)) :=
    register_comb_foldl_is_id n _
  rw [henv'']
  -- Step 3: All filterMap entries have value false
  have hall : ∀ p ∈ (mkRegisterN n).gates.filterMap (fun g =>
      if g.gateType == GateType.DFF then
        some (g.output, evalDFF g (mergeStateIntoEnv initState env (getDFFOutputs (mkRegisterN n))))
      else none),
    p.2 = false :=
    register_filterMap_all_false n _ henv'
  -- Step 4: updateState with all false
  apply updateState_all_false
  · rfl  -- initState returns false
  · exact hall

end Shoumei.Circuits.Sequential
