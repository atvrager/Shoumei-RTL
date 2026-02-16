/-
Reflection/SequentialCompile.lean - Sequential circuit compilation

Extends the Reflection infrastructure to handle sequential circuits.
`evalCycleSequential` uses a 3-phase evaluation:
  1. Merge DFF state into environment
  2. Fold only combinational gates
  3. Evaluate DFFs for next state

This module provides WireMap-based versions of these phases with correctness proofs.
-/

import Shoumei.Reflection.CompileCircuit

namespace Shoumei.Reflection

open Shoumei

/-! ## Combinational gate filtering -/

/-- Filter a gate list to only combinational gates. -/
def combGates (gates : List Gate) : List Gate :=
  gates.filter (·.gateType.isCombinational)

/-- Compile only combinational gates from a list (mirrors Phase 2 of evalCycleSequential). -/
def compileCombGates (gates : List Gate) (m : WireMap) : WireMap :=
  gates.foldl (fun m gate =>
    if gate.gateType.isCombinational then compileGate m gate else m
  ) m

/-- Evaluate only combinational gates (mirrors Phase 2 of evalCycleSequential). -/
def evalCombGatesSeq (gates : List Gate) (env : Env) : Env :=
  gates.foldl (fun env gate =>
    if gate.gateType.isCombinational then
      updateEnv env gate.output (evalGate gate env)
    else env
  ) env

/-- Core correctness: compileCombGates agrees with evalCombGatesSeq. -/
theorem compileCombGates_correct (gates : List Gate) (m : WireMap) (env : Env)
    (h : ∀ w, m.lookup w = env w) :
    ∀ w, (compileCombGates gates m).lookup w = evalCombGatesSeq gates env w := by
  induction gates generalizing m env with
  | nil => exact h
  | cons g rest ih =>
    simp only [compileCombGates, evalCombGatesSeq, List.foldl]
    by_cases hc : g.gateType.isCombinational
    · simp [hc]
      apply ih
      exact compileGate_correct g m env h
    · simp [hc]
      exact ih m env h

/-! ## DFF evaluation on WireMap -/

/-- Evaluate a DFF gate using WireMap lookups (mirrors `evalDFF`). -/
def evalDFFMap (g : Gate) (m : WireMap) : Bool :=
  match g.gateType with
  | GateType.DFF =>
      match g.inputs with
      | [d, _clk, reset] =>
          if m.lookup reset then false else m.lookup d
      | _ => false
  | GateType.DFF_SET =>
      match g.inputs with
      | [d, _clk, reset] =>
          if m.lookup reset then true else m.lookup d
      | _ => false
  | _ => false

/-- evalDFFMap agrees with evalDFF when lookups agree. -/
theorem evalDFFMap_correct (g : Gate) (m : WireMap) (env : Env)
    (h : ∀ w, m.lookup w = env w) :
    evalDFFMap g m = evalDFF g env := by
  simp only [evalDFFMap, evalDFF]
  cases g.gateType <;> simp_all
  all_goals (split <;> simp_all)

/-! ## DFF state compilation -/

/-- Compile DFF updates from a WireMap (mirrors Phase 3 of evalCycleSequential). -/
def compileDFFUpdates (gates : List Gate) (m : WireMap) : List (Wire × Bool) :=
  gates.filterMap fun g =>
    if g.gateType.isDFF then some (g.output, evalDFFMap g m) else none

/-- compileDFFUpdates agrees with the Phase 3 filterMap in evalCycleSequential. -/
theorem compileDFFUpdates_correct (gates : List Gate) (m : WireMap) (env : Env)
    (h : ∀ w, m.lookup w = env w) :
    compileDFFUpdates gates m =
    gates.filterMap (fun g => if g.gateType.isDFF then some (g.output, evalDFF g env) else none) := by
  simp only [compileDFFUpdates]
  congr 1
  funext g
  by_cases hd : g.gateType.isDFF
  · simp [hd, evalDFFMap_correct g m env h]
  · simp [hd]

/-! ## Master bridge theorem -/

/-- Phase 2 of evalCycleSequential equals evalCombGatesSeq. -/
theorem evalCycleSequential_combEnv_eq (c : Circuit) (state : State) (inputEnv : Env) :
    (evalCycleSequential c state inputEnv).2 =
    evalCombGatesSeq c.gates (mergeStateIntoEnv state inputEnv (getDFFOutputs c)) := by
  simp [evalCycleSequential, evalCombGatesSeq]

/-- The next-state part of evalCycleSequential uses updateState on DFF filterMap. -/
theorem evalCycleSequential_state_eq (c : Circuit) (state : State) (inputEnv : Env) :
    (evalCycleSequential c state inputEnv).1 =
    updateState state (c.gates.filterMap (fun gate =>
      if gate.gateType.isDFF then
        some (gate.output, evalDFF gate (evalCombGatesSeq c.gates
          (mergeStateIntoEnv state inputEnv (getDFFOutputs c))))
      else none)) := by
  simp [evalCycleSequential, evalCombGatesSeq]

/-- Master bridge: evalCycleSequential outputs and next state agree with WireMap compilation.
    After applying this, goals reduce to WireMap lookups that `simp` can handle gate-by-gate. -/
theorem evalCycleSequential_via_wiremap (c : Circuit) (state : State) (inputEnv : Env)
    (initMap : WireMap)
    (h_init : ∀ w, initMap.lookup w = mergeStateIntoEnv state inputEnv (getDFFOutputs c) w) :
    let combMap := compileCombGates c.gates initMap
    (∀ w, (evalCycleSequential c state inputEnv).2 w = combMap.lookup w)
    ∧
    (∀ w, (evalCycleSequential c state inputEnv).1 w =
      updateState state (compileDFFUpdates c.gates combMap) w) := by
  have h_comb := compileCombGates_correct c.gates initMap
    (mergeStateIntoEnv state inputEnv (getDFFOutputs c)) h_init
  constructor
  · intro w
    rw [evalCycleSequential_combEnv_eq]
    exact (h_comb w).symm
  · intro w
    rw [evalCycleSequential_state_eq]
    have h_lists := (compileDFFUpdates_correct c.gates (compileCombGates c.gates initMap)
      (evalCombGatesSeq c.gates (mergeStateIntoEnv state inputEnv (getDFFOutputs c)))
      h_comb).symm
    simp only [updateState]
    rw [h_lists]

end Shoumei.Reflection
