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

end Shoumei.Reflection
