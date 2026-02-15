/-
Reflection/CompileGate.lean - Gate compilation on WireMap

Mirrors `evalGate` + `updateEnv` but operates on `WireMap` instead of `Env`,
producing structurally inductive terms that `simp` can reduce.
-/

import Shoumei.Reflection.WireMap

namespace Shoumei.Reflection

open Shoumei

/-- Evaluate a gate using WireMap lookups (mirrors `evalGate`). -/
def evalGateMap (g : Gate) (m : WireMap) : Bool :=
  match g.gateType with
  | GateType.AND =>
      match g.inputs with
      | [i0, i1] => m.lookup i0 && m.lookup i1
      | _ => false
  | GateType.OR =>
      match g.inputs with
      | [i0, i1] => m.lookup i0 || m.lookup i1
      | _ => false
  | GateType.NOT =>
      match g.inputs with
      | [i0] => !(m.lookup i0)
      | _ => false
  | GateType.XOR =>
      match g.inputs with
      | [i0, i1] => xor (m.lookup i0) (m.lookup i1)
      | _ => false
  | GateType.BUF =>
      match g.inputs with
      | [i0] => m.lookup i0
      | _ => false
  | GateType.MUX =>
      match g.inputs with
      | [in0, in1, sel] => if m.lookup sel then m.lookup in1 else m.lookup in0
      | _ => false
  | GateType.DFF | GateType.DFF_SET => false

/-- Compile one gate: evaluate it on the WireMap and insert the result. -/
def compileGate (m : WireMap) (g : Gate) : WireMap :=
  m.insert g.output (evalGateMap g m)

/-- Key correctness lemma: evalGateMap agrees with evalGate when lookups agree. -/
theorem evalGateMap_correct (g : Gate) (m : WireMap) (env : Env)
    (h : ∀ w, m.lookup w = env w) :
    evalGateMap g m = evalGate g env := by
  simp only [evalGateMap, evalGate]
  cases g.gateType <;> simp_all
  all_goals (split <;> simp_all)

/-- compileGate produces a WireMap whose lookup matches updateEnv after evalGate. -/
theorem compileGate_correct (g : Gate) (m : WireMap) (env : Env)
    (h : ∀ w, m.lookup w = env w) :
    ∀ w, (compileGate m g).lookup w = updateEnv env g.output (evalGate g env) w := by
  intro w
  simp only [compileGate, updateEnv]
  by_cases hne : w = g.output
  · subst hne
    rw [WireMap.lookup_insert_eq]
    simp [wire_beq_self]
    exact evalGateMap_correct g m env h
  · rw [WireMap.lookup_insert_ne _ _ _ _ hne]
    simp [wire_beq_ne w g.output hne]
    exact h w

end Shoumei.Reflection
