/-
Reflection/SymbolicCompile.lean - Symbolic gate compilation with correctness proof

Mirrors `compileGate`/`compileGates` but operates on `SymWireMap` (Wire → BoolExpr)
instead of `WireMap` (Wire → Bool). The key theorem `symCompileGates_correct` proves
that symbolic compilation agrees with concrete compilation under any variable assignment.
-/

import Shoumei.Reflection.BoolExpr
import Shoumei.Reflection.CompileCircuit

namespace Shoumei.Reflection

open Shoumei

/-- Association-list map from wires to BoolExpr. -/
abbrev SymWireMap := List (Wire × BoolExpr)

namespace SymWireMap

/-- Look up a wire in a symbolic map. Returns `.lit false` if not found. -/
def lookup (m : SymWireMap) (w : Wire) : BoolExpr :=
  match m.find? (fun p => p.1 == w) with
  | some (_, e) => e
  | none => .lit false

/-- Insert a wire-expression binding (prepend). -/
def insert (m : SymWireMap) (w : Wire) (e : BoolExpr) : SymWireMap :=
  (w, e) :: m

@[simp]
theorem lookup_insert_eq (m : SymWireMap) (w : Wire) (e : BoolExpr) :
    (m.insert w e).lookup w = e := by
  simp [insert, lookup, wire_beq_self]

@[simp]
theorem lookup_insert_ne (m : SymWireMap) (w w' : Wire) (e : BoolExpr) (h : w' ≠ w) :
    (m.insert w e).lookup w' = m.lookup w' := by
  have hbeq : (w == w') = false := wire_beq_ne w w' (Ne.symm h)
  simp [insert, lookup, hbeq]

@[simp]
theorem lookup_nil (w : Wire) : SymWireMap.lookup [] w = .lit false := by
  unfold SymWireMap.lookup
  simp [List.find?]

end SymWireMap

/-- Symbolically evaluate a gate (mirrors `evalGateMap`). -/
def symEvalGate (g : Gate) (m : SymWireMap) : BoolExpr :=
  match g.gateType with
  | GateType.AND =>
      match g.inputs with
      | [i0, i1] => .and (m.lookup i0) (m.lookup i1)
      | _ => .lit false
  | GateType.OR =>
      match g.inputs with
      | [i0, i1] => .or (m.lookup i0) (m.lookup i1)
      | _ => .lit false
  | GateType.NOT =>
      match g.inputs with
      | [i0] => .not (m.lookup i0)
      | _ => .lit false
  | GateType.XOR =>
      match g.inputs with
      | [i0, i1] => .xor (m.lookup i0) (m.lookup i1)
      | _ => .lit false
  | GateType.BUF =>
      match g.inputs with
      | [i0] => m.lookup i0
      | _ => .lit false
  | GateType.MUX =>
      match g.inputs with
      | [in0, in1, sel] => .ite (m.lookup sel) (m.lookup in1) (m.lookup in0)
      | _ => .lit false
  | GateType.DFF | GateType.DFF_SET => .lit false

/-- Symbolically compile one gate. -/
def symCompileGate (m : SymWireMap) (g : Gate) : SymWireMap :=
  m.insert g.output (symEvalGate g m)

/-- Symbolically compile a gate list. -/
def symCompileGates (gates : List Gate) (m : SymWireMap) : SymWireMap :=
  gates.foldl symCompileGate m

/-- symEvalGate agrees with evalGateMap under any assignment. -/
theorem symEvalGate_correct (g : Gate) (sm : SymWireMap) (m : WireMap)
    (assign : Nat → Bool)
    (h : ∀ w, (sm.lookup w).eval assign = m.lookup w) :
    (symEvalGate g sm).eval assign = evalGateMap g m := by
  simp only [symEvalGate, evalGateMap]
  cases g.gateType <;> simp_all [BoolExpr.eval]
  all_goals (split <;> simp_all [BoolExpr.eval])

/-- symCompileGate agrees with compileGate under any assignment. -/
theorem symCompileGate_correct (g : Gate) (sm : SymWireMap) (m : WireMap)
    (assign : Nat → Bool)
    (h : ∀ w, (sm.lookup w).eval assign = m.lookup w) :
    ∀ w, ((symCompileGate sm g).lookup w).eval assign = (compileGate m g).lookup w := by
  intro w
  simp only [symCompileGate, compileGate]
  by_cases hne : w = g.output
  · subst hne
    simp [SymWireMap.lookup_insert_eq, WireMap.lookup_insert_eq]
    exact symEvalGate_correct g sm m assign h
  · simp [SymWireMap.lookup_insert_ne _ _ _ _ hne, WireMap.lookup_insert_ne _ _ _ _ hne]
    exact h w

/-- Core correctness: symCompileGates agrees with compileGates under any assignment. -/
theorem symCompileGates_correct (gates : List Gate) (sm : SymWireMap) (m : WireMap)
    (assign : Nat → Bool)
    (h : ∀ w, (sm.lookup w).eval assign = m.lookup w) :
    ∀ w, ((symCompileGates gates sm).lookup w).eval assign =
         (compileGates gates m).lookup w := by
  induction gates generalizing sm m with
  | nil => exact h
  | cons g rest ih =>
    simp [symCompileGates, compileGates, List.foldl]
    apply ih
    exact symCompileGate_correct g sm m assign h

end Shoumei.Reflection
