/-
Reflection/WireMap.lean - Proof-friendly wire-to-Bool association list

A WireMap is an association list mapping Wires to Bool values.
Unlike `Env` (Wire → Bool), WireMap is structurally inductive,
making it amenable to `simp` and `bv_decide` reasoning.
-/

import Shoumei.DSL
import Shoumei.Semantics

namespace Shoumei.Reflection

open Shoumei

-- Wire BEq lemmas (derived BEq goes through String BEq)

theorem wire_beq_unfold (w1 w2 : Wire) : (w1 == w2) = (w1.name == w2.name) := by
  cases w1; cases w2; simp [BEq.beq, instBEqWire.beq]

@[simp]
theorem wire_beq_self (w : Wire) : (w == w) = true := by
  rw [wire_beq_unfold]; exact beq_self_eq_true w.name

theorem wire_beq_ne (w1 w2 : Wire) (h : w1 ≠ w2) : (w1 == w2) = false := by
  rw [wire_beq_unfold]
  apply beq_eq_false_iff_ne.mpr
  intro heq; exact h (by cases w1; cases w2; simp_all)

theorem wire_beq_eq (w1 w2 : Wire) : (w1 == w2) = true → w1 = w2 := by
  rw [wire_beq_unfold]
  intro h
  have := (beq_iff_eq (α := String)).mp h
  cases w1; cases w2; simp_all

/-- Association-list map from wires to Bool, with default `false`. -/
abbrev WireMap := List (Wire × Bool)

namespace WireMap

/-- Look up a wire in the map. Returns `false` if not found (matching `mkEnv` default). -/
def lookup (m : WireMap) (w : Wire) : Bool :=
  match m.find? (fun p => p.1 == w) with
  | some (_, v) => v
  | none => false

/-- Insert a wire-value binding (prepend, so latest shadows earlier). -/
def insert (m : WireMap) (w : Wire) (v : Bool) : WireMap :=
  (w, v) :: m

/-- Convert a WireMap to an Env function. -/
def toEnv (m : WireMap) : Env :=
  fun w => m.lookup w

-- Core lemmas

@[simp]
theorem lookup_insert_eq (m : WireMap) (w : Wire) (v : Bool) :
    (m.insert w v).lookup w = v := by
  simp [insert, lookup, wire_beq_self]

@[simp]
theorem lookup_insert_ne (m : WireMap) (w w' : Wire) (v : Bool) (h : w' ≠ w) :
    (m.insert w v).lookup w' = m.lookup w' := by
  have hbeq : (w == w') = false := wire_beq_ne w w' (Ne.symm h)
  simp [insert, lookup, hbeq]

/-- The toEnv of an insert matches updateEnv of toEnv. -/
theorem toEnv_insert (m : WireMap) (w : Wire) (v : Bool) :
    (m.insert w v).toEnv = updateEnv m.toEnv w v := by
  funext w'
  simp only [toEnv, updateEnv]
  by_cases h : w' = w
  · subst h; simp [wire_beq_self, lookup_insert_eq]
  · simp [wire_beq_ne w' w h, lookup_insert_ne m w w' v h]

/-- WireMap.lookup agrees with mkEnv on the same bindings. -/
theorem lookup_eq_mkEnv (bindings : WireMap) (w : Wire) :
    bindings.lookup w = mkEnv bindings w := by
  rfl

end WireMap

end Shoumei.Reflection
