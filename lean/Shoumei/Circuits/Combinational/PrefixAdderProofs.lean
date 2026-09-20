/-
Circuits/Combinational/PrefixAdderProofs.lean - Parallel-prefix adder correctness

Two layers:

1. **Network algebra** (`prefixNetwork_correct`).  A prefix cell merges the
   group (generate, propagate) pair of two adjacent bit ranges.  `grpGen` /
   `grpProp` give the group meaning of a range; `grpGen_split` shows the merge
   is exactly the group of the union.  A network whose final span map gives
   every bit the full range `[0, i]` therefore computes the true prefix
   carries.  This is the load-bearing argument and it covers *every* tree and
   width uniformly.

2. **Gate-level realization**.  `mkPrefixAdd` emits one gate per network
   operation, so the same network is realized; the exhaustive checks at the
   bottom pin that realization against Nat arithmetic for the small widths
   (`native_decide` over all inputs).  Wider widths are additionally checked by
   the Yosys LEC (`verification/techmap-equiv.sh`) and RISC-V cosimulation.
-/

import Shoumei.Circuits.Combinational.PrefixAdder
import Shoumei.Circuits.Combinational.CarrySelectAdder
import Shoumei.Semantics
import Shoumei.Reflection.CompileCircuit
import Std.Data.HashMap

namespace Shoumei.Circuits.Combinational

open Shoumei
open Shoumei.Reflection
open Shoumei.Components

/-! ## Group generate / propagate

`grpGen gg pp lo len` is the group generate of bits `[lo, lo+len)`, combining
from the MSB down: `G = g_hi ∨ (p_hi ∧ G_lower)`.  `grpProp` is the AND of the
propagate bits on the same range (true on an empty range). -/

def grpProp (pp : Nat → Bool) : Nat → Nat → Bool
  | _, 0 => true
  | lo, len + 1 => pp (lo + len) && grpProp pp lo len

def grpGen (gg pp : Nat → Bool) : Nat → Nat → Bool
  | _, 0 => false
  | lo, len + 1 => gg (lo + len) || (pp (lo + len) && grpGen gg pp lo len)

theorem grpGen_one (gg pp : Nat → Bool) (lo : Nat) : grpGen gg pp lo 1 = gg lo := by
  simp [grpGen]

theorem grpProp_one (pp : Nat → Bool) (lo : Nat) : grpProp pp lo 1 = pp lo := by
  simp [grpProp]

/-- The prefix merge identity, abstracted so it can be discharged by cases. -/
theorem bool_merge (g p b c d : Bool) :
    (g || (p && (b || (c && d)))) = ((g || (p && b)) || ((p && c) && d)) := by
  cases g <;> cases p <;> cases b <;> cases c <;> cases d <;> rfl

/-- Group generate splits at a point: the upper range combined onto the lower
    range's group.  This is the algebraic content of one prefix merge cell. -/
theorem grpGen_split (gg pp : Nat → Bool) (lo a b : Nat) :
    grpGen gg pp lo (a + b)
      = (grpGen gg pp (lo + a) b || (grpProp pp (lo + a) b && grpGen gg pp lo a)) := by
  induction b with
  | zero => simp only [Nat.add_zero, grpGen, grpProp, Bool.true_and, Bool.false_or]
  | succ b ih =>
      rw [Nat.add_succ]
      simp only [grpGen, grpProp]
      rw [ih, Nat.add_assoc]
      exact bool_merge _ _ _ _ _

theorem grpProp_split (pp : Nat → Bool) (lo a b : Nat) :
    grpProp pp lo (a + b) = (grpProp pp (lo + a) b && grpProp pp lo a) := by
  induction b with
  | zero => rfl
  | succ b ih =>
      rw [Nat.add_succ]
      simp only [grpProp]
      rw [ih, Nat.add_assoc, Bool.and_assoc]

/-! ## Network value model

`NetVal` carries the span map plus the per-bit (g, p) wires.  `netStep` applies
one level atomically (each cell reads the previous level's values), exactly
mirroring `applyLevel`'s spans.  `Inv` is the invariant that bit `i`'s wires
hold the group of its current span `[start, i]`. -/

structure NetVal where
  spans : Nat → Nat × Nat
  g     : Nat → Bool
  p     : Nat → Bool

def netInit (gg pp : Nat → Bool) : NetVal :=
  { spans := initSpans, g := gg, p := pp }

def netStep (st : NetVal) (cells : List (Nat × Nat)) : Option NetVal :=
  if cells.any (fun c => !cellLegal st.spans c.1 c.2) then none
  else
    some
      { spans := fun j =>
          match cells.find? (fun c => c.1 == j) with
          | some c => ((st.spans c.2).1, j)
          | none => st.spans j
        g := fun j =>
          match cells.find? (fun c => c.1 == j) with
          | some c => st.g j || (st.p j && st.g c.2)
          | none => st.g j
        p := fun j =>
          match cells.find? (fun c => c.1 == j) with
          | some c => st.p j && st.p c.2
          | none => st.p j }

/-- Bit `i`'s span ends at `i` and starts at or below it, and its (g, p) wires
    are the group of `[start, i]`. -/
def Inv (gg pp : Nat → Bool) (st : NetVal) : Prop :=
  ∀ i, (st.spans i).2 = i ∧ (st.spans i).1 ≤ i ∧
       st.g i = grpGen gg pp (st.spans i).1 (i + 1 - (st.spans i).1) ∧
       st.p i = grpProp pp (st.spans i).1 (i + 1 - (st.spans i).1)

theorem netInit_inv (gg pp : Nat → Bool) : Inv gg pp (netInit gg pp) := by
  intro i
  refine ⟨rfl, Nat.le_refl i, ?_, ?_⟩
  · simp only [netInit, initSpans, Nat.add_sub_cancel_left, grpGen_one]
  · simp only [netInit, initSpans, Nat.add_sub_cancel_left, grpProp_one]

/-- One level preserves the invariant. -/
theorem netStep_inv (gg pp : Nat → Bool) (st st' : NetVal) (cells : List (Nat × Nat))
    (h : Inv gg pp st) (hstep : netStep st cells = some st') : Inv gg pp st' := by
  rw [netStep] at hstep
  split at hstep
  · simp at hstep
  next hcond =>
    simp only [Option.some.injEq] at hstep
    subst hstep
    have hlegal : ∀ c ∈ cells, cellLegal st.spans c.1 c.2 = true := by
      have hnot : cells.any (fun c => !cellLegal st.spans c.1 c.2) = false := by
        cases hh : cells.any (fun c => !cellLegal st.spans c.1 c.2) <;> simp_all
      rw [List.any_eq_false] at hnot
      intro c hc
      have := hnot c hc
      simpa using this
    intro i
    obtain ⟨hs2, hle, hg, hp⟩ := h i
    cases hf : cells.find? (fun c => c.1 == i) with
    | none =>
        refine ⟨by simp only [hf]; exact hs2, by simp only [hf]; exact hle,
                by simp only [hf]; exact hg, by simp only [hf]; exact hp⟩
    | some c =>
        have hc1 : c.1 = i := by
          have := List.find?_some hf
          simpa using this
        have hcmem : c ∈ cells := List.mem_of_find?_eq_some hf
        have hleg := hlegal c hcmem
        obtain ⟨hc2, hcle, hcg, hcp⟩ := h c.2
        simp only [cellLegal, Bool.and_eq_true, decide_eq_true_eq] at hleg
        obtain ⟨hlt, hadj⟩ := hleg
        have hlt' : c.2 < i := by rw [← hc1]; exact hlt
        have hsi1 : (st.spans i).1 = c.2 + 1 := by rw [← hc1, hadj, hc2]
        have hidx : i + 1 - (c.2 + 1) = i - c.2 := by omega
        have ha : c.2 + 1 - (st.spans c.2).1 + (i - c.2) = i + 1 - (st.spans c.2).1 := by
          omega
        have hb : (st.spans c.2).1 + (c.2 + 1 - (st.spans c.2).1) = c.2 + 1 := by
          omega
        refine ⟨?_, ?_, ?_, ?_⟩
        · simp only [hf]
        · simp only [hf]; omega
        · simp only [hf, hg, hp, hcg, hsi1, hidx]
          rw [← ha, grpGen_split, hb]
        · simp only [hf, hp, hcp, hsi1, hidx]
          rw [← ha, grpProp_split, hb]

/-! ## Network fold and Lemma A -/

def netFold (gg pp : Nat → Bool) (levels : List (List (Nat × Nat))) : Option NetVal :=
  levels.foldl (fun acc lvl => acc.bind (fun st => netStep st lvl)) (some (netInit gg pp))

theorem netStep_spans (st : NetVal) (cells : List (Nat × Nat)) :
    (netStep st cells).map (·.spans) = applyLevel st.spans cells := by
  simp only [netStep, applyLevel]
  split <;> rfl

/-- A fold that `bind`s through an `Option` accumulator starting from `none`
    never recovers. -/
theorem foldl_bind_none {α β : Type} (g : α → β → Option α) (rest : List β) :
    List.foldl (fun acc x => acc.bind (fun a => g a x)) none rest = none := by
  induction rest with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons, Option.bind_none]; exact ih

/-- The value fold's span map is the span-only fold. -/
theorem fold_spans_from (st0 : NetVal) (levels : List (List (Nat × Nat))) :
    (levels.foldl (fun acc lvl => acc.bind (fun st => netStep st lvl)) (some st0)).map (·.spans)
      = spanFoldFrom st0.spans levels := by
  induction levels generalizing st0 with
  | nil => rfl
  | cons lvl rest ih =>
      simp only [spanFoldFrom, List.foldl, Option.bind_some]
      cases hst : netStep st0 lvl with
      | none =>
          have hsp : applyLevel st0.spans lvl = none := by
            have := netStep_spans st0 lvl
            simp only [hst, Option.map_none] at this
            exact this.symm
          rw [hsp, foldl_bind_none, foldl_bind_none]
          rfl
      | some st =>
          have hsp : applyLevel st0.spans lvl = some st.spans := by
            have := netStep_spans st0 lvl
            simp only [hst, Option.map_some] at this
            exact this.symm
          rw [hsp]
          simpa only [spanFoldFrom] using ih st

theorem netFold_spans (gg pp : Nat → Bool) (levels : List (List (Nat × Nat))) :
    (netFold gg pp levels).map (·.spans) = spanFold levels := by
  have := fold_spans_from (netInit gg pp) levels
  simpa only [netFold, spanFold, netInit, spanFoldFrom] using this

/-- The value fold preserves the invariant. -/
theorem fold_inv_from (gg pp : Nat → Bool) (st0 : NetVal) (h0 : Inv gg pp st0)
    (levels : List (List (Nat × Nat))) :
    ∀ st, levels.foldl (fun acc lvl => acc.bind (fun st => netStep st lvl)) (some st0) = some st →
      Inv gg pp st := by
  induction levels generalizing st0 with
  | nil =>
      intro st h
      simp only [List.foldl, Option.some.injEq] at h
      subst h; exact h0
  | cons lvl rest ih =>
      intro st h
      simp only [List.foldl] at h
      cases hst : netStep st0 lvl with
      | none =>
          rw [Option.bind_some, hst, foldl_bind_none] at h
          exact absurd h (by simp)
      | some st1 =>
          rw [Option.bind_some, hst] at h
          exact ih st1 (netStep_inv gg pp st0 st1 lvl h0 hst) st h

theorem netFold_inv (gg pp : Nat → Bool) (levels : List (List (Nat × Nat))) :
    ∀ st, netFold gg pp levels = some st → Inv gg pp st :=
  fold_inv_from gg pp (netInit gg pp) (netInit_inv gg pp) levels

/-- **Lemma A.**  A valid network's final wires hold the full-prefix group of
    each bit: bit `i`'s generate is `G[0..i]` and its propagate is `P[0..i]`. -/
theorem prefixNetwork_correct (gg pp : Nat → Bool) (levels : List (List (Nat × Nat)))
    (width : Nat) (st : NetVal)
    (hval : validPrefixNetwork levels width = true) (hfold : netFold gg pp levels = some st) :
    ∀ i, i < width →
      st.g i = grpGen gg pp 0 (i + 1) ∧ st.p i = grpProp pp 0 (i + 1) := by
  have hinv := netFold_inv gg pp levels st hfold
  have hspans : spanFold levels = some st.spans := by
    rw [← netFold_spans gg pp levels, hfold]; rfl
  have hall : (List.range width).all (fun i => decide (st.spans i = (0, i))) = true := by
    unfold validPrefixNetwork at hval
    rw [hspans] at hval
    simpa using hval
  intro i hi
  have hsi : st.spans i = (0, i) := by
    have := (List.all_eq_true.mp hall) i (List.mem_range.mpr hi)
    simpa using this
  obtain ⟨_, _, hg, hp⟩ := hinv i
  rw [hsi] at hg hp
  exact ⟨hg, hp⟩

/-! ## Lemma B -- every selectable network is valid

The selector only offers a tree at a width when `validPrefixNetwork` holds, so
the networks below are exactly those that can be emitted. -/

def coveredNetworks : List (PrefixTree × Nat) :=
  (([8, 16, 32, 64].map (fun w => (PrefixTree.rippleCarry, w)))
   ++ ([8, 16, 32, 64].map (fun w => (PrefixTree.brentKung, w)))
   ++ ([8, 16, 23, 32, 52, 64, 106].map (fun w => (PrefixTree.sklansky, w)))
   ++ ([8, 16, 23, 32, 52, 64, 106].map (fun w => (PrefixTree.hanCarlson, w)))
   ++ ([8, 16, 23, 32, 52, 64, 106].map (fun w => (PrefixTree.koggeStone, w))))

/-- **Lemma B.**  Every network the selector can offer forms a valid
    full-prefix network at its width. -/
theorem prefixLevels_valid :
    coveredNetworks.all (fun p => validPrefixNetwork (prefixLevels p.1 p.2) p.2) = true := by
  native_decide

/-! ## Gate-level realization

`mkPrefixAdd` emits one gate per network operation; the checks below pin the
realized gates against Nat arithmetic over *all* inputs at the small widths.
`one`/`zero` are the constant wires the SV emitter renders as `1'b1`/`1'b0`. -/

def bitsToNat (bs : List Bool) : Nat :=
  (bs.enum.map (fun (i, b) => if b then 2 ^ i else 0)).foldl (· + ·) 0

/-- A gate list compiled to integer wire indices, so exhaustive evaluation runs
    on `Array` accesses instead of string-keyed lookups. -/
structure EvalPlan where
  ops    : Array (GateType × List Nat × Nat)
  size   : Nat
  cinIdx : Option Nat
  oneIdx : Nat
  sumIdx : List Nat

/-- Wire indices are laid out as `a_i` = i, `b_i` = width+i, then `cin`, `one`,
    `zero`, then one index per gate output in order. -/
def buildEvalPlan (c : Circuit) (width : Nat) : EvalPlan := Id.run do
  let hasCin := c.inputs.any (fun w => w.name == "cin")
  let cinBase := 2 * width
  let oneIdx := cinBase + (if hasCin then 1 else 0)
  let mut idx : Std.HashMap String Nat := {}
  for i in List.range width do
    idx := idx.insert s!"a_{i}" i
    idx := idx.insert s!"b_{i}" (width + i)
  if hasCin then idx := idx.insert "cin" cinBase
  idx := idx.insert "one" oneIdx
  idx := idx.insert "zero" (oneIdx + 1)
  let mut next := oneIdx + 2
  let mut ops : Array (GateType × List Nat × Nat) := #[]
  for g in c.gates do
    let oi := next
    idx := idx.insert g.output.name oi
    next := next + 1
    ops := ops.push (g.gateType, g.inputs.map (fun w => idx.getD w.name 0), oi)
  let sumIdx := (List.range width).map (fun i => idx.getD s!"sum_{i}" 0)
  return { ops, size := next, cinIdx := if hasCin then some cinBase else none, oneIdx, sumIdx }

/-- Evaluate one gate against an `Array` of wire values. -/
def evalOp (arr : Array Bool) (op : GateType) (ins : List Nat) : Bool :=
  let v (k : Nat) := arr.getD k false
  match op with
  | .AND => match ins with | [i0, i1] => v i0 && v i1 | _ => false
  | .OR  => match ins with | [i0, i1] => v i0 || v i1 | _ => false
  | .NOT => match ins with | [i0] => !(v i0) | _ => false
  | .XOR => match ins with | [i0, i1] => xor (v i0) (v i1) | _ => false
  | .BUF => match ins with | [i0] => v i0 | _ => false
  | .MUX => match ins with | [i0, i1, sel] => if v sel then v i1 else v i0 | _ => false
  | .DFF | .DFF_SET => false

def runPlan (p : EvalPlan) (width : Nat) (cin : Bool) (a b : Nat) : Nat := Id.run do
  let mut arr := Array.replicate p.size false
  for i in List.range width do
    arr := arr.set! i (((a >>> i) &&& 1) == 1)
    arr := arr.set! (width + i) (((b >>> i) &&& 1) == 1)
  if let some ci := p.cinIdx then arr := arr.set! ci cin
  arr := arr.set! p.oneIdx true
  for (op, ins, out) in p.ops do
    arr := arr.set! out (evalOp arr op ins)
  return bitsToNat (p.sumIdx.map (fun k => arr.getD k false))

/-- Expected sum for a carry mode and carry-in value. -/
def expectedSum (cin : CinMode) (ci : Bool) (a b : Nat) : Nat :=
  a + b + (match cin with
           | .one   => 1
           | .input => if ci then 1 else 0
           | .none  => 0)

def checkPlan (c : Circuit) (width : Nat) (cin : CinMode) : Bool :=
  let p := buildEvalPlan c width
  (List.range (2 ^ width)).all fun a =>
    (List.range (2 ^ width)).all fun b =>
      (match cin with | .input => [false, true] | _ => [false]).all fun ci =>
        runPlan p width ci a b == expectedSum cin ci a b % 2 ^ width

/-- Exhaustively compare a prefix adder's gates against Nat arithmetic. -/
def checkPrefixAdder (tree : PrefixTree) (width : Nat) (cin : CinMode) : Bool :=
  checkPlan (mkPrefixAdderCircuit tree width cin) width cin

def checkCarrySelect (width : Nat) (cin : CinMode) : Bool :=
  checkPlan (mkCarrySelectAdderCircuit width cin) width cin

def allTrees : List PrefixTree :=
  [.rippleCarry, .brentKung, .sklansky, .hanCarlson, .koggeStone]

def allCins : List CinMode := [.none, .input, .one]

/-- Exhaustive gate-level correctness at width 4 (all trees, all carry modes)
    and width 8 (all trees, `none`/`input`), plus carry-select at width 8. -/
theorem prefixAdder_gates_correct :
    (allTrees.all (fun t => allCins.all (fun ci => checkPrefixAdder t 4 ci)))
    && (allTrees.all (fun t => [CinMode.none, CinMode.input].all (fun ci =>
          checkPrefixAdder t 8 ci)))
    && ([CinMode.none, CinMode.input].all (fun ci => checkCarrySelect 8 ci)) = true := by
  native_decide

end Shoumei.Circuits.Combinational