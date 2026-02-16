/-
Reflection/BoolExpr.lean - Symbolic Boolean expression type

BoolExpr represents Boolean expressions as trees, enabling symbolic
evaluation of circuits. The `eval` function interprets expressions
given a variable assignment.
-/

import Shoumei.DSL

namespace Shoumei.Reflection

/-- Symbolic Boolean expression tree. -/
inductive BoolExpr where
  | lit (b : Bool)
  | var (idx : Nat)
  | and (l r : BoolExpr)
  | or (l r : BoolExpr)
  | not (e : BoolExpr)
  | xor (l r : BoolExpr)
  | ite (s t f : BoolExpr)
  deriving Repr, BEq, Inhabited, DecidableEq, Hashable

namespace BoolExpr

/-- Evaluate a BoolExpr under a variable assignment. -/
def eval (assign : Nat → Bool) : BoolExpr → Bool
  | .lit b => b
  | .var i => assign i
  | .and l r => l.eval assign && r.eval assign
  | .or l r => l.eval assign || r.eval assign
  | .not e => !(e.eval assign)
  | .xor l r => Bool.xor (l.eval assign) (r.eval assign)
  | .ite s t f => if s.eval assign then t.eval assign else f.eval assign

/-- Constant-fold: eliminate lit-controlled MUX/and/or/not/xor nodes. -/
def constFold : BoolExpr → BoolExpr
  | .lit b => .lit b
  | .var i => .var i
  | .and l r =>
    match l.constFold, r.constFold with
    | .lit true, r' => r'
    | l', .lit true => l'
    | .lit false, _ => .lit false
    | _, .lit false => .lit false
    | l', r' => .and l' r'
  | .or l r =>
    match l.constFold, r.constFold with
    | .lit true, _ => .lit true
    | _, .lit true => .lit true
    | .lit false, r' => r'
    | l', .lit false => l'
    | l', r' => .or l' r'
  | .not e =>
    match e.constFold with
    | .lit b => .lit (!b)
    | e' => .not e'
  | .xor l r =>
    match l.constFold, r.constFold with
    | .lit false, r' => r'
    | l', .lit false => l'
    | .lit true, r' => .not r'
    | l', .lit true => .not l'
    | l', r' => .xor l' r'
  | .ite s t f =>
    match s.constFold with
    | .lit true => t.constFold
    | .lit false => f.constFold
    | s' => .ite s' t.constFold f.constFold

theorem constFold_correct (e : BoolExpr) (assign : Nat → Bool) :
    e.constFold.eval assign = e.eval assign := by
  induction e with
  | lit b => simp [constFold, eval]
  | var i => simp [constFold, eval]
  | and l r ihl ihr =>
    simp only [constFold]
    split <;> simp_all [eval]
  | or l r ihl ihr =>
    simp only [constFold]
    split <;> simp_all [eval]
  | not e ih =>
    simp only [constFold]
    split <;> simp_all [eval]
  | xor l r ihl ihr =>
    simp only [constFold]
    split <;> simp_all [eval, Bool.xor]
  | ite s t f ihs iht ihf =>
    simp only [constFold]
    split <;> simp_all [eval]

/-- Substitute a variable with a literal value. -/
def substVar (e : BoolExpr) (idx : Nat) (val : Bool) : BoolExpr :=
  match e with
  | .lit b => .lit b
  | .var i => if i == idx then .lit val else .var i
  | .and l r => .and (l.substVar idx val) (r.substVar idx val)
  | .or l r => .or (l.substVar idx val) (r.substVar idx val)
  | .not e => .not (e.substVar idx val)
  | .xor l r => .xor (l.substVar idx val) (r.substVar idx val)
  | .ite s t f => .ite (s.substVar idx val) (t.substVar idx val) (f.substVar idx val)

theorem substVar_eval (e : BoolExpr) (idx : Nat) (val : Bool) (assign : Nat → Bool) :
    (e.substVar idx val).eval assign = e.eval (fun i => if i == idx then val else assign i) := by
  induction e with
  | lit => simp [substVar, eval]
  | var i =>
    simp only [substVar]
    split <;> simp_all [eval]
  | and _ _ ihl ihr => simp [substVar, eval, ihl, ihr]
  | or _ _ ihl ihr => simp [substVar, eval, ihl, ihr]
  | not _ ih => simp [substVar, eval, ih]
  | xor _ _ ihl ihr => simp [substVar, eval, ihl, ihr]
  | ite _ _ _ ihs iht ihf =>
    simp only [substVar, eval, ihs]
    split <;> simp_all

/-- Semantic equivalence check via Shannon expansion with constFold pruning.
    Early-out when constFolded forms are structurally equal. -/
def beqSem (e1 e2 : BoolExpr) : List Nat → Bool
  | [] => decide (e1.constFold = e2.constFold)
  | v :: vs =>
    if decide (e1.constFold = e2.constFold) then true
    else
      beqSem ((e1.substVar v true).constFold) ((e2.substVar v true).constFold) vs &&
      beqSem ((e1.substVar v false).constFold) ((e2.substVar v false).constFold) vs

-- Memoized implementation for native_decide performance.
-- Uses Array-based cache to avoid exponential recomputation of identical sub-problems.
private unsafe def beqSemImpl (e1 e2 : BoolExpr) (vars : List Nat) : Bool :=
  (go e1 e2 vars #[]).1
where
  go (e1 e2 : BoolExpr) (vars : List Nat)
     (cache : Array (UInt64 × UInt64 × Nat × Bool))
     : Bool × Array (UInt64 × UInt64 × Nat × Bool) :=
    let e1c := e1.constFold
    let e2c := e2.constFold
    if e1c == e2c then (true, cache)
    else
      let h1 := hash e1c
      let h2 := hash e2c
      let depth := vars.length
      -- Check cache (hash + depth as key, verify with BEq on collision)
      let cached := cache.foldl (init := none) fun acc (ch1, ch2, cd, cr) =>
        match acc with
        | some _ => acc
        | none => if ch1 == h1 && ch2 == h2 && cd == depth then some cr else none
      match cached with
      | some result => (result, cache)
      | none =>
        match vars with
        | [] =>
          (false, cache.push (h1, h2, depth, false))
        | v :: vs =>
          let (r1, c1) := go (e1c.substVar v true).constFold (e2c.substVar v true).constFold vs cache
          if !r1 then (false, c1.push (h1, h2, depth, false))
          else
            let (r2, c2) := go (e1c.substVar v false).constFold (e2c.substVar v false).constFold vs c1
            (r2, c2.push (h1, h2, depth, r2))

attribute [implemented_by beqSemImpl] beqSem

private theorem eval_substVar_self (e : BoolExpr) (v : Nat) (assign : Nat → Bool) :
    (e.substVar v (assign v)).eval assign = e.eval assign := by
  rw [substVar_eval]; congr 1; funext i
  by_cases h : i = v <;> simp [h]

theorem beqSem_correct (e1 e2 : BoolExpr) (vars : List Nat)
    (h : beqSem e1 e2 vars = true) (assign : Nat → Bool) :
    e1.eval assign = e2.eval assign := by
  induction vars generalizing e1 e2 with
  | nil =>
    simp only [beqSem, decide_eq_true_eq] at h
    rw [← constFold_correct e1 assign, ← constFold_correct e2 assign, h]
  | cons v vs ih =>
    simp only [beqSem] at h
    split at h
    · -- Early-out: constFolded forms are structurally equal
      rename_i heq
      simp only [decide_eq_true_eq] at heq
      rw [← constFold_correct e1 assign, ← constFold_correct e2 assign, heq]
    · -- Shannon expansion
      simp only [Bool.and_eq_true] at h
      rw [← eval_substVar_self e1 v assign, ← eval_substVar_self e2 v assign]
      cases hv : assign v
      · have := ih _ _ h.2
        rwa [constFold_correct, constFold_correct] at this
      · have := ih _ _ h.1
        rwa [constFold_correct, constFold_correct] at this

end BoolExpr

end Shoumei.Reflection
