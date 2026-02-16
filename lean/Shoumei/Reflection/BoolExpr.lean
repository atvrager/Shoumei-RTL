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
  deriving Repr, BEq, Inhabited, DecidableEq

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

end BoolExpr

end Shoumei.Reflection
