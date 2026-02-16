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

end BoolExpr

end Shoumei.Reflection
