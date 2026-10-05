/-
HDL/Expr.lean - Combinators and Operators for High-Level Signals

Provides expression combinators:
- Relational comparators: equality, inequality, unsigned order
- N-way multiplexers: priority mux, case selection
- Bit-reduction operators: AND-reduce, OR-reduce, parity XOR-reduce
- Bit-manipulation operators: static shifts, replication, sign extension
-/

import Shoumei.HDL.Types

namespace Shoumei.HDL

namespace Signal

/-- Inequality comparison (returns 1-bit boolean signal). -/
def ne (a b : Signal w) : Signal 1 :=
  ~~~(.eq a b)

/-- Unsigned greater-than comparison. -/
def ugt (a b : Signal w) : Signal 1 :=
  .ult b a

/-- Unsigned less-than-or-equal comparison. -/
def ule (a b : Signal w) : Signal 1 :=
  ~~~(ugt a b)

/-- Unsigned greater-than-or-equal comparison. -/
def uge (a b : Signal w) : Signal 1 :=
  ~~~(.ult a b)

/-- Multiplex between two signals based on a 1-bit condition. -/
def mux2 (sel : Signal 1) (thenSig elseSig : Signal w) : Signal w :=
  .mux sel thenSig elseSig

/-- Priority case multiplexer.
    Evaluates condition-value pairs from head to tail.
    Falls back to `defaultSig` when no condition holds. -/
def muxCase (defaultSig : Signal w) (cases : List (Signal 1 × Signal w)) : Signal w :=
  cases.foldr (fun (cond, val) acc => .mux cond val acc) defaultSig

/-- Static logical shift left by `amt` positions. -/
def shl (amt : Nat) (s : Signal w) : Signal w :=
  if h : amt = 0 then
    s
  else if hle : w ≤ amt then
    zero w
  else
    let keepWidth := w - amt
    have hlt : amt < w := Nat.not_le.mp hle
    have hsub : w - 1 - amt - 0 + 1 = keepWidth := by omega
    let kept : Signal keepWidth := hsub ▸ .extract s (w - 1 - amt) 0
    let zeros : Signal amt := zero amt
    have hconcat : keepWidth + amt = w := by omega
    hconcat ▸ .concat kept zeros

/-- Static logical shift right by `amt` positions. -/
def lshr (amt : Nat) (s : Signal w) : Signal w :=
  if h : amt = 0 then
    s
  else if hle : w ≤ amt then
    zero w
  else
    let keepWidth := w - amt
    have hlt : amt < w := Nat.not_le.mp hle
    have hsub : w - 1 - amt + 1 = keepWidth := by omega
    let kept : Signal keepWidth := hsub ▸ .extract s (w - 1) amt
    let zeros : Signal amt := zero amt
    have hconcat : amt + keepWidth = w := by omega
    hconcat ▸ .concat zeros kept

/-- Replicate a 1-bit signal `n` times. -/
def replicate (n : Nat) (s : Signal 1) : Signal n :=
  match n with
  | 0 => .const (BitVec.ofNat 0 0)
  | 1 => s
  | n' + 1 =>
      have h : n' + 1 = 1 + n' := by omega
      h ▸ .concat s (replicate n' s)

/-- Sign-extend a signal of width `w` to a wider width `w'`. -/
def signExtend (w' : Nat) (h : w ≤ w') (s : Signal w) (hw : 0 < w) : Signal w' :=
  if heq : w = w' then
    heq ▸ s
  else
    let sign := signBit s hw
    let padWidth := w' - w
    let signPad : Signal padWidth := replicate padWidth sign
    have hconcat : padWidth + w = w' := Nat.sub_add_cancel h
    hconcat ▸ .concat signPad s

/-- Reduce a signal to 1 bit through bitwise OR (returns 1 if any bit is high). -/
def orReduce (s : Signal w) : Signal 1 :=
  ne s (zero w)

/-- Reduce a signal to 1 bit through bitwise AND (returns 1 if all bits are high). -/
def andReduce (s : Signal w) : Signal 1 :=
  .eq s (~~~(zero w))

end Signal

end Shoumei.HDL
