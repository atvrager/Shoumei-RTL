/-
HDL/Types.lean - Typed Hardware Signals for High-Level RTL DSL

Provides strongly typed bit-vector signal AST. Each signal carries
a bit width `w : Nat`. The Lean type checker enforces bit width
consistency by construction.
-/

import Shoumei.DSL

namespace Shoumei.HDL

open Shoumei

/-- Typed hardware signal representation.
    Bit width `w : Nat` indexes each signal. -/
inductive Signal : Nat → Type where
  /-- Constant bit-vector literal. -/
  | const (val : BitVec w) : Signal w
  /-- Input port reference with explicit name and width. -/
  | input (name : String) (w : Nat) : Signal w
  /-- Internal named wire binding. -/
  | wire (name : String) (w : Nat) : Signal w
  /-- Sequential register with clock, reset, initial value, and next signal. -/
  | reg (name : String) (w : Nat) (clock : Wire) (reset : Wire)
        (init : BitVec w) (next : Signal w) : Signal w
  /-- Bit-range extraction from `hi` down to `lo`. -/
  | extract (src : Signal srcW) (hi : Nat) (lo : Nat) : Signal (hi - lo + 1)
  /-- Concatenation of two bit-vectors. -/
  | concat (a : Signal w1) (b : Signal w2) : Signal (w1 + w2)
  /-- Bitwise NOT / Inversion. -/
  | not (a : Signal w) : Signal w
  /-- Bitwise AND. -/
  | and (a b : Signal w) : Signal w
  /-- Bitwise OR. -/
  | or (a b : Signal w) : Signal w
  /-- Bitwise XOR. -/
  | xor (a b : Signal w) : Signal w
  /-- Modular addition. -/
  | add (a b : Signal w) : Signal w
  /-- Modular subtraction. -/
  | sub (a b : Signal w) : Signal w
  /-- Full-width unsigned multiplication. -/
  | mul (a : Signal w1) (b : Signal w2) : Signal (w1 + w2)
  /-- 2-to-1 Multiplexer with 1-bit selector. -/
  | mux (sel : Signal 1) (thenSig elseSig : Signal w) : Signal w
  /-- Equality comparison (returns 1-bit boolean signal). -/
  | eq (a b : Signal srcW) : Signal 1
  /-- Unsigned less-than comparison (returns 1-bit boolean signal). -/
  | ult (a b : Signal srcW) : Signal 1
  /-- Submodule output port reference. -/
  | instOut (instName : String) (portName : String) (w : Nat) : Signal w

/-- Convenience alias for single-bit boolean signals. -/
abbrev SignalBool := Signal 1

namespace Signal

/-- Zero constant signal of width `w`. -/
def zero (w : Nat) : Signal w :=
  .const (BitVec.ofNat w 0)

/-- Single-bit boolean true. -/
def true1 : Signal 1 :=
  .const (BitVec.ofNat 1 1)

/-- Single-bit boolean false. -/
def false1 : Signal 1 :=
  .const (BitVec.ofNat 1 0)

/-- Register constructor with default zero initialization. -/
def register (name : String) (clock reset : Wire) (next : Signal w)
    (init : BitVec w := BitVec.ofNat w 0) : Signal w :=
  .reg name w clock reset init next

/-- Zero-extend a signal to width `w'`.
    Requires `w ≤ w'`. -/
def zeroExtend (w' : Nat) (h : w ≤ w') (s : Signal w) : Signal w' :=
  if hw : w = w' then
    hw ▸ s
  else
    let padWidth := w' - w
    let zeros : Signal padWidth := zero padWidth
    have hconcat : padWidth + w = w' := Nat.sub_add_cancel h
    hconcat ▸ .concat zeros s

/-- Sign-extend a signal to width `w'`.
    Extracts the sign bit and replicates it across the upper bits. -/
def signBit (s : Signal w) (h : 0 < w) : Signal 1 :=
  have hidx : w - 1 - (w - 1) + 1 = 1 := by omega
  hidx ▸ .extract s (w - 1) (w - 1)

instance : HAdd (Signal w) (Signal w) (Signal w) where
  hAdd a b := .add a b

instance : HSub (Signal w) (Signal w) (Signal w) where
  hSub a b := .sub a b

instance : HAnd (Signal w) (Signal w) (Signal w) where
  hAnd a b := .and a b

instance : HOr (Signal w) (Signal w) (Signal w) where
  hOr a b := .or a b

instance : HXor (Signal w) (Signal w) (Signal w) where
  hXor a b := .xor a b

instance : Complement (Signal w) where
  complement a := .not a

end Signal

end Shoumei.HDL
