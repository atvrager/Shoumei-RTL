/-
Circuits/Sequential/FPNormalize.lean - Operand normalization primitives

A nonzero subnormal operand has no implicit leading one: its fraction is
small and its exponent field is zero.  Before an arithmetic unit that
assumes two significands in [1, 2) sees it, the fraction must be shifted
up until its leading one reaches the implicit position and the exponent
lowered by the same shift.

  fraction  0...0 1 x x x        exponent field 0  (subnormal)
                   |               |
                   | shift left by (width - pos)
                   v               v
  mantissa  1 x x x 0...0        effective exponent 1 - shift

Both primitives are pure gate builders shared by the multiplier and the
dividers, so the leading-one detector and the shifter exist once.
-/

import Shoumei.DSL

namespace Shoumei.Circuits.Sequential

open Shoumei

/-- Index of the highest set bit of a little-endian bit list, or zero when the
    list is zero.  Returns (position, gates); the position is `width` bits. -/
def mkLeadPos (pfx : String) (bits : List Wire) (zero_wire : Wire)
    (width : Nat) : List Wire × List Gate :=
  let n := bits.length
  let above := (List.range (n + 1)).map fun i => Wire.mk s!"{pfx}_ab{i}"
  let above_gates :=
    [Gate.mkBUF zero_wire (above[n]!)] ++
    ((List.range n).reverse.map fun i => Gate.mkOR (bits[i]!) (above[i + 1]!) (above[i]!))
  let lead := (List.range n).map fun i => Wire.mk s!"{pfx}_ld{i}"
  let lead_gates := (List.range n).flatMap fun i =>
    let na := Wire.mk s!"{pfx}_na{i}"
    [Gate.mkNOT (above[i + 1]!) na, Gate.mkAND (bits[i]!) na (lead[i]!)]
  -- The reduce is written out rather than reusing an OR tree: a `base_N` family
  -- name makes the code generator treat the chain as a bus and rewrite it, which
  -- is wrong for a filtered OR.  A `gx` suffix, as the adders use, is safe.
  let enc := (List.range width).map fun k =>
    let terms := (List.range n).filter (fun i => (i >>> k) &&& 1 == 1) |>.map (fun i => lead[i]!)
    match terms with
    | [] => (zero_wire, [])
    | t0 :: rest =>
      let (last, gs) := rest.enum.foldl (fun (acc : Wire × List Gate) (i, w) =>
        let o := Wire.mk s!"{pfx}b{k}gx{i}"
        (o, acc.2 ++ [Gate.mkOR acc.1 w o])) (t0, [])
      (last, gs)
  (enc.map Prod.fst, above_gates ++ lead_gates ++ (enc.map Prod.snd).flatten)

/-- OR-reduce a contiguous wire list. -/
private def mkOrChain (pfx : String) (wires : List Wire) : Wire × List Gate :=
  match wires with
  | [] => (Wire.mk s!"{pfx}_gnd", [])
  | w0 :: rest =>
    let (last, gates) := rest.foldl (fun (acc, gs) w =>
      let o := Wire.mk s!"{pfx}_{gs.length}"
      (o, gs ++ [Gate.mkOR acc w o])) (w0, [])
    (last, gates)

/-- Right barrel shifter that accumulates every bit shifted below position 0
    into `sticky_out`.  The caller must saturate the shift amount: only its low
    six bits are used, so an amount at or past the width must be forced to 63.
    Named apart from the dividers' private shifter of the same shape. -/
def mkShiftRightSticky (input : List Wire) (shift_amt : List Wire)
    (output : List Wire) (sticky_out : Wire) (zero_wire : Wire) (pfx : String) : List Gate :=
  let w := input.length
  let nlev := shift_amt.length          -- one level per bit of the amount
  let levels : List (List Wire) := (List.range (nlev + 1)).map fun level =>
    if level == 0 then input
    else (List.range w).map fun i => Wire.mk (pfx ++ "_l" ++ toString level ++ "_" ++ toString i)
  let stickies : List Wire := (List.range (nlev + 1)).map fun level => Wire.mk (pfx ++ "_stk_" ++
    toString level)
  let init_stk_gate := Gate.mkBUF zero_wire stickies[0]!
  let (mux_gates, stk_gates) := (List.range nlev).foldl (fun (acc : List Gate × List Gate) level =>
    let shift_by := 1 <<< level
    let prev := levels[level]!
    let curr := levels[level + 1]!
    let sel := shift_amt[level]!
    let prev_stk := stickies[level]!
    let curr_stk := stickies[level + 1]!
    let m_gates := (List.range w).map fun i =>
      let shifted := if i + shift_by < w then prev[i + shift_by]! else zero_wire
      Gate.mkMUX prev[i]! shifted sel curr[i]!
    let lost_bits := (List.range (min shift_by w)).map fun i => prev[i]!
    let (lost_or, lost_or_gates) := mkOrChain (pfx ++ "_lost_" ++ toString level) lost_bits
    let stk_c := Wire.mk (pfx ++ "_stkc_" ++ toString level)
    let s_gates := lost_or_gates ++ [
      Gate.mkAND sel lost_or stk_c,
      Gate.mkOR prev_stk stk_c curr_stk
    ]
    (acc.1 ++ m_gates, acc.2 ++ s_gates)
  ) ([], [init_stk_gate])
  let copy_gates := (List.range w).map fun i => Gate.mkBUF (levels[nlev]!)[i]! output[i]!
  mux_gates ++ stk_gates ++ copy_gates ++ [Gate.mkBUF stickies[nlev]! sticky_out]

/-- Barrel left shifter, one level per bit of the shift amount. -/
def mkBarrelShiftLeft (input : List Wire) (shift_amt : List Wire)
    (output : List Wire) (zero_wire : Wire) (pfx : String) : List Gate :=
  let w := input.length
  let nlev := shift_amt.length          -- one level per bit of the amount
  let levels : List (List Wire) := (List.range (nlev + 1)).map fun level =>
    if level == 0 then input
    else (List.range w).map fun i => Wire.mk (pfx ++ "_l" ++ toString level ++ "_" ++ toString i)
  let mux_gates := (List.range nlev).flatMap fun level =>
    let shift_by := 1 <<< level
    let prev := levels[level]!
    let curr := levels[level + 1]!
    let sel := shift_amt[level]!
    (List.range w).map fun i =>
      let unshifted := prev[i]!
      let shifted := if i >= shift_by then prev[i - shift_by]! else zero_wire
      Gate.mkMUX unshifted shifted sel curr[i]!
  let copy_gates := (List.range w).map fun i =>
    Gate.mkBUF (levels[nlev]!)[i]! output[i]!
  mux_gates ++ copy_gates

end Shoumei.Circuits.Sequential
