/-
Circuits/Combinational/Subtractor.lean - N-bit Subtractor using 2's Complement

A subtractor computes A - B using the identity:
  A - B = A + (~B) + 1  (2's complement)

Implementation strategy:
1. Invert all bits of B using NOT gates
2. Feed A and ~B to RippleCarryAdder with cin=1
3. Output: difference and borrow

Structure for N-bit subtractor:
- Inputs: a[N-1:0], b[N-1:0]
- Outputs: diff[N-1:0], borrow
- Gates: N NOT gates + RippleCarryAdder (N FullAdders × 5 gates)
- Total: N + (N × 5) = 6N gates

This demonstrates compositional reuse: building on proven RippleCarryAdder!
-/

import Shoumei.DSL
import Shoumei.Circuits.Combinational.RippleCarryAdder

namespace Shoumei.Circuits.Combinational

open Shoumei

-- Helper: Build N-bit subtractor by composing NOT gates + RippleCarryAdder
-- Uses 2's complement: A - B = A + (~B) + 1
def mkSubtractorN (n : Nat) : Circuit :=
  let a := makeIndexedWires "a" n
  let b := makeIndexedWires "b" n
  let diff := makeIndexedWires "diff" n
  let borrow := Wire.mk "borrow"

  -- Create inverted B wires
  let b_inv := makeIndexedWires "b_inv" n

  -- NOT gates to invert B (for 2's complement)
  let not_gates := List.zipWith (fun b_wire b_inv_wire =>
    Gate.mkNOT b_wire b_inv_wire
  ) b b_inv

  -- RippleCarryAdder structure (reuse our proven implementation!)
  -- For N bits, need N-1 internal carries
  let internal_carries := makeIndexedWires "c" (n - 1)
  let cin := Wire.mk "one"  -- cin=1 for 2's complement

  -- Carry chain: cin (=1), c0, c1, ..., c(n-2), borrow
  let carries := cin :: internal_carries ++ [borrow]

  -- Build RCA gates using A and inverted B
  let rca_gates := buildFullAdderChain a b_inv carries diff ""

  -- Create a constant "1" wire for cin
  -- We'll represent this as an input that should be tied to 1
  let one := Wire.mk "one"

  { name := s!"Subtractor{n}"
    inputs := a ++ b ++ [one]  -- one should be tied to 1 externally
    outputs := diff ++ [borrow]
    gates := not_gates ++ rca_gates
  }

-- Specific widths
def mkSubtractor4 : Circuit := mkSubtractorN 4
def mkSubtractor8 : Circuit := mkSubtractorN 8
def mkSubtractor32 : Circuit := mkSubtractorN 32

-- Alternative: Subtractor without explicit "one" input
-- Instead, use a fixed high signal (requires extending DSL or using a trick)
-- For now, we'll use the version above where "one" is an input

end Shoumei.Circuits.Combinational
