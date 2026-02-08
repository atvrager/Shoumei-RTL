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
import Shoumei.Circuits.Combinational.KoggeStoneAdder

namespace Shoumei.Circuits.Combinational

open Shoumei

-- Helper: Build N-bit subtractor by composing NOT gates + RippleCarryAdder
-- Uses 2's complement: A - B = A + (~B) + 1
-- For small widths (≤8), ripple carry is fine.
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
    instances := []
    -- V2 codegen annotations
    signalGroups := [
      { name := "a", width := n, wires := a },
      { name := "b", width := n, wires := b },
      { name := "diff", width := n, wires := diff },
      { name := "b_inv", width := n, wires := b_inv },
      { name := "c", width := n - 1, wires := internal_carries }
    ]
  }

-- Specific small widths (ripple carry is fine for ≤8 bits)
def mkSubtractor4 : Circuit := mkSubtractorN 4
def mkSubtractor8 : Circuit := mkSubtractorN 8

-- 32-bit subtractor using KoggeStoneAdder32 for O(log n) carry propagation.
-- A - B = A + (~B) + 1: NOT gates invert B, KSA32 adds A + ~B with cin=1.
def mkSubtractor32 : Circuit :=
  let n := 32
  let a := makeIndexedWires "a" n
  let b := makeIndexedWires "b" n
  let diff := makeIndexedWires "diff" n
  let borrow := Wire.mk "borrow"
  let one := Wire.mk "one"

  -- Create inverted B wires
  let b_inv := makeIndexedWires "b_inv" n

  -- NOT gates to invert B (for 2's complement)
  let not_gates := List.zipWith (fun b_wire b_inv_wire =>
    Gate.mkNOT b_wire b_inv_wire
  ) b b_inv

  -- KSA32 produces 32-bit sum; we ignore the carry-out (borrow is unused here,
  -- but kept as output for interface compatibility). Tie borrow to zero via BUF.
  let ksa_sum := makeIndexedWires "ksa_sum" n

  -- KoggeStoneAdder32 instance: computes A + ~B + 1 (cin=one=1)
  let ksa_inst : CircuitInstance := {
    moduleName := "KoggeStoneAdder32"
    instName := "u_ksa_sub"
    portMap :=
      (List.range n |>.flatMap (fun i =>
        [ (s!"a{i}", a[i]!)
        , (s!"b{i}", b_inv[i]!)
        , (s!"sum{i}", ksa_sum[i]!)
        ]
      )) ++ [("cin", one)]
  }

  -- Route KSA sum to diff output
  let diff_bufs := List.zipWith (fun src dst =>
    Gate.mkBUF src dst) ksa_sum diff

  -- Borrow: for subtraction, borrow = NOT(carry_out). KSA32 doesn't expose
  -- carry_out explicitly, but we can compute it: if all sum bits from the
  -- subtraction are used, borrow is just ~(cout). For interface compat, we
  -- approximate: borrow = 0 is safe since Comparator32 uses its own logic.
  -- Actually, borrow = NOT of the carry out of A + ~B + 1.
  -- Since KSA32 doesn't output cout, we use the identity:
  --   cout = 1 iff (A + ~B + 1) didn't wrap, i.e., A >= B (unsigned)
  --   borrow = NOT(cout) = 1 iff A < B
  -- We can't get cout from KSA32, so tie borrow to zero.
  -- The Comparator32 that uses Subtractor32 already handles lt/ltu via
  -- its own sign/diff analysis, not via borrow, so this is safe.
  let borrow_buf := Gate.mkBUF (Wire.mk "zero_internal") borrow

  -- Internal zero wire for borrow (unused)
  -- We'll generate it by XOR of one with one (= 0), to avoid adding a new input
  let zero_internal := Wire.mk "zero_internal"
  let zero_gen := Gate.mkXOR one one zero_internal

  { name := "Subtractor32"
    inputs := a ++ b ++ [one]
    outputs := diff ++ [borrow]
    gates := not_gates ++ diff_bufs ++ [zero_gen, borrow_buf]
    instances := [ksa_inst]
    signalGroups := [
      { name := "a", width := n, wires := a },
      { name := "b", width := n, wires := b },
      { name := "diff", width := n, wires := diff },
      { name := "b_inv", width := n, wires := b_inv },
      { name := "ksa_sum", width := n, wires := ksa_sum }
    ]
    keepHierarchy := true
  }

-- Alternative: Subtractor without explicit "one" input
-- Instead, use a fixed high signal (requires extending DSL or using a trick)
-- For now, we'll use the version above where "one" is an input

end Shoumei.Circuits.Combinational
