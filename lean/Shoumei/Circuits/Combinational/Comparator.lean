/-
Circuits/Combinational/Comparator.lean - N-bit Comparator using Subtraction

A comparator computes equality and less-than relations between two N-bit values.
Uses subtraction (A - B) to determine:
  - eq: A == B (all diff bits are 0)
  - ltu: A < B (unsigned) - borrow from subtraction
  - lt: A < B (signed) - sign bit logic with overflow handling
  - gtu: A > B (unsigned) - ~eq & ~ltu
  - gt: A > B (signed) - ~eq & ~lt

Implementation strategy:
1. Use Subtractor to compute A - B
2. Check if all diff bits are 0 (equality)
3. Use borrow for unsigned comparison
4. Use sign bits for signed comparison (with overflow handling)

Structure for N-bit comparator:
- Inputs: a[N-1:0], b[N-1:0]
- Outputs: eq, lt, ltu, gt, gtu
- Gates: Subtractor (6N gates) + comparison logic (~3N gates)
- Total: ~9N gates

Formula for signed less-than (handles overflow):
  lt = (a[N-1] & ~b[N-1]) | (~(a[N-1] XOR b[N-1]) & diff[N-1])
  - If signs differ: negative < positive (a[N-1] & ~b[N-1])
  - If signs same: check sign of difference (~(a XOR b) & diff)
-/

import Shoumei.DSL
import Shoumei.Circuits.Combinational.Subtractor

namespace Shoumei.Circuits.Combinational

open Shoumei

-- Helper: OR all bits together (for zero detection)
-- Returns wire that is 1 if ANY input bit is 1
def mkOrTree (wires : List Wire) (output : Wire) : List Gate :=
  match wires with
  | [] => []  -- Should not happen
  | [w] => [Gate.mkBUF w output]  -- Single wire - just buffer it
  | w1 :: w2 :: rest =>
    -- Create intermediate wires
    let intermediate := Wire.mk s!"or_tree_{output.name}_{rest.length}"
    let first_or := Gate.mkOR w1 w2 intermediate
    first_or :: mkOrTree (intermediate :: rest) output
termination_by wires.length

-- Helper: Build N-bit comparator using Subtractor
def mkComparatorN (n : Nat) : Circuit :=
  let a := makeIndexedWires "a" n
  let b := makeIndexedWires "b" n

  -- Outputs
  let eq := Wire.mk "eq"
  let lt := Wire.mk "lt"
  let ltu := Wire.mk "ltu"
  let gt := Wire.mk "gt"
  let gtu := Wire.mk "gtu"

  -- Subtractor outputs
  let diff := makeIndexedWires "diff" n
  let borrow := Wire.mk "borrow"

  -- Build subtractor (inlined to avoid creating separate circuit)
  let b_inv := makeIndexedWires "b_inv" n
  let not_gates := List.zipWith (fun b_wire b_inv_wire =>
    Gate.mkNOT b_wire b_inv_wire
  ) b b_inv

  let internal_carries := makeIndexedWires "c" (n - 1)
  let one := Wire.mk "one"
  let carries := one :: internal_carries ++ [borrow]
  let rca_gates := buildFullAdderChain a b_inv carries diff

  -- Equality detection: diff == 0 means all bits are 0
  -- OR all diff bits, then NOT the result
  let any_diff := Wire.mk "any_diff"
  let or_tree_gates := mkOrTree diff any_diff
  let eq_gate := Gate.mkNOT any_diff eq

  -- Unsigned less-than: just use borrow (buffer it to output)
  let ltu_gate := Gate.mkBUF borrow ltu

  -- Signed less-than: lt = (a[n-1] & ~b[n-1]) | (~(a[n-1] XOR b[n-1]) & diff[n-1])
  let a_sign := a.get! (n - 1)
  let b_sign := b.get! (n - 1)
  let diff_sign := diff.get! (n - 1)

  -- Intermediate wires for signed comparison
  let b_sign_inv := Wire.mk "b_sign_inv"
  let a_neg_b_pos := Wire.mk "a_neg_b_pos"  -- a[n-1] & ~b[n-1]
  let signs_xor := Wire.mk "signs_xor"      -- a[n-1] XOR b[n-1]
  let signs_same := Wire.mk "signs_same"    -- ~(a[n-1] XOR b[n-1])
  let same_sign_cmp := Wire.mk "same_sign_cmp"  -- signs_same & diff[n-1]

  let lt_gates := [
    Gate.mkNOT b_sign b_sign_inv,
    Gate.mkAND a_sign b_sign_inv a_neg_b_pos,
    Gate.mkXOR a_sign b_sign signs_xor,
    Gate.mkNOT signs_xor signs_same,
    Gate.mkAND signs_same diff_sign same_sign_cmp,
    Gate.mkOR a_neg_b_pos same_sign_cmp lt
  ]

  -- Greater than (unsigned): ~eq & ~ltu
  let eq_inv := Wire.mk "eq_inv"
  let ltu_inv := Wire.mk "ltu_inv"
  let gtu_gates := [
    Gate.mkNOT eq eq_inv,
    Gate.mkNOT ltu ltu_inv,
    Gate.mkAND eq_inv ltu_inv gtu
  ]

  -- Greater than (signed): ~eq & ~lt
  let lt_inv := Wire.mk "lt_inv"
  let gt_gates := [
    Gate.mkNOT lt lt_inv,
    Gate.mkAND eq_inv lt_inv gt
  ]

  { name := s!"Comparator{n}"
    inputs := a ++ b ++ [one]
    outputs := [eq, lt, ltu, gt, gtu]
    gates := not_gates ++ rca_gates ++ or_tree_gates ++ [eq_gate, ltu_gate]
             ++ lt_gates ++ gtu_gates ++ gt_gates
  }

-- Specific widths
def mkComparator4 : Circuit := mkComparatorN 4
def mkComparator8 : Circuit := mkComparatorN 8
def mkComparator32 : Circuit := mkComparatorN 32

end Shoumei.Circuits.Combinational
