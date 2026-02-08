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

-- Helper: OR all bits together (for zero detection) using balanced binary tree.
-- O(log n) depth instead of O(n) ripple chain.
-- Uses fuel parameter to guarantee termination (log2(n) + 1 levels suffice).
def mkOrTree (wires : List Wire) (output : Wire) : List Gate :=
  -- Pair up adjacent wires, OR them into intermediates
  let buildLevel (ws : List Wire) (lvl : Nat) : List Wire × List Gate :=
    let rec go (remaining : List Wire) (acc_w : List Wire) (acc_g : List Gate) :=
      match remaining with
      | [] => (acc_w.reverse, acc_g)
      | [w] => ((w :: acc_w).reverse, acc_g)
      | w1 :: w2 :: rest =>
        let intermediate := Wire.mk s!"or_t_{output.name}_l{lvl}_{acc_w.length}"
        let gate := Gate.mkOR w1 w2 intermediate
        go rest (intermediate :: acc_w) (acc_g ++ [gate])
    go ws [] []
  -- Iterate levels with fuel to guarantee termination
  let rec reduceTree (ws : List Wire) (lvl : Nat) (acc : List Gate) (fuel : Nat)
      : List Gate :=
    match fuel with
    | 0 => acc  -- Should never hit for reasonable inputs
    | fuel' + 1 =>
      match ws with
      | [] => acc
      | [w] => acc ++ [Gate.mkBUF w output]
      | _ =>
        let (next_ws, next_gates) := buildLevel ws lvl
        reduceTree next_ws (lvl + 1) (acc ++ next_gates) fuel'
  reduceTree wires 0 [] (wires.length + 1)

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
  let rca_gates := buildFullAdderChain a b_inv carries diff ""

  -- Equality detection: diff == 0 means all bits are 0
  -- OR all diff bits, then NOT the result
  -- Use intermediate wires to avoid reading output ports (firtool strips read-back outputs)
  let any_diff := Wire.mk "any_diff"
  let or_tree_gates := mkOrTree diff any_diff
  let eq_raw := Wire.mk "eq_raw"
  let eq_gate := Gate.mkNOT any_diff eq_raw
  let eq_buf := Gate.mkBUF eq_raw eq

  -- Unsigned less-than: borrow=1 means a>=b, so ltu = ~borrow
  let ltu_raw := Wire.mk "ltu_raw"
  let ltu_gate := Gate.mkNOT borrow ltu_raw
  let ltu_buf := Gate.mkBUF ltu_raw ltu

  -- Signed less-than: lt = (a[n-1] & ~b[n-1]) | (~(a[n-1] XOR b[n-1]) & diff[n-1])
  let a_sign := a[n - 1]!
  let b_sign := b[n - 1]!
  let diff_sign := diff[n - 1]!

  -- Intermediate wires for signed comparison
  let b_sign_inv := Wire.mk "b_sign_inv"
  let a_neg_b_pos := Wire.mk "a_neg_b_pos"  -- a[n-1] & ~b[n-1]
  let signs_xor := Wire.mk "signs_xor"      -- a[n-1] XOR b[n-1]
  let signs_same := Wire.mk "signs_same"    -- ~(a[n-1] XOR b[n-1])
  let same_sign_cmp := Wire.mk "same_sign_cmp"  -- signs_same & diff[n-1]

  let lt_raw := Wire.mk "lt_raw"
  let lt_gates := [
    Gate.mkNOT b_sign b_sign_inv,
    Gate.mkAND a_sign b_sign_inv a_neg_b_pos,
    Gate.mkXOR a_sign b_sign signs_xor,
    Gate.mkNOT signs_xor signs_same,
    Gate.mkAND signs_same diff_sign same_sign_cmp,
    Gate.mkOR a_neg_b_pos same_sign_cmp lt_raw
  ]
  let lt_buf := Gate.mkBUF lt_raw lt

  -- Greater than (unsigned): ~eq & ~ltu (use raw wires, not output ports)
  let eq_inv := Wire.mk "eq_inv"
  let ltu_inv := Wire.mk "ltu_inv"
  let gtu_gates := [
    Gate.mkNOT eq_raw eq_inv,
    Gate.mkNOT ltu_raw ltu_inv,
    Gate.mkAND eq_inv ltu_inv gtu
  ]

  -- Greater than (signed): ~eq & ~lt (use raw wire, not output port)
  let lt_inv := Wire.mk "lt_inv"
  let gt_gates := [
    Gate.mkNOT lt_raw lt_inv,
    Gate.mkAND eq_inv lt_inv gt
  ]

  { name := s!"Comparator{n}"
    inputs := a ++ b ++ [one]
    outputs := [eq, lt, ltu, gt, gtu]
    gates := not_gates ++ rca_gates ++ or_tree_gates
             ++ [eq_gate, eq_buf, ltu_gate, ltu_buf]
             ++ lt_gates ++ [lt_buf] ++ gtu_gates ++ gt_gates
    instances := []
    -- V2 codegen annotations
    signalGroups := [
      { name := "a", width := n, wires := a },
      { name := "b", width := n, wires := b },
      { name := "diff", width := n, wires := diff },
      { name := "b_inv", width := n, wires := b_inv },
      { name := "c", width := n - 1, wires := internal_carries }
    ]
    keepHierarchy := Nat.ble 6 n  -- Preserve hierarchy for 6-bit and 32-bit comparators
  }

-- Specific widths
def mkComparator4 : Circuit := mkComparatorN 4
def mkComparator8 : Circuit := mkComparatorN 8
def mkComparator32 : Circuit := mkComparatorN 32

end Shoumei.Circuits.Combinational
