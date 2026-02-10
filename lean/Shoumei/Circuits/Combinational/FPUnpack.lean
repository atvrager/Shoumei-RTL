/-
Circuits/Combinational/FPUnpack.lean - IEEE 754 Binary32 Unpacker

Unpacks a 32-bit IEEE 754 single-precision float into its components:
  - sign (1 bit) - bit 31
  - exp[7:0] (8 bits) - bits 30:23
  - mant[23:0] (24 bits) - bits 22:0 with implicit leading 1 restored for normals
  - isZero, isInf, isNaN, isSubnormal classification flags

Implementation:
  - BUF gates to route sign, exponent, and raw mantissa bits
  - AND-tree to detect exp_all_ones (0xFF)
  - NOR-reduce (NOT each + AND-tree) to detect exp_all_zeros
  - OR-tree + NOT to detect mant_all_zeros
  - Implicit bit: NOT(exp_all_zeros) AND NOT(exp_all_ones)
  - Classification flags from combinations of the above
-/

import Shoumei.DSL

namespace Shoumei.Circuits.Combinational

open Shoumei

private def makeIndexedWires (name : String) (n : Nat) : List Wire :=
  (List.range n).map (fun i => Wire.mk s!"{name}_{i}")

/-- Balanced binary AND-tree: reduces a list of wires to a single output via AND gates. -/
private def mkAndTree (wires : List Wire) (output : Wire) (pfx : String) : List Gate :=
  let buildLevel (ws : List Wire) (lvl : Nat) : List Wire × List Gate :=
    let rec go (remaining : List Wire) (acc_w : List Wire) (acc_g : List Gate) :=
      match remaining with
      | [] => (acc_w.reverse, acc_g)
      | [w] => ((w :: acc_w).reverse, acc_g)
      | w1 :: w2 :: rest =>
        let intermediate := Wire.mk s!"and_t_{pfx}_l{lvl}_{acc_w.length}"
        let gate := Gate.mkAND w1 w2 intermediate
        go rest (intermediate :: acc_w) (acc_g ++ [gate])
    go ws [] []
  let rec reduceTree (ws : List Wire) (lvl : Nat) (acc : List Gate) (fuel : Nat)
      : List Gate :=
    match fuel with
    | 0 => acc
    | fuel' + 1 =>
      match ws with
      | [] => acc
      | [w] => acc ++ [Gate.mkBUF w output]
      | _ =>
        let (next_ws, next_gates) := buildLevel ws lvl
        reduceTree next_ws (lvl + 1) (acc ++ next_gates) fuel'
  reduceTree wires 0 [] (wires.length + 1)

/-- Balanced binary OR-tree: reduces a list of wires to a single output via OR gates. -/
private def mkOrTreeFP (wires : List Wire) (output : Wire) (pfx : String) : List Gate :=
  let buildLevel (ws : List Wire) (lvl : Nat) : List Wire × List Gate :=
    let rec go (remaining : List Wire) (acc_w : List Wire) (acc_g : List Gate) :=
      match remaining with
      | [] => (acc_w.reverse, acc_g)
      | [w] => ((w :: acc_w).reverse, acc_g)
      | w1 :: w2 :: rest =>
        let intermediate := Wire.mk s!"or_t_{pfx}_l{lvl}_{acc_w.length}"
        let gate := Gate.mkOR w1 w2 intermediate
        go rest (intermediate :: acc_w) (acc_g ++ [gate])
    go ws [] []
  let rec reduceTree (ws : List Wire) (lvl : Nat) (acc : List Gate) (fuel : Nat)
      : List Gate :=
    match fuel with
    | 0 => acc
    | fuel' + 1 =>
      match ws with
      | [] => acc
      | [w] => acc ++ [Gate.mkBUF w output]
      | _ =>
        let (next_ws, next_gates) := buildLevel ws lvl
        reduceTree next_ws (lvl + 1) (acc ++ next_gates) fuel'
  reduceTree wires 0 [] (wires.length + 1)

def fpUnpackCircuit : Circuit :=
  -- Inputs: 32-bit IEEE 754 value
  let data := makeIndexedWires "data" 32

  -- Outputs
  let sign := Wire.mk "sign"
  let exp := makeIndexedWires "exp" 8
  let mant := makeIndexedWires "mant" 24
  let isZero := Wire.mk "isZero"
  let isInf := Wire.mk "isInf"
  let isNaN := Wire.mk "isNaN"
  let isSubnormal := Wire.mk "isSubnormal"

  -- 1. Sign: BUF data[31] -> sign
  let sign_gate := Gate.mkBUF data[31]! sign

  -- 2. Exponent: BUF data[23+i] -> exp[i] for i in 0..7
  let exp_gates := List.range 8 |>.map (fun i =>
    Gate.mkBUF data[23 + i]! exp[i]!)

  -- 3. Raw mantissa: BUF data[i] -> mant[i] for i in 0..22
  let mant_raw_gates := List.range 23 |>.map (fun i =>
    Gate.mkBUF data[i]! mant[i]!)

  -- 4. Detect exp_all_ones: AND-reduce exp[7:0]
  --    We use intermediate wires (not output ports) for the tree
  let exp_wires := List.range 8 |>.map (fun i => Wire.mk s!"exp_w_{i}")
  let exp_buf_gates := List.range 8 |>.map (fun i =>
    Gate.mkBUF data[23 + i]! exp_wires[i]!)
  let exp_all_ones := Wire.mk "exp_all_ones"
  let exp_ones_gates := mkAndTree exp_wires exp_all_ones "exp_ones"

  -- 5. Detect exp_all_zeros: NOT each exp bit, then AND-reduce
  let exp_inv := List.range 8 |>.map (fun i => Wire.mk s!"exp_inv_{i}")
  let exp_inv_gates := List.range 8 |>.map (fun i =>
    Gate.mkNOT exp_wires[i]! exp_inv[i]!)
  let exp_all_zeros := Wire.mk "exp_all_zeros"
  let exp_zeros_gates := mkAndTree exp_inv exp_all_zeros "exp_zeros"

  -- 6. Detect mant_all_zeros: OR-tree of data[22:0], then NOT
  let mant_raw_wires := List.range 23 |>.map (fun i => Wire.mk s!"mant_w_{i}")
  let mant_raw_buf_gates := List.range 23 |>.map (fun i =>
    Gate.mkBUF data[i]! mant_raw_wires[i]!)
  let mant_any_set := Wire.mk "mant_any_set"
  let mant_or_gates := mkOrTreeFP mant_raw_wires mant_any_set "mant_or"
  let mant_all_zeros := Wire.mk "mant_all_zeros"
  let mant_all_zeros_gate := Gate.mkNOT mant_any_set mant_all_zeros

  -- 7. mant_nonzero = NOT mant_all_zeros (== mant_any_set, but use a named wire)
  let mant_nonzero := Wire.mk "mant_nonzero"
  let mant_nonzero_gate := Gate.mkBUF mant_any_set mant_nonzero

  -- 8. Implicit bit: mant[23] = NOT(exp_all_zeros) AND NOT(exp_all_ones)
  let not_exp_zeros := Wire.mk "not_exp_zeros"
  let not_exp_ones := Wire.mk "not_exp_ones"
  let implicit_bit_gates := [
    Gate.mkNOT exp_all_zeros not_exp_zeros,
    Gate.mkNOT exp_all_ones not_exp_ones,
    Gate.mkAND not_exp_zeros not_exp_ones mant[23]!
  ]

  -- 9. isZero = exp_all_zeros AND mant_all_zeros
  let isZero_gate := Gate.mkAND exp_all_zeros mant_all_zeros isZero

  -- 10. isInf = exp_all_ones AND mant_all_zeros
  let isInf_gate := Gate.mkAND exp_all_ones mant_all_zeros isInf

  -- 11. isNaN = exp_all_ones AND mant_nonzero
  let isNaN_gate := Gate.mkAND exp_all_ones mant_nonzero isNaN

  -- 12. isSubnormal = exp_all_zeros AND mant_nonzero
  let isSubnormal_gate := Gate.mkAND exp_all_zeros mant_nonzero isSubnormal

  { name := "FPUnpack"
    inputs := data
    outputs := [sign] ++ exp ++ mant ++ [isZero, isInf, isNaN, isSubnormal]
    gates := [sign_gate]
             ++ exp_gates
             ++ mant_raw_gates
             ++ exp_buf_gates
             ++ exp_ones_gates
             ++ exp_inv_gates
             ++ exp_zeros_gates
             ++ mant_raw_buf_gates
             ++ mant_or_gates
             ++ [mant_all_zeros_gate, mant_nonzero_gate]
             ++ implicit_bit_gates
             ++ [isZero_gate, isInf_gate, isNaN_gate, isSubnormal_gate]
    instances := []
    signalGroups := [
      { name := "data", width := 32, wires := data },
      { name := "exp", width := 8, wires := exp },
      { name := "mant", width := 24, wires := mant }
    ]
  }

end Shoumei.Circuits.Combinational
