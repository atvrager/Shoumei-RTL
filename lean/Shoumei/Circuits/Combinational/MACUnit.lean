/-
Circuits/Combinational/MACUnit.lean - Multiply-Accumulate Unit

MAC cells for the Vector Matrix Extension (VME).
Two variants:
- mkMACUnit8:  int8 × int8 → sign-extend to 32b → multiply → add acc_in → result[31:0]
- mkMACUnit16: int16 × int16 → sign-extend to 32b → multiply → add acc_in → result[31:0]

Architecture:
- Sign-extension of inputs to 32 bits
- 32×32 → 64-bit unsigned multiply (reusing partial-product + adder approach)
- Lower 32 bits of product + acc_in via RippleCarryAdder32
- Result is the 32-bit accumulated value (overflow wraps)

For int8: inputs a[7:0], b[7:0], acc_in[31:0] → result[31:0]
For int16: inputs a[15:0], b[15:0], acc_in[31:0] → result[31:0]
-/

import Shoumei.DSL
import Shoumei.Circuits.Combinational.RippleCarryAdder

namespace Shoumei.Circuits.Combinational

open Shoumei

/-! ## Behavioral Model -/

/-- Sign-extend an n-bit value to 32 bits -/
def signExtend (val : UInt32) (width : Nat) : UInt32 :=
  let truncated := val.toNat % (2 ^ width)
  let signBit := 2 ^ (width - 1)
  if truncated >= signBit then
    -- Negative: fill upper bits with 1s
    ((truncated ||| (0xFFFFFFFF - (2 ^ width - 1))) % (2^32)).toUInt32
  else
    truncated.toUInt32

/-- MAC operation: (sign_extend(a, w) * sign_extend(b, w) + acc) mod 2^32 -/
def macCompute (a b acc : UInt32) (inputWidth : Nat) : UInt32 :=
  let sa := signExtend a inputWidth
  let sb := signExtend b inputWidth
  -- Use Int for the multiply to handle sign correctly, then truncate
  let ai : Int := if sa.toNat >= 2^31 then (sa.toNat : Int) - 2^32 else sa.toNat
  let bi : Int := if sb.toNat >= 2^31 then (sb.toNat : Int) - 2^32 else sb.toNat
  let product := ai * bi
  let productU32 := ((product % (2^32 : Int) + (2^32 : Int)).toNat % (2^32)).toUInt32
  productU32 + acc

/-! ## Structural Circuit: MACUnit8 -/

/-- Build an 8-bit MAC unit.

    Inputs (48): a[7:0], b[7:0], acc_in[31:0]
    Outputs (32): result[31:0]

    Computes: result = sign_extend(a,8) * sign_extend(b,8) + acc_in (mod 2^32)

    Architecture:
    - Sign-extend a and b to 32 bits via gate-level sign extension
    - Generate partial products (32×32 AND array, only lower 32 bits matter)
    - Compress via adder tree
    - Add accumulator input
-/
def mkMACUnit8 : Circuit :=
  let inputWidth := 8
  -- Inputs
  let a := makeIndexedWires "a" inputWidth
  let b := makeIndexedWires "b" inputWidth
  let acc_in := makeIndexedWires "acc_in" 32
  -- Outputs
  let result := makeIndexedWires "result" 32

  -- Sign-extend a[7:0] → a_ext[31:0]
  let a_ext := makeIndexedWires "a_ext" 32
  let a_ext_gates : List Gate :=
    -- Lower 8 bits: buffer from input
    (List.range inputWidth).map (fun i => Gate.mkBUF (a[i]!) (a_ext[i]!)) ++
    -- Upper 24 bits: replicate sign bit (a[7])
    (List.range (32 - inputWidth)).map (fun i =>
      Gate.mkBUF (a[inputWidth - 1]!) (a_ext[inputWidth + i]!))

  -- Sign-extend b[7:0] → b_ext[31:0]
  let b_ext := makeIndexedWires "b_ext" 32
  let b_ext_gates : List Gate :=
    (List.range inputWidth).map (fun i => Gate.mkBUF (b[i]!) (b_ext[i]!)) ++
    (List.range (32 - inputWidth)).map (fun i =>
      Gate.mkBUF (b[inputWidth - 1]!) (b_ext[inputWidth + i]!))

  -- Partial products: pp[i][j] = a_ext[i] AND b_ext[j] for lower 32 bits
  -- We only need bits [31:0] of the product, so for row i, we need columns j where i+j < 32
  let pp_wires : List (List Wire) := (List.range 32).map (fun i =>
    (List.range 32).map (fun j =>
      Wire.mk s!"pp_{i}_{j}"))
  let pp_gates : List Gate := (List.range 32).flatMap (fun i =>
    (List.range 32).map (fun j =>
      Gate.mkAND (a_ext[i]!) (b_ext[j]!) ((pp_wires[i]!)[j]!)))

  -- Sum partial products column by column using a simple ripple approach
  -- For each output bit k (0..31), sum all pp[i][j] where i+j=k, plus carry from k-1
  -- This is a simplified approach — use a tree of full adders per column

  -- For a practical gate-level implementation, we use an instance of RippleCarryAdder32
  -- to add the product (computed via sub-instance) to the accumulator.
  -- Here we use a simpler approach: instantiate multiplier + adder as sub-modules.

  -- Product accumulation wires
  let zero := Wire.mk "zero"

  -- Build column sums using XOR/AND chains (Wallace tree simplified)
  -- For simplicity and correctness, we flatten to a series of additions.
  -- Row 0 partial products form the initial sum.
  -- Each subsequent row is shifted and added.

  -- Actually, for a clean hierarchical design, we just need the adder instance.
  -- The partial product reduction is done via a chain of RippleCarryAdder32 instances.

  -- Row reduction: accumulate partial product rows one by one
  -- acc_0 = pp_row_0 (partial products where a_ext[0] selects b_ext)
  -- acc_k = acc_{k-1} + (pp_row_k << k)

  -- For each row i (0..31), the contribution to bit j is pp[i][j-i] if j >= i
  -- We create 32 intermediate sums, each via RippleCarryAdder32

  -- Row 0 wires (pp[0][0..31])
  let row_sums : List (List Wire) := (List.range 33).map (fun r =>
    if r == 0 then
      -- Initial: all zeros
      (List.range 32).map (fun j => Wire.mk s!"rsum_0_{j}")
    else
      (List.range 32).map (fun j => Wire.mk s!"rsum_{r}_{j}"))

  -- Initialize row_sum_0 to zero
  let init_gates := (List.range 32).map (fun j =>
    Gate.mkBUF zero ((row_sums[0]!)[j]!))

  -- Shifted row wires and adder instances for each row
  let shifted_rows : List (List Wire) := (List.range 32).map (fun i =>
    (List.range 32).map (fun j => Wire.mk s!"srow_{i}_{j}"))

  -- Build shifted row i: bit j = if j >= i then pp[i][j-i] else 0
  let shift_gates : List Gate := (List.range 32).flatMap (fun i =>
    (List.range 32).map (fun j =>
      if j >= i && j - i < 32 then
        Gate.mkBUF ((pp_wires[i]!)[j - i]!) ((shifted_rows[i]!)[j]!)
      else
        Gate.mkBUF zero ((shifted_rows[i]!)[j]!)))

  -- Chain of adder instances: rsum[i+1] = rsum[i] + shifted_row[i]
  let adder_carry_wires := (List.range 32).map (fun i => Wire.mk s!"rcarry_{i}")
  let adder_instances : List CircuitInstance := (List.range 32).map (fun i =>
    { moduleName := "RippleCarryAdder32"
      instName := s!"u_add_row_{i}"
      portMap :=
        ((row_sums[i]!).enum.map (fun ⟨k, w⟩ => (s!"a_{k}", w))) ++
        ((shifted_rows[i]!).enum.map (fun ⟨k, w⟩ => (s!"b_{k}", w))) ++
        [("carry_in", zero)] ++
        ((row_sums[i + 1]!).enum.map (fun ⟨k, w⟩ => (s!"sum_{k}", w))) ++
        [("carry_out", adder_carry_wires[i]!)]
    })

  -- Final product is in row_sums[32]
  -- Now add product + acc_in
  let final_carry := Wire.mk "final_carry"
  let final_adder : CircuitInstance :=
    { moduleName := "RippleCarryAdder32"
      instName := "u_add_acc"
      portMap :=
        ((row_sums[32]!).enum.map (fun ⟨k, w⟩ => (s!"a_{k}", w))) ++
        (acc_in.enum.map (fun ⟨k, w⟩ => (s!"b_{k}", w))) ++
        [("carry_in", zero)] ++
        (result.enum.map (fun ⟨k, w⟩ => (s!"sum_{k}", w))) ++
        [("carry_out", final_carry)]
    }

  { name := "MACUnit8"
    inputs := a ++ b ++ acc_in ++ [zero]
    outputs := result
    gates := a_ext_gates ++ b_ext_gates ++ pp_gates ++ init_gates ++ shift_gates
    instances := adder_instances ++ [final_adder]
    signalGroups := [
      { name := "a", width := inputWidth, wires := a },
      { name := "b", width := inputWidth, wires := b },
      { name := "acc_in", width := 32, wires := acc_in },
      { name := "result", width := 32, wires := result }
    ]
  }

/-- Build a 16-bit MAC unit.

    Inputs (64): a[15:0], b[15:0], acc_in[31:0]
    Outputs (32): result[31:0]

    Computes: result = sign_extend(a,16) * sign_extend(b,16) + acc_in (mod 2^32)
-/
def mkMACUnit16 : Circuit :=
  let inputWidth := 16
  let a := makeIndexedWires "a" inputWidth
  let b := makeIndexedWires "b" inputWidth
  let acc_in := makeIndexedWires "acc_in" 32
  let result := makeIndexedWires "result" 32
  let zero := Wire.mk "zero"

  -- Sign-extend a[15:0] → a_ext[31:0]
  let a_ext := makeIndexedWires "a_ext" 32
  let a_ext_gates : List Gate :=
    (List.range inputWidth).map (fun i => Gate.mkBUF (a[i]!) (a_ext[i]!)) ++
    (List.range (32 - inputWidth)).map (fun i =>
      Gate.mkBUF (a[inputWidth - 1]!) (a_ext[inputWidth + i]!))

  -- Sign-extend b[15:0] → b_ext[31:0]
  let b_ext := makeIndexedWires "b_ext" 32
  let b_ext_gates : List Gate :=
    (List.range inputWidth).map (fun i => Gate.mkBUF (b[i]!) (b_ext[i]!)) ++
    (List.range (32 - inputWidth)).map (fun i =>
      Gate.mkBUF (b[inputWidth - 1]!) (b_ext[inputWidth + i]!))

  -- Partial products
  let pp_wires : List (List Wire) := (List.range 32).map (fun i =>
    (List.range 32).map (fun j => Wire.mk s!"pp_{i}_{j}"))
  let pp_gates : List Gate := (List.range 32).flatMap (fun i =>
    (List.range 32).map (fun j =>
      Gate.mkAND (a_ext[i]!) (b_ext[j]!) ((pp_wires[i]!)[j]!)))

  -- Row sums (same approach as MACUnit8)
  let row_sums : List (List Wire) := (List.range 33).map (fun r =>
    (List.range 32).map (fun j => Wire.mk s!"rsum_{r}_{j}"))

  let init_gates := (List.range 32).map (fun j =>
    Gate.mkBUF zero ((row_sums[0]!)[j]!))

  let shifted_rows : List (List Wire) := (List.range 32).map (fun i =>
    (List.range 32).map (fun j => Wire.mk s!"srow_{i}_{j}"))

  let shift_gates : List Gate := (List.range 32).flatMap (fun i =>
    (List.range 32).map (fun j =>
      if j >= i && j - i < 32 then
        Gate.mkBUF ((pp_wires[i]!)[j - i]!) ((shifted_rows[i]!)[j]!)
      else
        Gate.mkBUF zero ((shifted_rows[i]!)[j]!)))

  let adder_carry_wires := (List.range 32).map (fun i => Wire.mk s!"rcarry_{i}")
  let adder_instances : List CircuitInstance := (List.range 32).map (fun i =>
    { moduleName := "RippleCarryAdder32"
      instName := s!"u_add_row_{i}"
      portMap :=
        ((row_sums[i]!).enum.map (fun ⟨k, w⟩ => (s!"a_{k}", w))) ++
        ((shifted_rows[i]!).enum.map (fun ⟨k, w⟩ => (s!"b_{k}", w))) ++
        [("carry_in", zero)] ++
        ((row_sums[i + 1]!).enum.map (fun ⟨k, w⟩ => (s!"sum_{k}", w))) ++
        [("carry_out", adder_carry_wires[i]!)]
    })

  let final_carry := Wire.mk "final_carry"
  let final_adder : CircuitInstance :=
    { moduleName := "RippleCarryAdder32"
      instName := "u_add_acc"
      portMap :=
        ((row_sums[32]!).enum.map (fun ⟨k, w⟩ => (s!"a_{k}", w))) ++
        (acc_in.enum.map (fun ⟨k, w⟩ => (s!"b_{k}", w))) ++
        [("carry_in", zero)] ++
        (result.enum.map (fun ⟨k, w⟩ => (s!"sum_{k}", w))) ++
        [("carry_out", final_carry)]
    }

  { name := "MACUnit16"
    inputs := a ++ b ++ acc_in ++ [zero]
    outputs := result
    gates := a_ext_gates ++ b_ext_gates ++ pp_gates ++ init_gates ++ shift_gates
    instances := adder_instances ++ [final_adder]
    signalGroups := [
      { name := "a", width := inputWidth, wires := a },
      { name := "b", width := inputWidth, wires := b },
      { name := "acc_in", width := 32, wires := acc_in },
      { name := "result", width := 32, wires := result }
    ]
  }

/-- Convenience aliases -/
def macUnit8 : Circuit := mkMACUnit8
def macUnit16 : Circuit := mkMACUnit16

end Shoumei.Circuits.Combinational
