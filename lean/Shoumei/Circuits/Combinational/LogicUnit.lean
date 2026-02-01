/-
Circuits/Combinational/LogicUnit.lean - N-bit Logic Unit for bitwise operations

A logic unit performs bitwise logical operations on two N-bit inputs.
Supported operations: AND, OR, XOR (selected by 2-bit control signal)

Implementation strategy:
1. For each bit position, compute all three operations (AND, OR, XOR)
2. Use MUX tree to select the desired operation based on op[1:0]
3. All operations execute in parallel (purely combinational)

Structure for N-bit logic unit:
- Inputs: a[N-1:0], b[N-1:0], op[1:0]
- Output: result[N-1:0]
- Gates: 3N (operation gates) + 2N (MUX tree) = 5N gates per bit = 5N total

Operation encoding:
- op = 00: AND
- op = 01: OR
- op = 10: XOR
- op = 11: XOR (duplicate, or could be reserved)

MUX tree per bit:
  op[0]
    |
    v
  [AND/OR] -----> op[1] -----> [result]
               |           ^
             [XOR] --------+
-/

import Shoumei.DSL

namespace Shoumei.Circuits.Combinational

open Shoumei

-- Helper: Create a list of wires with indexed names (private to this module)
private def makeIndexedWires (name : String) (n : Nat) : List Wire :=
  (List.range n).map (fun i => Wire.mk s!"{name}{i}")

-- Helper: Build logic unit for one bit position
-- Inputs: a_i, b_i, op0, op1
-- Output: result_i
-- Returns list of gates for this bit
def mkLogicUnitBit (a b op0 op1 : Wire) (result : Wire) (bitIndex : Nat) : List Gate :=
  -- Intermediate wires
  let and_result := Wire.mk s!"and_{bitIndex}"
  let or_result := Wire.mk s!"or_{bitIndex}"
  let xor_result := Wire.mk s!"xor_{bitIndex}"
  let mux1 := Wire.mk s!"mux1_{bitIndex}"  -- AND or OR based on op[0]

  [
    -- Compute all three operations
    Gate.mkAND a b and_result,
    Gate.mkOR a b or_result,
    Gate.mkXOR a b xor_result,

    -- MUX tree: first select between AND and OR
    Gate.mkMUX and_result or_result op0 mux1,

    -- Then select between (AND/OR) and XOR based on op[1]
    Gate.mkMUX mux1 xor_result op1 result
  ]

-- Helper: Build N-bit logic unit
def mkLogicUnitN (n : Nat) : Circuit :=
  let a := makeIndexedWires "a" n
  let b := makeIndexedWires "b" n
  let result := makeIndexedWires "result" n
  let op0 := Wire.mk "op0"  -- LSB of operation selector
  let op1 := Wire.mk "op1"  -- MSB of operation selector

  -- Build gates for all bit positions
  let gates := List.flatten (List.range n |>.map (fun i =>
    mkLogicUnitBit (a[i]!) (b[i]!) op0 op1 (result[i]!) i
  ))

  { name := s!"LogicUnit{n}"
    inputs := a ++ b ++ [op0, op1]
    outputs := result
    gates := gates
    instances := []
  }

-- Specific widths
def mkLogicUnit4 : Circuit := mkLogicUnitN 4
def mkLogicUnit8 : Circuit := mkLogicUnitN 8
def mkLogicUnit32 : Circuit := mkLogicUnitN 32

end Shoumei.Circuits.Combinational
