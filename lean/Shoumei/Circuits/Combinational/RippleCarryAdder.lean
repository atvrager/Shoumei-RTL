/-
Circuits/Combinational/Adder.lean - 32-bit Ripple-Carry Adder

A 32-bit ripple-carry adder built from 32 FullAdder circuits chained together.
Each FullAdder adds one bit position, with the carry-out of bit i feeding
the carry-in of bit i+1.

Structure:
- Inputs: a[31:0], b[31:0], cin
- Outputs: sum[31:0], cout
- Gates: 160 total (32 FullAdders × 5 gates each)

Logic:
  For each bit i (0 to 31):
    sum[i], c[i+1] = FullAdder(a[i], b[i], c[i])
  where c[0] = cin and c[32] = cout
-/

import Shoumei.DSL
import Shoumei.Examples.Adder

namespace Shoumei.Circuits.Combinational

open Shoumei
open Shoumei.Examples

-- Helper: Create a list of wires with indexed names
-- Reuse from Register.lean pattern
def makeIndexedWires (name : String) (n : Nat) : List Wire :=
  (List.range n).map (fun i => Wire.mk s!"{name}{i}")

-- Helper: Create a FullAdder instance for a specific bit position
-- Uses Circuit.inline to properly reuse the proven fullAdderCircuit
-- This demonstrates hierarchical composition!
def mkFullAdderInstance (a b cin sum cout : Wire) (bitIndex : Nat) (wirePrefix : String) : List Gate :=
  -- Create wire mapping from fullAdderCircuit to our wires
  let wireMap (w : Wire) : Wire :=
    match w.name with
    | "a" => a
    | "b" => b
    | "cin" => cin
    | "sum" => sum
    | "cout" => cout
    -- Internal wires need unique names per bit position
    | "ab_xor" => Wire.mk s!"{wirePrefix}ab_xor{bitIndex}"
    | "ab_and" => Wire.mk s!"{wirePrefix}ab_and{bitIndex}"
    | "cin_ab" => Wire.mk s!"{wirePrefix}cin_ab{bitIndex}"
    | _ => Wire.mk s!"{wirePrefix}unknown_{w.name}{bitIndex}"  -- Fallback

  -- Inline the proven fullAdderCircuit with our wire mapping
  fullAdderCircuit.inline wireMap

-- Helper: Build a chain of FullAdders with carry propagation
-- Returns the gates list for a ripple-carry adder
-- wirePrefix: wirePrefix for internal wire names to avoid collisions (use "" for no wirePrefix)
def buildFullAdderChain (a_wires b_wires carry_wires sum_wires : List Wire) (wirePrefix : String) : List Gate :=
  let n := a_wires.length
  -- For each bit position i, instantiate a FullAdder
  List.flatten (List.range n |>.map fun i =>
    mkFullAdderInstance
      (a_wires.get! i)
      (b_wires.get! i)
      (carry_wires.get! i)      -- cin for bit i
      (sum_wires.get! i)        -- sum for bit i
      (carry_wires.get! (i + 1)) -- cout = cin for bit i+1
      i                         -- bit index for wire naming
      wirePrefix                    -- wirePrefix for internal wires
  )

-- Build a 32-bit ripple-carry adder
def mkRippleCarryAdder32 : Circuit :=
  let a := makeIndexedWires "a" 32
  let b := makeIndexedWires "b" 32
  let sum := makeIndexedWires "sum" 32

  -- Carry chain: cin → c0 → c1 → ... → c30 → cout
  -- For 32 bits, need 31 internal carries (c0..c30)
  let internal_carries := makeIndexedWires "c" 31
  let cin := Wire.mk "cin"
  let cout := Wire.mk "cout"

  -- Full carry chain: cin, c0, c1, ..., c30, cout (33 elements)
  let carries := cin :: internal_carries ++ [cout]

  -- Build the gates
  let gates := buildFullAdderChain a b carries sum ""

  { name := "RippleCarryAdder32"
    inputs := a ++ b ++ [cin]
    outputs := sum ++ [cout]
    gates := gates
    instances := []
  }

-- Convenience: 8-bit ripple-carry adder (for testing)
def mkRippleCarryAdder8 : Circuit :=
  let a := makeIndexedWires "a" 8
  let b := makeIndexedWires "b" 8
  let sum := makeIndexedWires "sum" 8
  -- For 8 bits, need 7 internal carries (c0..c6)
  let internal_carries := makeIndexedWires "c" 7
  let cin := Wire.mk "cin"
  let cout := Wire.mk "cout"
  let carries := cin :: internal_carries ++ [cout]

  let gates := buildFullAdderChain a b carries sum ""

  { name := "RippleCarryAdder8"
    inputs := a ++ b ++ [cin]
    outputs := sum ++ [cout]
    gates := gates
    instances := []
  }

-- Convenience: 4-bit ripple-carry adder (for testing)
def mkRippleCarryAdder4 : Circuit :=
  let a := makeIndexedWires "a" 4
  let b := makeIndexedWires "b" 4
  let sum := makeIndexedWires "sum" 4
  -- For 4 bits, need 3 internal carries (c0..c2)
  let internal_carries := makeIndexedWires "c" 3
  let cin := Wire.mk "cin"
  let cout := Wire.mk "cout"
  let carries := cin :: internal_carries ++ [cout]

  let gates := buildFullAdderChain a b carries sum ""

  { name := "RippleCarryAdder4"
    inputs := a ++ b ++ [cin]
    outputs := sum ++ [cout]
    gates := gates
    instances := []
  }

end Shoumei.Circuits.Combinational
