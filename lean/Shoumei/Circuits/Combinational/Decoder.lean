/-
Binary Decoder - Convert n-bit binary input to 2^n one-hot output

This module implements binary-to-one-hot decoders used for:
- Register file write enables (5→32 for RAT, 6→64 for PhysRegFile)
- Address decoding in memory systems
- Control signal generation

Behavioral model: Map binary input to one-hot output
Structural model: AND trees for each output bit

Example: 3-bit decoder (n=3, 8 outputs)
Input 101 (5) → output[5]=1, all other outputs=0

For output bit i, check if input == i by:
  AND all bits together, where bit j is:
    - input[j] if i has bit j set
    - NOT(input[j]) if i has bit j clear
-/

import Shoumei.DSL

namespace Shoumei.Circuits.Combinational

open Shoumei

/-! ## Behavioral Model -/

/-- Decoder state: n-bit input mapped to 2^n one-hot output -/
structure DecoderState (n : Nat) where
  /-- Binary input value -/
  input : Fin (2^n)
  /-- One-hot output: exactly one bit high -/
  output : Fin (2^n) → Bool
  /-- Invariant: output is one-hot encoding of input -/
  h_onehot : ∀ i, output i = (i == input)

/-- Create decoder state from binary input -/
def DecoderState.mk' {n : Nat} (input : Fin (2^n)) : DecoderState n :=
  { input := input
    output := fun i => i == input
    h_onehot := fun _ => rfl }

/-- Decode: convert binary input to one-hot output -/
def decode {n : Nat} (input : Fin (2^n)) : DecoderState n :=
  DecoderState.mk' input

/-! ## Structural Circuit Helpers -/

-- Helper: Create a list of wires with indexed names
private def makeIndexedWires (name : String) (count : Nat) : List Wire :=
  (List.range count).map (fun i => Wire.mk s!"{name}{i}")

-- Helper: Check if bit position is set in a natural number
-- testBit n i returns true if bit i of n is 1
private def testBit (n : Nat) (i : Nat) : Bool :=
  (n >>> i) % 2 == 1

/-! ## Structural Circuit -/

/--
Build gates to check if n-bit input equals target value.
Returns list of gates that produce output wire matching (input == target).

For each bit position i:
  - If target[i] = 1, use input[i] directly
  - If target[i] = 0, use NOT(input[i])
Then AND all these literals together.
-/
def mkEqualityCheckGates (n : Nat) (target : Nat) (inputs : List Wire) (output : Wire) : List Gate :=
  -- Create literals for each bit position
  let (gates, literals) := (List.range n).foldl
    (fun (acc : List Gate × List Wire) (bitIdx : Nat) =>
      let (gatesSoFar, litsSoFar) := acc
      let inputWire := inputs.get! bitIdx

      if testBit target bitIdx then
        -- Bit is 1: use input wire directly
        (gatesSoFar, litsSoFar ++ [inputWire])
      else
        -- Bit is 0: use NOT of input wire
        let notWire := Wire.mk s!"not_in{bitIdx}_t{target}"
        let notGate := Gate.mkNOT inputWire notWire
        (gatesSoFar ++ [notGate], litsSoFar ++ [notWire]))
    ([], [])

  -- Chain AND gates to check all bits match
  match literals with
  | [] => gates  -- n=0 case (shouldn't happen)
  | [single] =>
      -- Single bit: just buffer to output
      gates ++ [Gate.mkBUF single output]
  | first :: rest =>
      -- Multiple bits: chain ANDs
      let (andGates, _) := rest.enum.foldl
        (fun (acc : List Gate × Wire) (idx_wire : Nat × Wire) =>
          let (idx, wire) := idx_wire
          let (gatesSoFar, prevWire) := acc
          let isLast := (idx == rest.length - 1)
          let andWire := if isLast then output
                        else Wire.mk s!"and{idx}_t{target}"
          let andGate := Gate.mkAND prevWire wire andWire
          (gatesSoFar ++ [andGate], andWire))
        ([], first)
      gates ++ andGates

/--
n-bit binary decoder: converts n-bit input to 2^n one-hot output.

For each output bit i (where i ∈ [0, 2^n)):
- Build equality check to test if input == i
- Connect result to output[i]

Gate count per output: ~2n gates (n NOT gates + n-1 AND gates worst case)
Total: O(n * 2^n) gates

Example for n=3:
  Inputs: in0, in1, in2 (LSB to MSB)
  Outputs: out0, out1, ..., out7

  out5 (binary 101):
    - Use in0 directly (bit 0 = 1)
    - Use NOT(in1) (bit 1 = 0)
    - Use in2 directly (bit 2 = 1)
    - AND them: out5 = in0 AND NOT(in1) AND in2
-/
def mkDecoder (n : Nat) : Circuit :=
  if n = 0 then
    -- Degenerate case: 0 inputs, 1 output (always high)
    { name := "Decoder0"
      inputs := []
      outputs := [Wire.mk "out0"]

      gates := []
      instances := [] }
  else
    let numOutputs := 2^n
    let inputs := makeIndexedWires "in" n
    let outputs := makeIndexedWires "out" numOutputs

    -- Build equality check gates for each output
    let allGates := (List.range numOutputs).foldl
      (fun gatesSoFar (targetVal : Nat) =>
        let outWire := outputs.get! targetVal
        let eqGates := mkEqualityCheckGates n targetVal inputs outWire
        gatesSoFar ++ eqGates)
      []

    { name := s!"Decoder{n}"
      inputs := inputs
      outputs := outputs

      gates := allGates
      instances := [] }

/-! ## Concrete Examples -/

/-- 5-bit to 32-bit decoder (for RAT write enable) -/
def mkDecoder5 : Circuit := mkDecoder 5

/-- 6-bit to 64-bit decoder (for PhysRegFile write enable) -/
def mkDecoder6 : Circuit := mkDecoder 6

/-- 3-bit to 8-bit decoder (for testing) -/
def mkDecoder3 : Circuit := mkDecoder 3

/-- 2-bit to 4-bit decoder (for small tests) -/
def mkDecoder2 : Circuit := mkDecoder 2

end Shoumei.Circuits.Combinational
