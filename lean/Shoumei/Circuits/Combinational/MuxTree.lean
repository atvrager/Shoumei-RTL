/-
MuxTree - N-to-1 Multiplexer with Binary Tree Structure

This module implements parameterized multiplexer trees used for:
- Register file read ports (32:1 mux for RAT, 64:1 mux for PhysRegFile)
- Data path selection
- Result routing

Behavioral model: Select one of N inputs based on binary select signal
Structural model: Binary tree of 2:1 MUX gates

Example: 4:1 mux (n=4, width=8)
  inputs[0..3] (each 8 bits) + select[1:0] → output (8 bits)

  Tree structure:
         mux_level1_0 (sel[1])
            /        \
    mux_l0_0(sel[0]) mux_l0_1(sel[0])
      /    \           /    \
    in0   in1        in2   in3

Gate count: (n-1) MUX gates, each width bits wide
Total: (n-1) * width * 3 gates (MUX = 2 AND + 1 OR per bit)
-/

import Shoumei.DSL

namespace Shoumei.Circuits.Combinational

open Shoumei

/-! ## Behavioral Model -/

/-- MuxTree state: select one of n inputs -/
structure MuxTreeState (n width : Nat) where
  /-- Input values (each width bits) -/
  inputs : Fin n → List Bool
  /-- Binary select signal -/
  select : Fin n
  /-- Output value (width bits) -/
  output : List Bool
  /-- Invariant: output equals selected input -/
  h_select : output = inputs select

/-- Create MuxTree state by selecting from inputs -/
def MuxTreeState.mk' {n width : Nat} (inputs : Fin n → List Bool) (select : Fin n) : MuxTreeState n width :=
  { inputs := inputs
    select := select
    output := inputs select
    h_select := rfl }

/-- Select: choose input based on select signal -/
def muxSelect {n width : Nat} (inputs : Fin n → List Bool) (select : Fin n) : MuxTreeState n width :=
  MuxTreeState.mk' inputs select

/-! ## Structural Circuit Helpers -/

-- Helper: Create indexed wires
private def makeIndexedWires (name : String) (count : Nat) : List Wire :=
  (List.range count).map (fun i => Wire.mk s!"{name}_{i}")

-- Helper: Create multi-bit indexed wires (for each input, create width wires)
private def makeMultiBitWires (basename : String) (count : Nat) (width : Nat) : List (List Wire) :=
  (List.range count).map (fun i =>
    (List.range width).map (fun j => Wire.mk s!"{basename}{i}_b{j}"))

-- Helper: Compute log2 ceiling (number of select bits needed)
private def log2Ceil (n : Nat) : Nat :=
  if n <= 1 then 0
  else Nat.log2 n + (if 2^(Nat.log2 n) < n then 1 else 0)

/-! ## Structural Circuit -/

/--
Build gates for a single 2:1 MUX (one bit).
Inputs: in0, in1, sel
Output: out
Logic: out = sel ? in1 : in0 = (sel & in1) | (~sel & in0)
wirePrefix: unique identifier to avoid wire name collisions
-/
def mkMux2Bit (wirePrefix : String) (bitIdx : Nat) (in0 in1 sel out : Wire) : List Gate :=
  let notSel := Wire.mk s!"not_sel_{wirePrefix}_{bitIdx}"
  let and0 := Wire.mk s!"and0_{wirePrefix}_{bitIdx}"
  let and1 := Wire.mk s!"and1_{wirePrefix}_{bitIdx}"
  [
    Gate.mkNOT sel notSel,
    Gate.mkAND notSel in0 and0,  -- ~sel & in0
    Gate.mkAND sel in1 and1,     -- sel & in1
    Gate.mkOR and0 and1 out      -- (~sel & in0) | (sel & in1)
  ]

/--
Build gates for a width-bit 2:1 MUX.
Returns gates for all bits in parallel.
wirePrefix: unique identifier to avoid wire name collisions
-/
def mkMux2Gates (wirePrefix : String) (width : Nat) (in0 in1 : List Wire) (sel : Wire) (out : List Wire) : List Gate :=
  (List.range width).foldl
    (fun gates bitIdx =>
      let in0Bit := in0[bitIdx]!
      let in1Bit := in1[bitIdx]!
      let outBit := out[bitIdx]!
      gates ++ mkMux2Bit wirePrefix bitIdx in0Bit in1Bit sel outBit)
    []

/--
Build an N-to-1 MUX tree recursively.

Base case (n=1): Output = input (just buffers)
Recursive case (n>1):
  - Split inputs into two halves
  - Build two subtrees for each half
  - Combine results with top-level MUX using MSB of select

Tree depth = log2(n)
Total MUX gates = n - 1 (one for each non-leaf node)
wirePrefix: unique identifier for wire naming
depth: current tree depth (for unique naming)
-/
def mkMuxTreeGates (wirePrefix : String) (depth : Nat) (n width : Nat) (inputs : List (List Wire)) (selBits : List Wire) (output : List Wire) : List Gate :=
  if n <= 1 then
    -- Base case: n=1, just buffer input to output
    if h : inputs.length > 0 then
      let input0 := inputs.get ⟨0, h⟩
      (List.range width).foldl
        (fun gates bitIdx =>
          gates ++ [Gate.mkBUF (input0[bitIdx]!) (output[bitIdx]!)])
        []
    else
      []
  else if n = 2 then
    -- Base case: 2:1 MUX
    if h : inputs.length >= 2 ∧ selBits.length > 0 then
      let input0 := inputs[0]!
      let input1 := inputs[1]!
      let sel := selBits.get ⟨0, h.right⟩
      mkMux2Gates s!"{wirePrefix}_d{depth}" width input0 input1 sel output
    else
      []
  else
    -- Recursive case: split in half
    let half := (n + 1) / 2  -- Ceiling division
    let leftInputs := inputs.take half
    let rightInputs := inputs.drop half

    -- Intermediate wires for left and right subtree outputs
    let leftOut := makeMultiBitWires s!"{wirePrefix}_left_d{depth}" 1 width |>.head!
    let rightOut := makeMultiBitWires s!"{wirePrefix}_right_d{depth}" 1 width |>.head!

    -- Recursively build left and right subtrees (using lower select bits)
    let lowerSelBits := selBits.take (selBits.length - 1)
    let leftGates := mkMuxTreeGates s!"{wirePrefix}_L" (depth + 1) half width leftInputs lowerSelBits leftOut
    let rightGates := mkMuxTreeGates s!"{wirePrefix}_R" (depth + 1) (n - half) width rightInputs lowerSelBits rightOut

    -- Top-level MUX using MSB of select
    let topSel := selBits.getLast!
    let topGates := mkMux2Gates s!"{wirePrefix}_d{depth}_top" width leftOut rightOut topSel output

    leftGates ++ rightGates ++ topGates

/--
N-to-1 MUX tree: select one of n inputs (each width bits) based on select signal.

Inputs:
  - in{i}_b{j} : Input i, bit j (for i ∈ [0,n), j ∈ [0,width))
  - sel{k} : Select bit k (for k ∈ [0, log2(n)))

Output:
  - out{j} : Output bit j (for j ∈ [0, width))

Structure: Binary tree of 2:1 MUXes
Depth: log2(n)
Gates: (n-1) * width * 4 gates (each bit MUX uses 4 gates: NOT, 2 AND, OR)
-/
def mkMuxTree (n width : Nat) : Circuit :=
  if n = 0 then
    -- Degenerate case
    { name := "Mux0"
      inputs := []
      outputs := makeIndexedWires "out" width
      gates := []
      instances := [] }
  else if n = 1 then
    -- Single input: just buffers
    let input := makeMultiBitWires "in" 1 width |>.head!
    let output := makeIndexedWires "out" width
    let gates := (List.range width).foldl
      (fun gs bitIdx => gs ++ [Gate.mkBUF (input[bitIdx]!) (output[bitIdx]!)])
      []
    { name := s!"Mux{n}x{width}"
      inputs := input.map (·.name) |>.map Wire.mk
      outputs := output
      gates := gates
      instances := [] }
  else
    let numSelBits := log2Ceil n
    let inputWires := makeMultiBitWires "in" n width
    let inputWiresFlat := inputWires.flatten
    let selWires := makeIndexedWires "sel" numSelBits
    let outputWires := makeIndexedWires "out" width

    let gates := mkMuxTreeGates "mux" 0 n width inputWires selWires outputWires

    let allInputs := (inputWiresFlat.map (·.name) |>.map Wire.mk) ++ selWires

    let inputGroups := (List.range n).map (fun i =>
      { name := s!"in{i}"
        width := width
        wires := inputWires[i]! : SignalGroup })

    { name := s!"Mux{n}x{width}"
      inputs := allInputs
      outputs := outputWires
      gates := gates
      instances := []
      -- V2 codegen annotations
      signalGroups := inputGroups ++ [
        { name := "sel", width := numSelBits, wires := selWires },
        { name := "out", width := width, wires := outputWires }
      ]
    }

/-! ## Concrete Examples -/

/-- 2:1 MUX, 8 bits (for testing) -/
def mkMux2x8 : Circuit := mkMuxTree 2 8

/-- 4:1 MUX, 8 bits (for testing) -/
def mkMux4x8 : Circuit := mkMuxTree 4 8

/-- 32:1 MUX, 6 bits (for RAT read ports - reads physical register tags) -/
def mkMux32x6 : Circuit := mkMuxTree 32 6

/-- 64:1 MUX, 32 bits (for PhysRegFile read ports - reads 32-bit register values) -/
def mkMux64x32 : Circuit := mkMuxTree 64 32

end Shoumei.Circuits.Combinational
