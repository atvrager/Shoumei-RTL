/-
Circuits/Sequential/Register.lean - Parameterized N-bit Register

A configurable-width register built from N parallel D flip-flops or hierarchically from
power-of-2 building blocks for compositional verification.

Behavior:
- On rising edge of clock:
  - If reset is high: all bits become 0
  - Otherwise: each output q[i] captures its input d[i]
-/

import Shoumei.DSL

namespace Shoumei.Circuits.Sequential

open Shoumei

-- Helper: Create a list of wires with indexed names
def makeIndexedWires (name : String) (n : Nat) : List Wire :=
  (List.range n).map (fun i => Wire.mk s!"{name}_{i}")

/-! ## Flat Register Construction (for small power-of-2 sizes) -/

-- Build an N-bit register from N parallel DFFs
-- Used for power-of-2 building blocks that will be verified via LEC
def mkRegisterN (n : Nat) : Circuit :=
  let d_wires := makeIndexedWires "d" n
  let q_wires := makeIndexedWires "q" n
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"

  let gates := List.zipWith (fun d q => Gate.mkDFF d clock reset q) d_wires q_wires

  { name := s!"Register{n}"
    inputs := d_wires ++ [clock, reset]
    outputs := q_wires
    gates := gates
    instances := []
    -- V2 codegen annotations
    signalGroups := [
      { name := "d", width := n, wires := d_wires },
      { name := "q", width := n, wires := q_wires }
    ]
  }

/-! ## Hierarchical Register Construction (for arbitrary sizes) -/

-- Decompose N into powers of 2 for hierarchical building
-- E.g., 91 = 64 + 16 + 8 + 2 + 1
partial def decomposeToPowersOf2 (n : Nat) : List Nat :=
  if n == 0 then []
  else if n >= 64 then 64 :: decomposeToPowersOf2 (n - 64)
  else if n >= 32 then 32 :: decomposeToPowersOf2 (n - 32)
  else if n >= 16 then 16 :: decomposeToPowersOf2 (n - 16)
  else if n >= 8 then 8 :: decomposeToPowersOf2 (n - 8)
  else if n >= 4 then 4 :: decomposeToPowersOf2 (n - 4)
  else if n >= 2 then 2 :: decomposeToPowersOf2 (n - 2)
  else [1]

-- Build RegisterN hierarchically from power-of-2 building blocks
-- This allows LEC verification of small blocks + compositional proof for large N
def mkRegisterNHierarchical (n : Nat) : Circuit :=
  let d_wires := makeIndexedWires "d" n
  let q_wires := makeIndexedWires "q" n
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"

  -- Decompose into power-of-2 chunks
  let chunks := decomposeToPowersOf2 n
  
  -- Build instances for each chunk
  let rec buildInstances (chunks : List Nat) (startBit : Nat) : List CircuitInstance :=
    match chunks with
    | [] => []
    | width :: rest =>
        let inst : CircuitInstance := {
          moduleName := s!"Register{width}"
          instName := s!"reg_{startBit}_to_{startBit + width - 1}"
          portMap :=
            -- Connect d inputs
            (List.range width).map (fun i =>
              (s!"d_{i}", d_wires[startBit + i]!)
            ) ++
            -- Connect clock and reset
            [("clock", clock), ("reset", reset)] ++
            -- Connect q outputs
            (List.range width).map (fun i =>
              (s!"q_{i}", q_wires[startBit + i]!)
            )
        }
        inst :: buildInstances rest (startBit + width)
  
  let instances := buildInstances chunks 0

  { name := s!"Register{n}"
    inputs := d_wires ++ [clock, reset]
    outputs := q_wires
    gates := []  -- No gates, only instances
    instances := instances
    -- V2 codegen annotations
    signalGroups := [
      { name := "d", width := n, wires := d_wires },
      { name := "q", width := n, wires := q_wires }
    ]
  }

/-! ## Convenience Definitions -/

-- Power-of-2 registers (for LEC verification)
def mkRegister1 : Circuit := mkRegisterN 1
def mkRegister2 : Circuit := mkRegisterN 2
def mkRegister4 : Circuit := mkRegisterN 4
def mkRegister8 : Circuit := mkRegisterN 8
def mkRegister16 : Circuit := mkRegisterN 16
def mkRegister32 : Circuit := mkRegisterN 32
def mkRegister64 : Circuit := mkRegisterN 64

-- Large registers (hierarchical, compositional verification)
def mkRegister91Hierarchical : Circuit := mkRegisterNHierarchical 91

-- Helper: Extract the number of DFFs in a register circuit
def registerWidth (c : Circuit) : Nat :=
  c.gates.filter (fun g => g.gateType.isDFF) |>.length

end Shoumei.Circuits.Sequential
