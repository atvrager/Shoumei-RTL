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
-- Used for power-of-2 building blocks (the flat DFF registers)
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
    svaProperties := [
      .ResetClears "q",
      .DataCapture "d" "q"
    ]
  }

/-! ## Hierarchical Register Construction (for arbitrary sizes) -/

-- Decompose N into powers of 2 for hierarchical building
-- E.g., 91 = 64 + 16 + 8 + 2 + 1
def decomposeToPowersOf2 (n : Nat) : List Nat :=
  if n == 0 then []
  else if n >= 64 then 64 :: decomposeToPowersOf2 (n - 64)
  else if n >= 32 then 32 :: decomposeToPowersOf2 (n - 32)
  else if n >= 16 then 16 :: decomposeToPowersOf2 (n - 16)
  else if n >= 8 then 8 :: decomposeToPowersOf2 (n - 8)
  else if n >= 4 then 4 :: decomposeToPowersOf2 (n - 4)
  else if n >= 2 then 2 :: decomposeToPowersOf2 (n - 2)
  else [1]

-- Build RegisterN hierarchically from power-of-2 building blocks
-- This keeps the small blocks separate, so a large N is a composition of them
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
    svaProperties := [
      .ResetClears "q",
      .DataCapture "d" "q"
    ]
  }

/-! ## Convenience Definitions -/

-- Power-of-2 registers (the building blocks of the hierarchical registers)
def mkRegister1 : Circuit := mkRegisterN 1
def mkRegister2 : Circuit := mkRegisterN 2
def mkRegister4 : Circuit := mkRegisterN 4
def mkRegister8 : Circuit := mkRegisterN 8
def mkRegister12 : Circuit := mkRegisterN 12
def mkRegister16 : Circuit := mkRegisterN 16
def mkRegister32 : Circuit := mkRegisterN 32
def mkRegister64 : Circuit := mkRegisterN 64

-- Large registers (hierarchical, compositional verification)
def mkRegister91Hierarchical : Circuit := mkRegisterNHierarchical 91
def mkRegister96Hierarchical : Circuit := mkRegisterNHierarchical 96
def mkRegister98Hierarchical : Circuit := mkRegisterNHierarchical 98
def mkRegister130Hierarchical : Circuit := mkRegisterNHierarchical 130
def mkRegister157Hierarchical : Circuit := mkRegisterNHierarchical 157
def mkRegister158Hierarchical : Circuit := mkRegisterNHierarchical 158
def mkRegister159Hierarchical : Circuit := mkRegisterNHierarchical 159
def mkRegister160Hierarchical : Circuit := mkRegisterNHierarchical 160

-- Flat counterparts for Sequential Equivalence Checking (SEC) miters
def mkRegisterFlat (n : Nat) : Circuit := { mkRegisterN n with name := s!"Register{n}Flat" }
def mkRegister160Flat : Circuit := mkRegisterFlat 160


-- Helper: Extract the number of DFFs in a register circuit
def registerWidth (c : Circuit) : Nat :=
  c.gates.filter (fun g => g.gateType.isDFF) |>.length

/-! ## Clock-Enabled Registers (Strobe / Retention Support) -/

/-- Build an N-bit register with clock enable (strobe).
    Each bit combines a 2-to-1 MUX and a DFF: next_d = en ? d : q. -/
def mkRegisterEnN (n : Nat) : Circuit :=
  let d_wires := makeIndexedWires "d" n
  let q_wires := makeIndexedWires "q" n
  let next_d_wires := makeIndexedWires "next_d" n
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let en := Wire.mk "en"

  let mux_gates := (List.range n).map (fun i => Gate.mkMUX q_wires[i]! d_wires[i]! en next_d_wires[i]!)
  let dff_gates := (List.range n).map (fun i => Gate.mkDFF next_d_wires[i]! clock reset q_wires[i]!)
  let gates := mux_gates ++ dff_gates

  { name := s!"RegisterEn{n}"
    inputs := d_wires ++ [clock, reset, en]
    outputs := q_wires
    gates := gates
    instances := []
    signalGroups := [
      { name := "d", width := n, wires := d_wires },
      { name := "q", width := n, wires := q_wires }
    ]
    svaProperties := [
      .ResetClears "q",
      .EnableHolds "en" "q",
      .EnableCapture "en" "d" "q"
    ]
  }

def mkRegisterEn1 : Circuit := mkRegisterEnN 1
def mkRegisterEn2 : Circuit := mkRegisterEnN 2
def mkRegisterEn4 : Circuit := mkRegisterEnN 4
def mkRegisterEn8 : Circuit := mkRegisterEnN 8
def mkRegisterEn16 : Circuit := mkRegisterEnN 16
def mkRegisterEn32 : Circuit := mkRegisterEnN 32
def mkRegisterEn64 : Circuit := mkRegisterEnN 64

end Shoumei.Circuits.Sequential
