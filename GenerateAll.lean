/-
GenerateAll.lean - Centralized Code Generation for All Circuits

Single entry point for generating all circuits in the project.
Just add your circuit here and it gets all 3 output formats automatically.

Usage: lake exe generate_all
-/

import Shoumei.Codegen.Unified

-- Phase 0: Foundation
import Shoumei.Examples.Adder
import Shoumei.Circuits.Sequential.DFF
import Shoumei.Circuits.Sequential.Queue

-- Phase 1: Arithmetic Building Blocks
import Shoumei.Circuits.Combinational.RippleCarryAdder
import Shoumei.Circuits.Combinational.Subtractor
import Shoumei.Circuits.Combinational.Comparator
import Shoumei.Circuits.Combinational.LogicUnit
import Shoumei.Circuits.Combinational.Shifter
import Shoumei.Circuits.Combinational.ALU

-- Phase 2: Decoders and Muxes
import Shoumei.Circuits.Combinational.Decoder
import Shoumei.Circuits.Combinational.MuxTree
import Shoumei.Circuits.Combinational.Arbiter

-- Phase 3: Sequential Components
import Shoumei.Circuits.Sequential.QueueN
import Shoumei.Circuits.Sequential.QueueComponents

-- Phase 4: RISC-V Components
-- Note: RISC-V Decoder uses dynamic code generation (not static Circuit)
import Shoumei.RISCV.Renaming.RAT
import Shoumei.RISCV.Renaming.FreeList
import Shoumei.RISCV.Renaming.PhysRegFile

-- Phase 5: Execution Units
import Shoumei.RISCV.Execution.IntegerExecUnit

open Shoumei.Codegen.Unified
open Shoumei.Examples
open Shoumei.Circuits.Combinational
open Shoumei.Circuits.Sequential
open Shoumei.RISCV.Renaming
open Shoumei.RISCV.Execution

-- Registry: Add circuits here for automatic generation
def allCircuits : List Circuit := [
  -- Phase 0: Foundation
  fullAdderCircuit,
  dff,
  mkQueue1StructuralComplete 8,
  mkQueue1StructuralComplete 32,

  -- Phase 1: Arithmetic
  mkRippleCarryAdder4,
  mkRippleCarryAdder8,
  mkRippleCarryAdder32,
  mkSubtractor4,
  mkSubtractor8,
  mkSubtractor32,
  mkComparator4,
  mkComparator8,
  mkComparator32,
  mkLogicUnit4,
  mkLogicUnit8,
  mkLogicUnit32,
  mkShifter4,
  mkShifter32,
  mkALU32,

  -- Phase 2: Decoders and Muxes
  mkDecoder 1,
  mkDecoder 2,
  mkDecoder 3,
  mkDecoder 5,
  mkDecoder 6,
  mkMux2x8,
  mkMux4x8,
  mkMux32x6,
  mkMux64x32,
  mkMuxTree 64 6,
  mkPriorityArbiter2,
  mkPriorityArbiter4,
  mkPriorityArbiter8,

  -- Phase 3: Queues
  mkQueueNStructural 2 8,
  mkQueueNStructural 4 8,
  mkQueueNStructural 64 6,
  mkQueueNStructural 64 32,
  mkQueueRAM 2 8,
  mkQueueRAM 4 8,
  mkQueueRAM 64 6,
  mkQueueRAM 64 32,
  mkQueuePointer 1,
  mkQueuePointer 2,
  mkQueuePointer 6,
  mkQueueCounterUpDown 2,
  mkQueueCounterUpDown 3,
  mkQueueCounterUpDown 7,

  -- Phase 4: RISC-V Components
  -- Note: RV32IDecoder generated separately via generate_riscv_decoder
  mkRAT64,
  mkFreeList64,
  mkPhysRegFile64,

  -- Phase 5: Execution Units
  mkIntegerExecUnit
]

def main : IO Unit := do
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "  証明 Shoumei RTL - Generate All Circuits"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println ""

  -- Initialize output directories
  initOutputDirs

  -- Generate all circuits
  let mut count := 0
  for c in allCircuits do
    writeCircuit c
    count := count + 1

  IO.println ""
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println s!"✓ Generated {count} circuits (all 3 formats)"
  IO.println "  SV:      output/sv-from-lean/"
  IO.println "  Chisel:  chisel/src/main/scala/generated/"
  IO.println "  SystemC: output/systemc/"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
