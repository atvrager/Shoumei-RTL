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
import Shoumei.Circuits.Sequential.Register

-- Phase 4: RISC-V Components
-- Note: RISC-V Decoder uses dynamic code generation (not static Circuit)
import Shoumei.RISCV.Renaming.RAT
import Shoumei.RISCV.Renaming.FreeList
import Shoumei.RISCV.Renaming.PhysRegFile

-- Phase 5: Execution Units
import Shoumei.RISCV.Execution.IntegerExecUnit
import Shoumei.RISCV.Execution.BranchExecUnit
import Shoumei.RISCV.Execution.MemoryExecUnit
import Shoumei.RISCV.Execution.ReservationStation

-- M-Extension Building Blocks
import Shoumei.Circuits.Combinational.Multiplier
import Shoumei.Circuits.Sequential.Divider
import Shoumei.RISCV.Execution.MulDivExecUnit

-- Phase 6: Retirement
import Shoumei.RISCV.Retirement.ROB

-- Phase 7: Memory
import Shoumei.RISCV.Memory.StoreBuffer
import Shoumei.RISCV.Memory.LSU

-- Phase 8: Top-Level Integration
import Shoumei.RISCV.Fetch
import Shoumei.RISCV.Renaming.RenameStage
import Shoumei.RISCV.CPU

-- Testbench generation
import Shoumei.RISCV.CPUTestbench

open Shoumei.Codegen.Unified
open Shoumei.Examples
open Shoumei.Circuits.Combinational
open Shoumei.Circuits.Sequential
open Shoumei.RISCV
open Shoumei.RISCV.Renaming
open Shoumei.RISCV.Execution
open Shoumei.RISCV.Retirement
open Shoumei.RISCV.Memory
open Shoumei.RISCV.CPU
open Shoumei.RISCV.CPUTestbench

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
  mkDecoder 4,   -- Phase 6: ROB allocation decode (4→16 one-hot)
  mkDecoder 5,
  mkDecoder 6,
  mkComparatorN 6,
  mkMux2x8,
  mkMux4x8,
  mkMuxTree 4 6,
  mkMuxTree 4 32,
  mkMuxTree 8 2,  -- Phase 7: Store buffer size readout
  mkMux8x6,       -- Building block for hierarchical 64:1 muxes
  mkMux8x32,      -- Building block for hierarchical 64:1 muxes
  mkMuxTree 8 32, -- Phase 7: Store buffer forwarding/dequeue data
  mkMuxTree 16 5, -- Phase 6: ROB head archRd readout
  mkMuxTree 16 6, -- Phase 6: ROB head physRd/oldPhysRd readout
  mkMux32x6,
  mkMux64x32Hierarchical,  -- Hierarchical version (9 instances instead of 8064 gates)
  mkMux64x6Hierarchical,   -- Hierarchical version (9 instances instead of 1512 gates)
  mkPriorityArbiter2,
  mkPriorityArbiter4,
  mkPriorityArbiter8,

  -- Phase 3: Queues and Registers
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
  mkQueuePointer 3,  -- Phase 7: Store buffer head/tail pointers
  mkQueuePointer 4,  -- Phase 6: ROB head/tail pointers
  mkQueuePointer 6,
  mkQueueCounterUpDown 2,
  mkQueueCounterUpDown 3,
  mkQueueCounterUpDown 4,  -- Phase 7: Store buffer entry count (0..8)
  mkQueueCounterUpDown 5,  -- Phase 6: ROB entry count (0..16)
  mkQueueCounterUpDown 7,
  -- Power-of-2 register building blocks (verified via LEC)
  mkRegisterN 1,
  mkRegisterN 2,
  mkRegisterN 3,  -- Used in PipelinedMultiplier pipeline
  mkRegisterN 4,
  mkRegisterN 6,  -- Used in PipelinedMultiplier and PhysRegFile
  mkRegisterN 8,
  mkRegisterN 16,
  mkRegisterN 32,
  mkRegisterN 64,
  -- Hierarchical registers (compositional verification)
  mkRegisterNHierarchical 24,  -- Phase 6: ROB entry storage (16+8)
  mkRegisterNHierarchical 68,  -- Phase 7: Store buffer entry storage (64+4)
  mkRegister91Hierarchical,

  -- Phase 4: RISC-V Components
  -- Note: RV32IDecoder generated separately via generate_riscv_decoder
  mkRAT64,
  mkFreeList64,
  mkPhysRegFile64,

  -- Phase 5: Execution Units
  mkIntegerExecUnit,
  mkBranchExecUnit,
  mkMemoryExecUnit,
  mkReservationStation4,

  -- M-Extension (conditional on CPUConfig.enableM)
  mkRippleCarryAdder64,
  csaCompressor64,
  mkPipelinedMultiplier,
  mkDividerCircuit,
  mkMulDivExecUnit,
  mkMulDivRS4,

  -- Phase 6: Retirement
  mkROB16,

  -- Phase 7: Memory
  mkStoreBuffer8,
  mkLSU,

  -- Phase 8: Top-Level Integration
  mkFetchStage,
  mkRenameStage,
  mkCPU_RV32I,
  mkCPU_RV32IM
]

def main : IO Unit := do
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "  証明 Shoumei RTL - Generate All Circuits"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println ""

  -- Initialize output directories
  initOutputDirs

  -- Generate all circuits (pass allCircuits for sub-module port direction lookup)
  let mut count := 0
  for c in allCircuits do
    writeCircuit c allCircuits
    count := count + 1

  -- Generate testbenches
  IO.println ""
  IO.println "Generating testbenches..."
  writeTestbenches cpuTestbenchConfig

  IO.println ""
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println s!"✓ Generated {count} circuits (all 3 formats)"
  IO.println "  SV:      output/sv-from-lean/"
  IO.println "  Chisel:  chisel/src/main/scala/generated/"
  IO.println "  SystemC: output/systemc/"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
