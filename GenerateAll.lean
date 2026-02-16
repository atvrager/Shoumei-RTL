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
import Shoumei.Circuits.Combinational.OneHotEncoder

-- Phase 3: Sequential Components
import Shoumei.Circuits.Sequential.QueueN
import Shoumei.Circuits.Sequential.QueueComponents
import Shoumei.Circuits.Sequential.Register

-- Phase 4: RISC-V Components
import Shoumei.RISCV.CodegenTest  -- RISC-V decoder generation (dynamic, from riscv-opcodes)
import Shoumei.RISCV.InstructionList
import Shoumei.RISCV.Renaming.RAT
import Shoumei.RISCV.Renaming.FreeList
import Shoumei.RISCV.Renaming.BitmapFreeList
import Shoumei.RISCV.Renaming.PhysRegFile

-- Phase 5: Execution Units
import Shoumei.RISCV.Execution.IntegerExecUnit
import Shoumei.RISCV.Execution.BranchExecUnit
import Shoumei.RISCV.Execution.MemoryExecUnit
import Shoumei.RISCV.Execution.ReservationStation

-- M-Extension Building Blocks
import Shoumei.Circuits.Combinational.KoggeStoneAdder
import Shoumei.Circuits.Combinational.Multiplier
import Shoumei.Circuits.Sequential.Divider
import Shoumei.RISCV.Execution.MulDivExecUnit

-- F-Extension
import Shoumei.Circuits.Combinational.FPUnpack
import Shoumei.Circuits.Combinational.FPPack
import Shoumei.Circuits.Combinational.FPMisc
import Shoumei.Circuits.Sequential.FPAdder
import Shoumei.Circuits.Sequential.FPMultiplier
import Shoumei.Circuits.Sequential.FPFMA
import Shoumei.Circuits.Sequential.FPDivider
import Shoumei.Circuits.Sequential.FPSqrt
import Shoumei.RISCV.Execution.FPExecUnit

-- Phase 6: Retirement
import Shoumei.RISCV.Retirement.ROB
import Shoumei.RISCV.Retirement.Queue16x32

-- Phase 7: Memory
import Shoumei.Circuits.Combinational.Popcount
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
  mkQueue1StructuralComplete 39,  -- CDB result FIFOs (6 tag + 32 data + 1 is_fp_rd)
  mkQueue1FlowStructural 39,     -- CDB result FIFOs with flow-through bypass
  mkQueue1FlowStructural 72,     -- INT/Branch CDB FIFO (39 + 32 redirect_target + 1 mispredicted)

  -- Phase 1: Arithmetic
  mkRippleCarryAdder4,
  mkRippleCarryAdder8,
  mkRippleCarryAdder32,
  mkKoggeStoneAdder32,
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
  mkEqualityComparatorN 6,
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
  mkMuxTree 16 32, -- Phase 8: RVVI Queue16x32 read mux
  mkMux32x6,
  mkMux64x32Hierarchical,  -- Hierarchical version (9 instances instead of 8064 gates)
  mkMux64x6Hierarchical,   -- Hierarchical version (9 instances instead of 1512 gates)
  mkPriorityArbiter2,
  mkPriorityArbiter4,
  mkPriorityArbiter8,
  mkPriorityArbiter64,  -- Bitmap free list allocation
  mkOneHotEncoder64,    -- Bitmap free list one-hot to binary
  mkPopcount8,  -- Phase 7: Store buffer flush recovery

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
  mkQueuePointer 3,  -- Phase 7: Store buffer head pointer
  mkQueuePointerLoadable 3,  -- Phase 7: Store buffer tail pointer (loadable for flush)
  mkQueuePointerLoadable 6,  -- Free list head pointer (loadable for flush)
  mkQueuePointer 4,  -- Phase 6: ROB head/tail pointers
  mkQueuePointer 6,
  mkQueueCounterUpDown 2,
  mkQueueCounterUpDown 3,
  mkQueueCounterUpDown 4,  -- Phase 7: Store buffer entry count (0..8)
  mkQueueCounterLoadable 4,  -- Phase 7: Store buffer loadable count (flush recovery)
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
  mkRegisterNHierarchical 66,  -- Phase 7: Store buffer entry payload (32+32+2)
  mkRegisterNHierarchical 68,  -- Phase 7: Store buffer entry storage (64+4)
  mkRegister91Hierarchical,

  -- Phase 3b: Flushable Queue Components
  mkQueueRAMInit 64 6 (fun i => i + 32),
  mkQueuePointerInit 6 32,
  mkQueueCounterLoadableInit 7 32,
  mkQueueNFlushable 64 6 32 (fun i => i + 32),

  -- Phase 4: RISC-V Components
  mkRAT64,
  mkFreeList64,
  mkFreeList64Flushable,
  mkBitmapFreeList64,
  mkPhysRegFile64,

  -- Phase 5: Execution Units
  mkIntegerExecUnit,
  mkBranchExecUnit,
  mkMemoryExecUnit,
  mkReservationStation4,
  mkMemoryRS4,

  -- M-Extension (conditional on CPUConfig.enableM)
  mkRippleCarryAdder64,
  mkKoggeStoneAdder64,
  csaCompressor64,
  mkPipelinedMultiplier,
  mkDividerCircuit,
  mkMulDivExecUnit,
  mkMulDivRS4,

  -- F-Extension: FPU building blocks
  fpUnpackCircuit,
  fpPackCircuit,
  fpMiscCircuit,
  fpAdderCircuit,
  fpMultiplierCircuit,
  fpFMACircuit,
  fpDividerCircuit,
  fpSqrtCircuit,
  mkFPExecUnit,

  -- Phase 6: Retirement
  mkROB16,
  mkQueue16x32,  -- Phase 8: RVVI PC/instruction queues

  -- Phase 7: Memory
  mkStoreBuffer8,
  mkLSU,

  -- Phase 8: Top-Level Integration
  mkFetchStage,
  mkRenameStage,
  mkCPU_RV32I,
  mkCPU_RV32IM,
  mkCPU_RV32IF,
  mkCPU_RV32IMF
]

def main (args : List String) : IO Unit := do
  let force := args.contains "--force"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "  証明 Shoumei RTL - Generate All Circuits"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  if force then
    IO.println "  (--force: regenerating all circuits)"
  IO.println ""

  -- Initialize output directories
  initOutputDirs

  -- Pre-compute dependency-aware hashes for incremental generation
  let hashMap := computeAllHashes allCircuits

  -- Generate all circuits (pass allCircuits for sub-module port direction lookup)
  let mut count := 0
  let mut skipped := 0
  for c in allCircuits do
    let wasCached ← if !force then
      if let some h := Shoumei.Codegen.Unified.lookupHash hashMap c.name then
        isUpToDate c.name h
      else pure false
    else pure false
    writeCircuit c allCircuits force hashMap
    if wasCached then skipped := skipped + 1
    count := count + 1

  -- Generate RISC-V decoders (from riscv-opcodes instruction definitions)
  IO.println ""
  IO.println "Generating RISC-V decoders..."
  -- Auto-generate opcodes JSON if missing
  let opcodesPath := Shoumei.RISCV.instrDictPath
  unless (← opcodesPath.pathExists) do
    IO.println "  instr_dict.json not found, running 'make opcodes'..."
    let result ← IO.Process.run { cmd := "make", args := #["opcodes"] }
    unless result.isEmpty do
      IO.println result
  let defs ← Shoumei.RISCV.loadInstrDictFromFile opcodesPath
  Shoumei.RISCV.generateDecoders defs

  -- Generate testbenches
  IO.println ""
  IO.println "Generating testbenches..."
  writeTestbenches cpuTestbenchConfig

  -- Generate filelist.f for each output directory
  IO.println ""
  IO.println "Generating filelists..."
  writeFilelist svOutputDir ".sv"
  writeFilelist svNetlistOutputDir ".sv"
  writeFilelist chiselOutputDir ".scala"
  writeFilelist systemcOutputDir ".h"
  writeFilelist asap7OutputDir ".sv"
  IO.println "✓ Generated filelist.f in each output directory"

  IO.println ""
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  if skipped > 0 then
    IO.println s!"✓ Generated {count - skipped} circuits, skipped {skipped} unchanged"
  else
    IO.println s!"✓ Generated {count} circuits (all formats)"
  IO.println "  SV:      output/sv-from-lean/"
  IO.println "  Chisel:  chisel/src/main/scala/generated/"
  IO.println "  SystemC: output/systemc/"
  IO.println "  ASAP7:   output/sv-asap7/ (tech-mapped modules)"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
