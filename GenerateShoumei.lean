/-
GenerateShoumei.lean - Emit all circuits as .shoumei text files

Usage: lake exe generate_shoumei
-/

import Shoumei.Codegen.ShoumeiEmit
import Shoumei.Codegen.ShoumeiParse
import Shoumei.Codegen.SystemVerilog

-- Import all circuit definitions (same as GenerateAll.lean)
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
import Shoumei.RISCV.CodegenTest
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
import Shoumei.RISCV.Config

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

-- Testbench generation (temporarily removed due to missing file)

open Shoumei.Codegen.ShoumeiEmit
open Shoumei.Codegen.ShoumeiParse
open Shoumei.Codegen.SystemVerilog
open Shoumei.Examples
open Shoumei.Circuits.Combinational
open Shoumei.Circuits.Sequential
open Shoumei.RISCV
open Shoumei.RISCV.Renaming
open Shoumei.RISCV.Execution
open Shoumei.RISCV.Retirement
open Shoumei.RISCV.Memory
open Shoumei.RISCV.CPU

-- Use the same allCircuits list from GenerateAll
def allCircuits : List Circuit := [
  -- Phase 0: Foundation
  fullAdderCircuit,
  dff,
  mkQueue1StructuralComplete 8,
  mkQueue1StructuralComplete 32,
  mkQueue1StructuralComplete 39,
  mkQueue1FlowStructural 39,
  mkQueue1FlowStructural 72,

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
  mkDecoder 4,
  mkDecoder 5,
  mkDecoder 6,
  mkComparatorN 6,
  mkEqualityComparatorN 6,
  mkMux2x8,
  mkMux4x8,
  mkMuxTree 4 6,
  mkMuxTree 4 32,
  mkMuxTree 8 2,
  mkMux8x6,
  mkMux8x32,
  mkMuxTree 8 32,
  mkMuxTree 16 5,
  mkMuxTree 16 6,
  mkMuxTree 16 32,
  mkMux32x6,
  mkMux64x32Hierarchical,
  mkMux64x6Hierarchical,
  mkPriorityArbiter2,
  mkPriorityArbiter4,
  mkPriorityArbiter8,
  mkPriorityArbiter64,
  mkOneHotEncoder64,
  mkPopcount8,

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
  mkQueuePointer 3,
  mkQueuePointerLoadable 3,
  mkQueuePointerLoadable 6,
  mkQueuePointer 4,
  mkQueuePointer 6,
  mkQueueCounterUpDown 2,
  mkQueueCounterUpDown 3,
  mkQueueCounterUpDown 4,
  mkQueueCounterLoadable 4,
  mkQueueCounterUpDown 5,
  mkQueueCounterUpDown 7,
  mkRegisterN 1,
  mkRegisterN 2,
  mkRegisterN 3,
  mkRegisterN 4,
  mkRegisterN 6,
  mkRegisterN 8,
  mkRegisterN 16,
  mkRegisterN 32,
  mkRegisterN 64,
  mkRegisterNHierarchical 24,
  mkRegisterNHierarchical 66,
  mkRegisterNHierarchical 68,
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
  mkPhysRegFile64,

  -- Phase 5: Execution Units
  mkIntegerExecUnit,
  mkBranchExecUnit,
  mkMemoryExecUnit,
  mkReservationStationFromConfig defaultCPUConfig,

  -- M-Extension
  mkRippleCarryAdder64,
  mkKoggeStoneAdder64,
  csaCompressor64,
  mkPipelinedMultiplier,
  mkDividerCircuit,
  mkMulDivExecUnit,
  -- TODO: mkMulDivRS removed in W=2 unification

  -- F-Extension
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
  mkQueue16x32,

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

def main : IO Unit := do
  IO.FS.createDirAll "output/shoumei"

  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "  証明 Shoumei RTL - Generate .shoumei files"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println ""

  let mut count := 0
  for c in allCircuits do
    let text := emitCircuit c allCircuits
    let path := s!"output/shoumei/{c.name}.shoumei"
    IO.FS.writeFile path text
    count := count + 1

  IO.println s!"  Emitted {count} .shoumei files"
  IO.println ""

  -- Phase 2: Round-trip parse → SV generation
  IO.println "  Round-trip: parse .shoumei → generate SV"
  IO.FS.createDirAll "output/sv-roundtrip"
  let mut parseOk := 0
  let mut parseFail := 0
  for c in allCircuits do
    let path := s!"output/shoumei/{c.name}.shoumei"
    let text ← IO.FS.readFile path
    match parseShoumei text with
    | .ok parsed =>
      let sv := generateModule parsed allCircuits
      IO.FS.writeFile s!"output/sv-roundtrip/{c.name}.sv" sv
      parseOk := parseOk + 1
    | .error err =>
      IO.eprintln s!"  PARSE ERROR: {c.name}: {err}"
      parseFail := parseFail + 1

  IO.println ""
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println s!"✓ Generated {count} .shoumei files"
  IO.println s!"✓ Round-trip: {parseOk} OK, {parseFail} failed"
  IO.println "  Output: output/shoumei/, output/sv-roundtrip/"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
