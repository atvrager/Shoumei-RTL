/-
GenerateAll.lean - Centralized Code Generation for All Circuits

Single entry point for generating all circuits in the project.
Just add your circuit here and it gets all 3 output formats automatically.

Usage: lake exe generate_all
-/

import Shoumei.Codegen.Unified
import Shoumei.Verification.ExportCerts

-- Phase 0: Foundation
import Shoumei.Examples.Adder
import Shoumei.Circuits.Sequential.DFF
import Shoumei.Circuits.Sequential.Queue

-- Phase 1: Arithmetic Building Blocks
import Shoumei.Circuits.Combinational.PCIncrementer
import Shoumei.Circuits.Combinational.BranchTargetAdder
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
import Shoumei.RISCV.Renaming.RenameStage

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

-- D-Extension
import Shoumei.Circuits.Combinational.FPDoubleMisc
import Shoumei.Circuits.Combinational.FPDoubleConverter
import Shoumei.Circuits.Combinational.FPLongConverter
import Shoumei.Circuits.Sequential.FPAdderD
import Shoumei.Circuits.Sequential.FPMultiplierD
import Shoumei.Circuits.Sequential.FPFMAD
import Shoumei.Circuits.Sequential.FPDividerD
import Shoumei.Circuits.Sequential.FPSqrtD

-- Phase 6: Retirement
import Shoumei.RISCV.Retirement.ROB
import Shoumei.RISCV.Retirement.Queue16x32

-- Phase 7: Memory
import Shoumei.Circuits.Combinational.Popcount
import Shoumei.RISCV.Memory.StoreBuffer
import Shoumei.RISCV.Memory.LSU

-- Phase 7b: Cache Hierarchy
import Shoumei.RISCV.Memory.Cache.L1ICache
import Shoumei.RISCV.Memory.Cache.L1DCache
import Shoumei.RISCV.Memory.Cache.L2Cache
import Shoumei.RISCV.Memory.Cache.MemoryHierarchy
import Shoumei.RISCV.Memory.Cache.CachedCPU

-- Phase 8a: Microcode Sequencer
import Shoumei.RISCV.Microcode.MicrocodeSequencerCodegen
import Shoumei.RISCV.Microcode.TrapSequencerCodegen

-- Phase 8: Top-Level Integration
import Shoumei.RISCV.Fetch
import Shoumei.RISCV.CDBMux
import Shoumei.RISCV.CSRFile
import Shoumei.RISCV.CPU.BusyBitTable
import Shoumei.RISCV.CPU

-- Testbench generation
import Shoumei.RISCV.CPUTestbench
import Shoumei.RISCV.TraceSchema

open Shoumei.Codegen.Unified
open Shoumei.Examples
open Shoumei.Circuits.Combinational
open Shoumei.Circuits.Sequential
open Shoumei.RISCV
open Shoumei.RISCV.Renaming
open Shoumei.RISCV.Execution
open Shoumei.RISCV.Retirement
open Shoumei.RISCV.Memory
open Shoumei.RISCV.Memory.Cache
open Shoumei.RISCV.CPU
open Shoumei.RISCV.Microcode
open Shoumei.RISCV.CPUTestbench

/-- Decoder modules generated from riscv-opcodes instruction definitions, outside
    the circuit registry above.  Named once because the stale-output pruner and
    the certificate registry must both agree with what is actually emitted. -/
def riscvDecoderModules : List String :=
  ["RV64GDecoder"]

-- Registry: Add circuits here for automatic generation
def allCircuits : List Circuit := [
  -- Phase 0: Foundation
  dff,
  mkQueue1FlowStructural 39,     -- CDB result FIFOs with flow-through bypass
  mkQueue1FlowStructural 70,     -- 64-bit result FIFOs (tag6 + data64)
  mkQueue1FlowStructural 71,     -- FP result FIFO (tag6 + data64 + is_fp)
  mkQueue1FlowStructural 72,     -- INT/Branch CDB FIFO (39 + 32 redirect_target + 1 mispredicted)
  mkQueue1FlowStructural 103,    -- 64-bit Branch CDB FIFO (tag6 + data64 + 32 redir + 1 mispred)
  mkQueue1FlowStructural 104,    -- 64-bit CDB FIFO (IB0 / IB_BR)

  -- Phase 1: Arithmetic
  pcIncrementer4Circuit,
  pcIncrementer8Circuit,
  branchTargetAdder32Circuit,
  mkKoggeStoneAdder32,
  mkKoggeStoneAdder32NoCin,
  mkSubtractor32,
  mkComparator32,
  mkLogicUnit32,
  mkShifter32,
  mkALU32,

  -- Phase 2: Decoders and Muxes
  mkDecoder 2,
  mkDecoder 3,
  mkDecoder 4,   -- Phase 6: ROB allocation decode (4→16 one-hot)
  mkDecoder 5,
  mkDecoder 6,
  mkComparatorN 6,
  mkEqualityComparatorN 6,
  mkEqualityComparator32,  -- Phase 7: Store buffer address matching (XOR + OR-tree)
  mkEqualityComparator64,  -- Phase 7: 64-bit store buffer address matching
  mkMuxTree 4 32,
  mkMuxTree 4 64,
  mkMuxTree 8 2,  -- Phase 7: Store buffer size readout
  mkMux8x32Hierarchical, -- Hierarchical 8:1 (2× Mux4x32 + sel buffers)
  mkMux8x64Hierarchical, -- Hierarchical 8:1 64-bit
  mkMuxTree 16 5, -- Phase 6: ROB head archRd readout
  mkMuxTree 16 6, -- Phase 6: ROB head physRd/oldPhysRd readout
  mkMuxTree 16 32, -- Phase 8: RVVI Queue16x32 read mux
  mkMux32x6,
  mkMux64x32Hierarchical,  -- Hierarchical version (9 instances instead of 8064 gates)
  mkMux64x64Hierarchical,  -- Hierarchical version 64-bit
  mkPriorityArbiter2,
  mkPriorityArbiter8,
  mkPriorityArbiter64,  -- Bitmap free list allocation
  mkOneHotEncoder64,    -- Bitmap free list one-hot to binary
  mkPopcount8,  -- Phase 7: Store buffer flush recovery

  -- Phase 3: Queues and Registers
  mkQueuePointer 3,  -- Phase 7: Store buffer head pointer
  mkQueuePointerLoadable 3,  -- Phase 7: Store buffer tail pointer (loadable for flush)
  mkQueueCounterLoadable 4,  -- Phase 7: Store buffer loadable count (flush recovery)
  -- Power-of-2 register building blocks
  mkRegisterN 1,
  mkRegisterN 2,
  mkRegisterN 3,  -- Used in PipelinedMultiplier pipeline
  mkRegisterN 4,
  mkRegisterN 6,  -- Used in PipelinedMultiplier and PhysRegFile
  mkRegisterN 8,
  mkRegisterN 12,
  mkRegisterN 16,
  mkRegisterN 32,
  mkRegisterN 64,
  -- Hierarchical registers (compositional verification)
  mkRegisterNHierarchical 96,  -- RS entry: 8-bit opcode + 7-bit tags (1+8+7+1+7+32+1+7+32)
  mkRegisterNHierarchical 98,  -- Store buffer entry payload (32+64+2)
  mkRegisterNHierarchical 130, -- Store buffer 64-bit entry payload (64+64+2)
  mkRegisterNHierarchical 157, -- Specialized RS 64-bit entry
  mkRegisterNHierarchical 158,
  mkRegisterNHierarchical 159,
  mkRegisterNHierarchical 160, -- RS 64-bit entry (1+8+7+1+7+64+1+7+64)

  -- Phase 4: RISC-V Components
  mkRAT64,
  mkIntRAT64,
  mkCRAT64,
  mkBitmapFreeList64_W2,
  mkBitmapFreeList64_W1,
  mkPhysRegFile64,
  mkPhysRegFile64x64,
  mkIntPhysRegFile 64 32,
  mkIntPhysRegFile 64 64,
  mkFPPhysRegFile 64 32,
  mkFPPhysRegFile 64 64,

  -- Phase 5: Execution Units
  mkIntegerExecUnit,
  mkBranchExecUnit,
  mkMemoryExecUnit,
  mkMemoryExecUnitDecoupled,
  mkReservationStationFromConfig defaultCPUConfig,
  mkReservationStation4W2_64,
  mkIntReservationStation4_W2 64,
  mkReservationStation2_W1 64,
  mkMemoryReservationStation2_W1 64,
  mkFPReservationStation2_W1 64,

  -- M-Extension & 64-bit Arithmetic Building Blocks
  mkKoggeStoneAdder64,
  mkKoggeStoneAdder64NoCin,
  koggeStoneAdder64WithCin1,
  mkMulFinalAdder64,
  koggeStoneAdder106,
  koggeStoneAdder106NoCin,
  mkSubtractor64,
  mkComparator64,
  mkLogicUnit64,
  mkShifter64,
  mkALU64,
  mkIntegerExecUnit64,
  csaCompressor48,
  csaCompressor64,
  csaCompressor106,
  mul32x32To64,
  mkPipelinedMultiplier,
  pipelinedMultiplier64,
  mkDividerCircuit,
  divider64Circuit,
  mkMulDivExecUnit,

  -- F-Extension: FPU building blocks
  fpSgnjCircuit,
  fpCompareCircuit,
  fpClassCircuit,
  fpCvtIntCircuit,
  fpMiscCircuit,
  fpAdder_Stage1Circuit,
  fpAdder_Stage2Circuit,
  fpAdder_Stage3Circuit,
  fpAdder_Stage4Circuit,
  fpAdderCircuit,
  fpMultiplierCircuit,
  fpFMACircuit,
  fpDividerCircuit,
  fpSqrtCircuit,
  mkFPExecUnit,

  -- D-Extension: Double-Precision FPU building blocks
  fpDoubleMiscCircuit,
  fpDoubleConverterCircuit,
  int64ToFPCircuit,
  fpToInt64Circuit,
  fpLongConverterCircuit,
  fpAdderD_Stage1Circuit,
  fpAdderD_Stage2Circuit,
  fpAdderD_Stage3Circuit,
  fpAdderD_Stage4Circuit,
  fpAdderDCircuit,
  fpMultiplierDCircuit,
  fpFMADCircuit,
  fpDividerDCircuit,
  fpSqrtDCircuit,
  fpExecUnitD,

  -- Phase 6: Retirement
  mkROB16,
  mkQueue16x32_DualPort,  -- W=2 dual-port RVVI PC/instruction queues

  -- Phase 7: Memory
  mkStoreBuffer8,
  mkLSU,

  -- Phase 7b: Cache Hierarchy Building Blocks
  mkRegisterN 24,   -- L1I/L2 tag storage (24-bit tags)
  mkRegisterN 25,   -- L1D tag storage (25-bit tags)
  mkEqualityComparatorN 24,     -- L1I/L2 tag comparison
  mkEqualityComparatorN 25,     -- L1D tag comparison
  mkMuxTree 4 25,    -- L1D tag set mux (4 sets × 25-bit tags)
  mkMuxTree 8 24,    -- L1I/L2 tag set mux (8 sets × 24-bit tags)

  -- Phase 7b: Cache Hierarchy Modules
  mkL1ICache,
  mkL1DCache,
  mkL2Cache,
  mkMemoryHierarchy,

  -- Phase 8a: Microcode Sequencer
  microcodeDecoderCircuit,
  microcodeSequencerCircuit,
  trapSequencerCircuit,

  -- Opcode PLA Decoders
  mkALUOpDecoder defaultCPUConfig,
  mkMulDivOpDecoder defaultCPUConfig,
  mkFPUOpDecoder defaultCPUConfig,
  mkAMOOpDecoder defaultCPUConfig,

  -- Phase 8: Top-Level Integration
  cdbMuxFDW2,
  mkFetchStage,
  mkRenameStage,
  mkRenameStage 64,
  mkIntRenameStage 32,
  mkIntRenameStage 64,
  mkFPRenameStage 32,
  mkFPRenameStage 64,
  mkCSRFile defaultCPUConfig,
  mkBusyTable_W2,
  mkFPBusyTable,
  CPU_W2.mkCPU_W2 defaultCPUConfig,
  Shoumei.RISCV.Memory.Cache.mkCachedCPU defaultCPUConfig
]

/-- Everything this generator emits, by module name. -/
def emittedModuleNames : List String :=
  allCircuits.map (·.name) ++ riscvDecoderModules

def main (args : List String) : IO Unit := do
  -- The circuit registry below is also the certificate registry: a
  -- compositional certificate is only meaningful for a circuit that is actually
  -- emitted.  `--export-certs` prints that registry, validating as it goes, and
  -- exits without generating anything.
  if args.contains "--export-certs" then
    Shoumei.Verification.ExportCerts.printCertificates allCircuits riscvDecoderModules
    return
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
  let loadedMap := Shoumei.Codegen.SystemVerilog.computeAllLoadedWires allCircuits

  -- Generate all circuits (pass allCircuits for sub-module port direction lookup)
  let mut count := 0
  let mut skipped := 0
  for c in allCircuits do
    let wasCached ← if !force then
      if let some h := Shoumei.Codegen.Unified.lookupHash hashMap c.name then
        isUpToDate c.name h
      else pure false
    else pure false
    writeCircuit c allCircuits force hashMap loadedMap
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
  Shoumei.RISCV.generateDecoders defs riscvDecoderModules

  -- Prune stale generated files (removed/renamed modules) so they don't
  -- linger in the build filelists.
  IO.println ""
  IO.println "Pruning stale generated outputs..."
  pruneStaleOutputs emittedModuleNames

  -- Generate testbenches
  IO.println ""
  IO.println "Generating testbenches..."
  writeTestbenches cpuTestbenchConfig

  -- Generate filelist.f for each output directory
  IO.println ""
  IO.println "Generating filelists..."
  writeFilelist svOutputDir ".sv"
  writeFilelist svNetlistOutputDir ".sv"
  writeFilelist cppSimOutputDir ".h"
  writeFilelist asap7OutputDir ".sv"
  IO.println "✓ Generated filelist.f in each output directory"

  -- Generate physical synthesis filelists (ASAP7-priority merge)
  IO.println ""
  IO.println "Generating physical synthesis filelists..."
  let physEntries ← System.FilePath.readDir physicalOutputDir
  let synthWrappers := physEntries.filter (fun e =>
    e.fileName.endsWith "_synth.sv")
  for wrapper in synthWrappers do
    let name := (wrapper.fileName.take (wrapper.fileName.length - 3)).toString  -- strip ".sv"
    writePhysicalFilelist name
    IO.println s!"  ✓ {name}.f"
  IO.println s!"✓ Generated {synthWrappers.size} physical filelists"

  -- Generate config.mk for testbench Makefile
  IO.println ""
  IO.println "Generating config.mk..."
  let cfg := defaultCPUConfig
  let configMk := s!"# Auto-generated by generate_all — do not edit\n" ++
    s!"CPU_NAME := {cfg.isaString}\n" ++
    s!"SPIKE_ISA := {cfg.spikeIsa}\n" ++
    s!"TB_MEM_SIZE := {cfg.memSizeWords}\n" ++
    s!"TIMEOUT_CYCLES := {cfg.timeoutCycles}\n" ++
    s!"NUM_PHYS_REGS := {cfg.numPhysRegs}\n" ++
    s!"ROB_ENTRIES := {cfg.robEntries}\n" ++
    s!"SB_ENTRIES := {cfg.storeBufferEntries}\n" ++
    s!"RS_ENTRIES := {cfg.rsEntries}\n"
  IO.FS.writeFile "output/config.mk" configMk
  IO.println "✓ Generated output/config.mk"

  -- Generate the canonical trace schema used by the C++ Kanata tracer and
  -- the TS pipeline viewer; stage drift becomes a compile error on both.
  IO.println ""
  IO.println "Generating trace schema..."
  IO.FS.writeFile "testbench/generated/trace_schema.gen.h" Shoumei.TraceSchema.renderCHeader
  IO.FS.writeFile "viewer/src/schema.gen.ts" Shoumei.TraceSchema.renderTsSchema
  IO.println "✓ Generated trace schema (C++ header + TS module)"

  IO.println ""
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  if skipped > 0 then
    IO.println s!"✓ Generated {count - skipped} circuits, skipped {skipped} unchanged"
  else
    IO.println s!"✓ Generated {count} circuits"
  IO.println "  SV:      output/sv-from-lean/"
  IO.println "  Netlist: output/sv-netlist/"
  IO.println "  C++ Sim: output/cpp_sim/"
  IO.println "  ASAP7:   output/sv-asap7/ (tech-mapped modules)"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
