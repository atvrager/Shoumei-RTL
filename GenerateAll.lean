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

-- Phase 8: Top-Level Integration
import Shoumei.RISCV.Fetch
import Shoumei.RISCV.CDBMux
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
open Shoumei.RISCV.Memory.Cache
open Shoumei.RISCV.CPU
open Shoumei.RISCV.Microcode
open Shoumei.RISCV.CPUTestbench

/-- Decoder modules generated from riscv-opcodes instruction definitions, outside
    the circuit registry above.  Named once because the stale-output pruner and
    the certificate registry must both agree with what is actually emitted. -/
def riscvDecoderModules : List String :=
  ["RV32IMFDecoder"]

-- Registry: Add circuits here for automatic generation
def allCircuits : List Circuit := [
  -- Phase 0: Foundation
  dff,
  mkQueue1FlowStructural 39,     -- CDB result FIFOs with flow-through bypass
  mkQueue1FlowStructural 72,     -- INT/Branch CDB FIFO (39 + 32 redirect_target + 1 mispredicted)

  -- Phase 1: Arithmetic
  mkKoggeStoneAdder32,
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
  mkMuxTree 4 32,
  mkMuxTree 8 2,  -- Phase 7: Store buffer size readout
  mkMux8x32Hierarchical, -- Hierarchical 8:1 (2× Mux4x32 + sel buffers)
  mkMuxTree 16 5, -- Phase 6: ROB head archRd readout
  mkMuxTree 16 6, -- Phase 6: ROB head physRd/oldPhysRd readout
  mkMuxTree 16 32, -- Phase 8: RVVI Queue16x32 read mux
  mkMux32x6,
  mkMux64x32Hierarchical,  -- Hierarchical version (9 instances instead of 8064 gates)
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
  mkRegisterN 16,
  mkRegisterN 32,
  mkRegisterN 64,
  -- Hierarchical registers (compositional verification)
  mkRegisterNHierarchical 66,  -- Phase 7: Store buffer entry payload (32+32+2)
  mkRegisterNHierarchical 95,  -- RS entry: 7-bit opcode + 7-bit tags (1+7+7+1+7+32+1+7+32)

  -- Phase 4: RISC-V Components
  mkRAT64,
  mkBitmapFreeList64_W2,
  mkPhysRegFile64,

  -- Phase 5: Execution Units
  mkIntegerExecUnit,
  mkBranchExecUnit,
  mkMemoryExecUnit,
  mkReservationStationFromConfig defaultCPUConfig,

  -- M-Extension (conditional on CPUConfig.enableM)
  mkKoggeStoneAdder64,
  csaCompressor64,
  mkPipelinedMultiplier,
  mkDividerCircuit,
  mkMulDivExecUnit,

  -- F-Extension: FPU building blocks
  fpMiscCircuit,
  fpAdderCircuit,
  fpMultiplierCircuit,
  fpFMACircuit,
  fpDividerCircuit,
  fpSqrtCircuit,
  mkFPExecUnit,

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

  -- Phase 8: Top-Level Integration
  cdbMuxFW2,
  mkFetchStage,
  mkRenameStage,
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
