/-
GenerateAll.lean - Centralized Code Generation for All Circuits

Single entry point for generating all circuits in the project.
Just add your circuit here and it gets all 3 output formats automatically.

Usage: lake exe generate_all
-/

import Shoumei.Codegen.Unified
import Shoumei.Codegen.SECMiter
import Shoumei.Codegen.ArchitectureDiagram
import Shoumei.Codegen.ArchitectureVisuals
import Shoumei.Codegen.BenchmarkVisual
import Shoumei.Codegen.LeanRoot
import Shoumei.Codegen.ProjectMap
import Shoumei.Codegen.SoCDiagram
import Shoumei.Components.Select
import Shoumei.Verification.ExportCerts
import Shoumei.Verification.StructuralLint
import Shoumei.DSL.PortResolve
import Shoumei.Verification.DualRTL

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
import Shoumei.RISCV.Microcode.FallbackSequencerCodegen

-- Phase 8: Top-Level Integration
import Shoumei.RISCV.Fetch
import Shoumei.RISCV.CDBMux
import Shoumei.RISCV.CSRFile
import Shoumei.RISCV.CPU.BusyBitTable
import Shoumei.RISCV.CPU

-- Phase 9: Shoumei SoC & Peripherals
import Shoumei.Circuits.Sequential.ResetSync
import Shoumei.Interconnect.TileLink.TLXbar
import Shoumei.Peripherals.BootROM
import Shoumei.Peripherals.ACLINT
import Shoumei.Peripherals.APLIC
import Shoumei.Peripherals.UART
import Shoumei.Peripherals.GPIO
import Shoumei.Peripherals.SRAM
import Shoumei.SoC.ShoumeiSoC

-- Testbench generation
import Shoumei.RISCV.CPUTestbench
import Shoumei.RISCV.TraceSchema

open Shoumei.Codegen.Unified
open Shoumei.Components
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
open Shoumei.Interconnect.TileLink
open Shoumei.Peripherals
open Shoumei.SoC

/-- Decoder modules generated from riscv-opcodes instruction definitions, outside
    the circuit registry above.  Named once because the stale-output pruner and
    the certificate registry must both agree with what is actually emitted. -/
def riscvDecoderModules : List String :=
  ["RV64GDecoder"]

def foundationBaseCircuits : List Circuit := [
  -- Phase 0: Foundation & Pilot Atoms
  dff,
  fullAdderCircuit,
  mkRippleCarryAdder4,
  mkLogicUnit4,
  mkMux4x1,
  mkComparator4,
  q1w1,
  mkQueue1StructuralComplete 8,
  mkQueue1FlowStructural 39,     -- CDB result FIFOs with flow-through bypass
  mkQueue1FlowStructural 70,     -- 64-bit result FIFOs (tag6 + data64)
  mkQueue1FlowStructural 71,     -- FP result FIFO (tag6 + data64 + is_fp)
  mkQueue1FlowStructural 72,     -- INT/Branch CDB FIFO (39 + 32 redirect_target + 1 mispredicted)
  mkQueue1FlowStructural 103,    -- 64-bit Branch CDB FIFO (tag6 + data64 + 32 redir + 1 mispred)
  mkQueue1FlowStructural 104,    -- 64-bit CDB FIFO (IB0 / IB_BR)
  mkQueue1FlowStructural 43,     -- FP writeback merge queue, SP (tag6 + data32 + exc5)
  mkQueue1FlowStructural 44,     -- FP writeback merge queue, SP (tag6 + data32 + exc5 + int-domain)
  mkQueue1FlowStructural 75,     -- FP writeback merge queue, DP (tag6 + data64 + exc5)
  mkQueue1FlowStructural 76      -- FP writeback merge queue, DP (tag6 + data64 + exc5 + int-domain)
]

def combinationalCircuits : List Circuit := [
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
  mkDecoder 7,   -- FPExcFile_128x5 write decoder
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
  mkMuxTree 64 5,          -- FPExcFile_64x5 readout
  mkPriorityArbiter2,
  mkPriorityArbiter8,
  mkPriorityArbiter64,  -- Bitmap free list allocation
  mkOneHotEncoder64,    -- Bitmap free list one-hot to binary
  mkPopcount8  -- Phase 7: Store buffer flush recovery
]

def sequentialCircuits : List Circuit := [
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
  mkRegisterN 5,   -- FP exception side file (FPExcFile_64x5 entries)
  mkRegisterN 24,  -- ROB16_W2 PC array
  mkRegisterN 32,
  mkRegisterN 64,
  -- Clock-enabled registers
  mkRegisterEnN 1,
  mkRegisterEnN 2,
  mkRegisterEnN 4,
  mkRegisterEnN 8,
  mkRegisterEnN 16,
  mkRegisterEnN 32,
  mkRegisterEnN 64,
  -- Hierarchical registers (compositional verification)
  mkRegisterNHierarchical 96,  -- RS entry: 8-bit opcode + 7-bit tags (1+8+7+1+7+32+1+7+32)
  mkRegisterNHierarchical 98,  -- Store buffer entry payload (32+64+2)
  mkRegisterNHierarchical 130, -- Store buffer 64-bit entry payload (64+64+2)
  mkRegisterNHierarchical 157, -- Specialized RS 64-bit entry
  mkRegisterNHierarchical 158,
  mkRegisterNHierarchical 159,
  mkRegisterNHierarchical 160, -- RS 64-bit entry (1+8+7+1+7+64+1+7+64)
  mkRegister160Flat
]

def renamingCircuits : List Circuit := [
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
  mkFPExcFile 64 5  -- FP exception flags keyed by destination phys reg
]

def executionCircuits : List Circuit := [
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
  fpAdderD_Stage4aCircuit,
  fpAdderD_Stage4bCircuit,
  fpAdderDCircuit,
  fpMultiplierDCircuit,
  fpFMADCircuit,
  fpDividerDCircuit,
  fpSqrtDCircuit,
  fpExecUnitD
]

def retirementCircuits : List Circuit := [
  -- Phase 6: Retirement
  mkROB16,
  mkQueue16x32_DualPort  -- W=2 dual-port RVVI PC/instruction queues
]

def memoryCircuits : List Circuit :=
  [-- Phase 7: Memory
   mkStoreBuffer8,
   mkLSU] ++
  cacheGeomCircuits defaultCPUConfig.cacheGeom ++
  [-- Phase 7b: Cache Hierarchy Modules
   mkL1ICache,
   mkL1DCache,
   mkL2Cache,
   mkMemoryHierarchy]

def controlCircuits : List Circuit := [
  -- Phase 8a: Microcode Sequencer
  microcodeDecoderCircuit,
  microcodeSequencerCircuit,
  trapSequencerCircuit,
  fallbackSequencerCircuitExport,

  -- Opcode PLA Decoders
  mkALUOpDecoder defaultCPUConfig,
  mkMulDivOpDecoder defaultCPUConfig,
  mkFPUOpDecoder defaultCPUConfig,
  mkAMOOpDecoder defaultCPUConfig
]

def cpuCircuits : List Circuit := [
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

def socCircuits : List Circuit := [
  -- Phase 9: Shoumei SoC & Peripherals
  resetSyncCircuit,
  tlXbar8Circuit,
  bootROMCircuit,
  aclintCircuit,
  aplicCircuit,
  uartCircuit,
  gpioCircuit,
  sramCircuit,
  shoumeiSoCCircuit
]

-- Registry: Add circuits here for automatic generation
def baseCircuits : List Circuit :=
  foundationBaseCircuits ++
  combinationalCircuits ++
  sequentialCircuits ++
  renamingCircuits ++
  executionCircuits ++
  retirementCircuits ++
  memoryCircuits ++
  controlCircuits ++
  cpuCircuits ++
  socCircuits

/-- Every selectable adder the sites may resolve to, followed by the rest of
    the registry minus any adder already listed.  The adders are leaves, so
    putting them first keeps `allCircuits` in topological order and lets the
    dependency-aware hash see them before the modules that instantiate them.

    Deduplicated by module name (first occurrence wins): a name can
    legitimately be built by more than one builder - the hierarchical 8:1 mux
    (`mkMux8x32Hierarchical`) and the parametric `mkMuxTree 8 32` share the
    module name `Mux8x32`, and the cache geometry derives a dword extract mux
    that may collide again.  Emitting both would alias the incremental
    codegen's per-name hash cache and the precomputed loaded-wire map, so the
    module body would depend on list order - the hierarchical mux then lost its
    instance output connections.  Keeping the first occurrence preserves the
    hand-written variants (byte-identical default output) and the interface is
    the same, so every instantiator still binds correctly. -/
def allCircuits : List Circuit :=
  (allAdderCircuits ++ baseCircuits.filter
    (fun c => !(allAdderCircuits.map (·.name)).contains c.name)).foldl
    (fun acc c => if acc.any (fun c' => c'.name == c.name) then acc else acc ++ [c]) []

/-- Everything this generator emits, by module name. -/
def emittedModuleNames : List String :=
  allCircuits.map (·.name) ++ riscvDecoderModules

def subsystemCircuitNames (subsystem : String) : Option (List String) :=
  let adderNames := allAdderCircuits.map (·.name)
  match subsystem with
  | "foundation" | "base" => some (adderNames ++ foundationBaseCircuits.map (·.name))
  | "combinational"       =>
    some (combinationalCircuits.filter (fun c => !adderNames.contains c.name) |>.map (·.name))
  | "sequential"          => some (sequentialCircuits.map (·.name))
  | "renaming"            => some (renamingCircuits.map (·.name))
  | "execution"           =>
    some (executionCircuits.filter (fun c => !adderNames.contains c.name) |>.map (·.name))
  | "retirement"          => some (retirementCircuits.map (·.name))
  | "memory"              => some (memoryCircuits.map (·.name))
  | "control"             => some (controlCircuits.map (·.name))
  | "cpu"                 => some (cpuCircuits.map (·.name))
  | "soc"                 => some (socCircuits.map (·.name))
  | "decoders"            => some []
  | "testbench"           => some []
  | "sec"                 => some []
  | "all"                 => some (allCircuits.map (·.name))
  | _                     => none

def circuitsForSubsystem (subsystem : String) : Option (List Circuit) :=
  match subsystemCircuitNames subsystem with
  | some names => some (allCircuits.filter (fun c => names.contains c.name))
  | none => none

def parseArg (pfx : String) (args : List String) : Option String :=
  args.findSome? (fun a =>
    if a.startsWith pfx then some (a.drop pfx.length).toString else none)

def main (args : List String) : IO Unit := do
  -- The circuit registry below is also the certificate registry: a
  -- compositional certificate is only meaningful for a circuit that is actually
  -- emitted.  `--export-certs` prints that registry, validating as it goes, and
  -- exits without generating anything.
  if args.contains "--export-certs" then
    Shoumei.Verification.ExportCerts.printCertificates allCircuits riscvDecoderModules
    return
  if args.contains "--export-refinements" then
    IO.eprintln "Refinements export is disabled in generate_all to keep code generation fast."
    IO.Process.exit 1
  if args.contains "--export-sec-manifest" || args.contains "--sec-manifest" then
    Shoumei.Verification.DualRTL.printManifest allCircuits
    return
  if args.contains "--check-sec-specs" then
    let rc ← Shoumei.Verification.DualRTL.checkSpecs allCircuits
    if rc != 0 then IO.Process.exit rc.toUInt8
    return
  if args.contains "--check-drivers" then
    let clashes := Shoumei.DSL.PortResolve.checkRegistryDrivers allCircuits
    if clashes.isEmpty then
      IO.println s!"✓ No wire in {allCircuits.length} circuits has more than one driver"
      return
    else
      IO.eprintln s!"✗ Driver check failed: {clashes.length} multiply-driven wires:"
      for c in clashes do
        IO.eprintln s!"  {c.moduleName}: {c.wireName} ({c.drivers} drivers)"
      IO.Process.exit 1
  if args.contains "--check-wiring" then
    let missing := Shoumei.DSL.PortResolve.checkRegistryWiring allCircuits
    if missing.isEmpty then
      IO.println s!"✓ All {allCircuits.length} circuits are WellWired (0 unconnected instance inputs)"
      return
    else
      IO.eprintln s!"✗ Wiring check failed: {missing.length} unconnected instance inputs found:"
      for m in missing do
        IO.eprintln s!"  {m.parentModule} / {m.childModule} {m.instName}: {m.portWire.name}"
      IO.Process.exit 1
  if args.contains "--treemap" then
    Shoumei.Codegen.ArchitectureDiagram.generate allCircuits (CPU_W2.mkCPU_W2 defaultCPUConfig)
    return
  if args.contains "--soc-diagram" then
    Shoumei.Codegen.SoCDiagram.generate defaultCPUConfig
    return
  if args.contains "--benchmarks" || args.contains "--benchmark-visual" then
    Shoumei.Codegen.BenchmarkVisual.generateBenchmarks
    return
  if args.contains "--gen-lean-root" then
    let rc ← Shoumei.Codegen.LeanRoot.run (checkOnly := false)
    if rc != 0 then IO.Process.exit rc.toUInt8
    return
  if args.contains "--check-lean-root" then
    let rc ← Shoumei.Codegen.LeanRoot.run (checkOnly := true)
    if rc != 0 then IO.Process.exit rc.toUInt8
    return
  if args.contains "--lint-structural" then
    let svDir := args.findSome? (fun a =>
      if a.startsWith "--sv-dir=" then some (System.FilePath.mk (a.drop 9).toString) else none)
      |>.getD (System.FilePath.mk "output/sv-from-lean")
    let rc ← Shoumei.Verification.StructuralLint.run svDir
    if rc != 0 then IO.Process.exit rc.toUInt8
    return
  if args.contains "--project-map" then
    let outPath := args.findSome? (fun a =>
      if a.startsWith "--out=" then some (System.FilePath.mk (a.drop 6).toString) else none)
      |>.getD (System.FilePath.mk "docs/project-map.md")
    let rc ← Shoumei.Codegen.ProjectMap.generate outPath
    if rc != 0 then IO.Process.exit rc.toUInt8
    return
  if args.contains "--visuals" || args.contains "--architecture-visuals" then
    Shoumei.Codegen.SoCDiagram.generate defaultCPUConfig
    Shoumei.Codegen.BenchmarkVisual.generateBenchmarks
    Shoumei.Codegen.ArchitectureVisuals.generateAllVisuals allCircuits
      (CPU_W2.mkCPU_W2 defaultCPUConfig)
    return

  let outSv := parseArg "--out-sv=" args |>.map System.FilePath.mk
    |>.getD (System.FilePath.mk "output/sv-from-lean")
  let outNetlist := parseArg "--out-netlist=" args |>.map System.FilePath.mk
    |>.getD (System.FilePath.mk "output/sv-netlist")
  let outCppSim := parseArg "--out-cpp-sim=" args |>.map System.FilePath.mk
    |>.getD (System.FilePath.mk "output/cpp_sim")
  let outAsap7 := parseArg "--out-asap7=" args |>.map System.FilePath.mk
    |>.getD (System.FilePath.mk "output/sv-asap7")
  let outGf180 := parseArg "--out-gf180=" args |>.map System.FilePath.mk
    |>.getD (System.FilePath.mk "output/sv-gf180")
  let outSec := parseArg "--out-sec=" args |>.map System.FilePath.mk
    |>.getD (System.FilePath.mk "output/sv-sec")
  let outTestbench := parseArg "--out-testbench=" args |>.map System.FilePath.mk
    |>.getD (System.FilePath.mk "testbench/generated")
  let outConfigMk := parseArg "--out-config-mk=" args |>.map System.FilePath.mk
    |>.getD (System.FilePath.mk "output/config.mk")
  let outPhysical := parseArg "--out-physical=" args |>.map System.FilePath.mk
    |>.getD (System.FilePath.mk "physical")
  let instrDict := parseArg "--instr-dict=" args |>.map System.FilePath.mk
    |>.getD Shoumei.RISCV.instrDictPath
  let subsystemOpt := parseArg "--subsystem=" args
  let circuitOpt := parseArg "--circuit=" args
  let skipVisuals := args.contains "--skip-visuals"
  let skipTestbench := args.contains "--skip-testbench"
  let skipSec := args.contains "--skip-sec"
  let skipDecoders := args.contains "--skip-decoders"

  let cfg : OutputConfig := {
    svDir := outSv,
    netlistDir := outNetlist,
    cppSimDir := outCppSim,
    asap7Dir := outAsap7,
    gf180Dir := outGf180,
    secDir := outSec,
    testbenchDir := outTestbench,
    configMkPath := outConfigMk,
    physicalDir := outPhysical,
    instrDictPath := instrDict
  }

  let selectedCircuits : List Circuit ← match circuitOpt with
    | some name =>
      match allCircuits.find? (fun (c : Circuit) => c.name == name) with
      | some c => pure [c]
      | none =>
        IO.eprintln s!"Unknown circuit: {name}"
        IO.Process.exit 1
    | none =>
      match subsystemOpt with
      | some sub =>
        match circuitsForSubsystem sub with
        | some cs => pure cs
        | none =>
          IO.eprintln s!"Unknown subsystem: {sub}"
          IO.Process.exit 1
      | none => pure allCircuits

  let isAllSubsystem := subsystemOpt.isNone || subsystemOpt == some "all"

  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  let subTag := match subsystemOpt with
    | some s => s!" ({s})"
    | none => ""
  IO.println s!"  証明 Shoumei RTL - Code Generation{subTag}"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println ""

  -- A wire with two drivers is a modelling error that proofs do not catch: the
  -- emitted SystemVerilog just gets two continuous assignments for the net. Fail
  -- before writing anything rather than ship a netlist whose value depends on
  -- evaluation order.
  let driverClashes := Shoumei.DSL.PortResolve.checkRegistryDrivers allCircuits
  if !driverClashes.isEmpty then
    IO.eprintln s!"✗ {driverClashes.length} wire(s) are driven more than once; refusing to generate:"
    for c in driverClashes do
      IO.eprintln s!"  {c.moduleName}: {c.wireName} ({c.drivers} drivers)"
    IO.eprintln "  Each wire is a single net, so a second driver silently overrides the first."
    IO.Process.exit 1

  -- Initialize output directories
  initOutputDirs cfg

  -- Pre-compute loaded-wire map
  let loadedMap := Shoumei.Codegen.SystemVerilog.computeAllLoadedWires allCircuits

  -- Generate circuits
  let mut count := 0
  for c in selectedCircuits do
    writeCircuit c allCircuits loadedMap cfg
    count := count + 1

  -- Generate RISC-V decoders
  if (isAllSubsystem || subsystemOpt == some "decoders") && circuitOpt.isNone && !skipDecoders then
    IO.println ""
    IO.println "Generating RISC-V decoders..."
    let opcodesPath := cfg.instrDictPath
    unless (← opcodesPath.pathExists) do
      IO.eprintln s!"instr_dict.json is missing at {opcodesPath}"
      IO.eprintln "Build it with: bazel build //generators:instr_dict"
      IO.Process.exit 1
    let defs ← Shoumei.RISCV.loadInstrDictFromFile opcodesPath
    Shoumei.RISCV.generateDecoders defs riscvDecoderModules cfg.svDir cfg.cppSimDir

  -- Generate testbenches
  if (isAllSubsystem || subsystemOpt == some "testbench") && circuitOpt.isNone && !skipTestbench then
    IO.println ""
    IO.println "Generating testbenches..."
    writeTestbenches cpuTestbenchConfig cfg.testbenchDir
    IO.println ""
    IO.println "Generating config.mk..."
    let cpuCfg := defaultCPUConfig
    let configMk := s!"# Auto-generated by generate_all — do not edit\n" ++
      s!"CPU_NAME := {cpuCfg.isaString}\n" ++
      s!"SPIKE_ISA := {cpuCfg.spikeIsa}\n" ++
      s!"TB_MEM_SIZE := {cpuCfg.memSizeWords}\n" ++
      s!"TIMEOUT_CYCLES := {cpuCfg.timeoutCycles}\n" ++
      s!"NUM_PHYS_REGS := {cpuCfg.numPhysRegs}\n" ++
      s!"ROB_ENTRIES := {cpuCfg.robEntries}\n" ++
      s!"SB_ENTRIES := {cpuCfg.storeBufferEntries}\n" ++
      s!"RS_ENTRIES := {cpuCfg.rsEntries}\n"
    if let some parent := cfg.configMkPath.parent then
      IO.FS.createDirAll parent
    IO.FS.writeFile cfg.configMkPath.toString configMk
    IO.println s!"✓ Generated {cfg.configMkPath}"

    IO.println ""
    IO.println "Generating trace schema..."
    IO.FS.createDirAll cfg.testbenchDir
    IO.FS.writeFile (cfg.testbenchDir / "trace_schema.gen.h").toString
      Shoumei.TraceSchema.renderCHeader
    if ← System.FilePath.isDir "viewer/src" then
      IO.FS.writeFile "viewer/src/schema.gen.ts" Shoumei.TraceSchema.renderTsSchema
    IO.println "✓ Generated trace schema"

  -- Generate SEC miters and scripts
  if (isAllSubsystem || subsystemOpt == some "sec") && circuitOpt.isNone && !skipSec then
    IO.println ""
    IO.println "Generating SEC miters and verification scripts..."
    let secOutputDir := cfg.secDir
    IO.FS.createDirAll secOutputDir
    let miter160 := Shoumei.Codegen.SECMiter.generateSECMiter mkRegister160Flat
      mkRegister160Hierarchical "Register160_sec_miter"
    IO.FS.writeFile (secOutputDir / "Register160_sec_miter.sv").toString miter160
    let svDirStr := cfg.svDir.toString
    let secDirStr := cfg.secDir.toString
    let formality160 := Shoumei.Codegen.SECMiter.generateFormalityTcl "Register160Flat" "Register160"
      [s!"{svDirStr}/Register160Flat.sv"]
      [s!"{svDirStr}/Register64.sv", s!"{svDirStr}/Register32.sv", s!"{svDirStr}/Register160.sv"]
    IO.FS.writeFile (secOutputDir / "Register160_formality.tcl").toString formality160
    let yosys160 := Shoumei.Codegen.SECMiter.generateYosysTcl "Register160Flat" "Register160"
      [s!"{svDirStr}/Register160Flat.sv", s!"{svDirStr}/Register64.sv", s!"{svDirStr}/Register32.sv",
       s!"{svDirStr}/Register160.sv"]
    IO.FS.writeFile (secOutputDir / "Register160_yosys.tcl").toString yosys160
    let vcFormal160 := Shoumei.Codegen.SECMiter.generateVCFormalTcl "Register160_sec_miter"
      [s!"{svDirStr}/Register160Flat.sv", s!"{svDirStr}/Register64.sv", s!"{svDirStr}/Register32.sv",
       s!"{svDirStr}/Register160.sv", s!"{secDirStr}/Register160_sec_miter.sv"]
    IO.FS.writeFile (secOutputDir / "Register160_vc_formal.tcl").toString vcFormal160
    let svaFormal160 := Shoumei.Codegen.SECMiter.generateVCFormalTcl "Register160"
      [s!"{svDirStr}/Register64.sv", s!"{svDirStr}/Register32.sv", s!"{svDirStr}/Register160.sv"]
    IO.FS.writeFile (secOutputDir / "Register160_sva_formal.tcl").toString svaFormal160
    let svaFormalEn64 := Shoumei.Codegen.SECMiter.generateVCFormalTcl "RegisterEn64"
      [s!"{svDirStr}/RegisterEn64.sv"]
    IO.FS.writeFile (secOutputDir / "RegisterEn64_sva_formal.tcl").toString svaFormalEn64
    let svaFormalLogicUnit32 := Shoumei.Codegen.SECMiter.generateVCFormalTcl "LogicUnit32"
      [s!"{svDirStr}/LogicUnit32.sv"] "clock" "reset" (hasClock := false)
    IO.FS.writeFile (secOutputDir / "LogicUnit32_sva_formal.tcl").toString svaFormalLogicUnit32
    let svaFormalLogicUnit64 := Shoumei.Codegen.SECMiter.generateVCFormalTcl "LogicUnit64"
      [s!"{svDirStr}/LogicUnit64.sv"] "clock" "reset" (hasClock := false)
    IO.FS.writeFile (secOutputDir / "LogicUnit64_sva_formal.tcl").toString svaFormalLogicUnit64
    let svaFormalMux4x32 := Shoumei.Codegen.SECMiter.generateVCFormalTcl "Mux4x32"
      [s!"{svDirStr}/Mux4x32.sv"] "clock" "reset" (hasClock := false)
    IO.FS.writeFile (secOutputDir / "Mux4x32_sva_formal.tcl").toString svaFormalMux4x32
    let svaFormalMux8x32 := Shoumei.Codegen.SECMiter.generateVCFormalTcl "Mux8x32"
      [s!"{svDirStr}/Mux4x32.sv", s!"{svDirStr}/Mux8x32.sv"] "clock" "reset" (hasClock := false)
    IO.FS.writeFile (secOutputDir / "Mux8x32_sva_formal.tcl").toString svaFormalMux8x32
    let svaFormalPopcount8 := Shoumei.Codegen.SECMiter.generateVCFormalTcl "Popcount8"
      [s!"{svDirStr}/Popcount8.sv"] "clock" "reset" (hasClock := false)
    IO.FS.writeFile (secOutputDir / "Popcount8_sva_formal.tcl").toString svaFormalPopcount8
    IO.println s!"✓ Generated SEC miters and scripts in {secOutputDir}"

  -- Prune stale generated files
  if isAllSubsystem && circuitOpt.isNone then
    IO.println ""
    IO.println "Pruning stale generated outputs..."
    pruneStaleOutputs emittedModuleNames cfg

    -- Generate filelist.f for each output directory
    IO.println ""
    IO.println "Generating filelists..."
    writeFilelist cfg.svDir ".sv"
    writeFilelist cfg.netlistDir ".sv"
    writeFilelist cfg.cppSimDir ".h"
    for pdk in allPdks do
      let pDir := match pdk with
        | .asap7 => cfg.asap7Dir
        | .gf180mcu => cfg.gf180Dir
      writeFilelist pDir ".sv"
    IO.println "✓ Generated filelist.f in each output directory"

    -- Generate physical synthesis filelists
    let physEntries ← try cfg.physicalDir.readDir catch _ => pure #[]
    let synthWrappers := physEntries.filter (fun e => e.fileName.endsWith "_synth.sv")
    if !synthWrappers.isEmpty then
      IO.println ""
      IO.println "Generating physical synthesis filelists..."
      for wrapper in synthWrappers do
        let name := (wrapper.fileName.take (wrapper.fileName.length - 3)).toString
        writePhysicalFilelist name cfg.asap7Dir cfg.svDir cfg.physicalDir
        IO.println s!"  ✓ {name}.f"
      IO.println s!"✓ Generated {synthWrappers.size} physical filelists"

    -- Architecture visuals
    if !skipVisuals then
      IO.println ""
      IO.println "Generating architecture treemap and visual suite..."
      Shoumei.Codegen.ArchitectureDiagram.generate allCircuits (CPU_W2.mkCPU_W2 defaultCPUConfig)
      Shoumei.Codegen.SoCDiagram.generate defaultCPUConfig
      Shoumei.Codegen.BenchmarkVisual.generateBenchmarks
      Shoumei.Codegen.ArchitectureVisuals.generateAllVisuals allCircuits
        (CPU_W2.mkCPU_W2 defaultCPUConfig)

  IO.println ""
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println s!"✓ Generated {count} circuits"
  IO.println s!"  SV:      {cfg.svDir}"
  IO.println s!"  Netlist: {cfg.netlistDir}"
  IO.println s!"  C++ Sim: {cfg.cppSimDir}"
  IO.println s!"  ASAP7:   {cfg.asap7Dir}"
  IO.println s!"  GF180:   {cfg.gf180Dir}"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
