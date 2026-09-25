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
import Shoumei.Circuits.Sequential.Queue1Bridge
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

-- Registry: Add circuits here for automatic generation
def baseCircuits : List Circuit := [
  -- Phase 0: Foundation & Pilot Atoms
  dff,
  fullAdderCircuit,
  mkRippleCarryAdder4,
  mkLogicUnit4,
  mkMux4x1,
  mkComparator4,
  q1w1,
  mkQueue1FlowStructural 39,     -- CDB result FIFOs with flow-through bypass
  mkQueue1FlowStructural 70,     -- 64-bit result FIFOs (tag6 + data64)
  mkQueue1FlowStructural 71,     -- FP result FIFO (tag6 + data64 + is_fp)
  mkQueue1FlowStructural 72,     -- INT/Branch CDB FIFO (39 + 32 redirect_target + 1 mispredicted)
  mkQueue1FlowStructural 103,    -- 64-bit Branch CDB FIFO (tag6 + data64 + 32 redir + 1 mispred)
  mkQueue1FlowStructural 104,    -- 64-bit CDB FIFO (IB0 / IB_BR)
  mkQueue1FlowStructural 43,     -- FP writeback merge queue, SP (tag6 + data32 + exc5)
  mkQueue1FlowStructural 44,     -- FP writeback merge queue, SP (tag6 + data32 + exc5 + int-domain)
  mkQueue1FlowStructural 75,     -- FP writeback merge queue, DP (tag6 + data64 + exc5)
  mkQueue1FlowStructural 76,     -- FP writeback merge queue, DP (tag6 + data64 + exc5 + int-domain)

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
  mkRegister160Flat,

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
  mkLSU
  ] ++
  -- Phase 7b: Cache Hierarchy Building Blocks, derived from the configured
  -- geometry (tag widths, set counts, word extract muxes, replacement blocks)
  -- so a different cache size does not silently reference missing modules.
  cacheGeomCircuits defaultCPUConfig.cacheGeom ++
  [
  -- Phase 7b: Cache Hierarchy Modules
  mkL1ICache,
  mkL1DCache,
  mkL2Cache,
  mkMemoryHierarchy,

  -- Phase 8a: Microcode Sequencer
  microcodeDecoderCircuit,
  microcodeSequencerCircuit,
  trapSequencerCircuit,
  fallbackSequencerCircuitExport,

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
  Shoumei.RISCV.Memory.Cache.mkCachedCPU defaultCPUConfig,


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

def main (args : List String) : IO Unit := do
  -- The circuit registry below is also the certificate registry: a
  -- compositional certificate is only meaningful for a circuit that is actually
  -- emitted.  `--export-certs` prints that registry, validating as it goes, and
  -- exits without generating anything.
  if args.contains "--export-certs" then
    Shoumei.Verification.ExportCerts.printCertificates allCircuits riscvDecoderModules
    return
  if args.contains "--export-refinements" then
    Shoumei.Verification.ExportCerts.printRefinements allCircuits riscvDecoderModules
    return
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
    let svDir := args.findSome? (fun a => if a.startsWith "--sv-dir=" then some (System.FilePath.mk (a.drop 9).toString) else none) |>.getD (System.FilePath.mk "output/sv-from-lean")
    let rc ← Shoumei.Verification.StructuralLint.run svDir
    if rc != 0 then IO.Process.exit rc.toUInt8
    return
  if args.contains "--project-map" then
    let outPath := args.findSome? (fun a => if a.startsWith "--out=" then some (System.FilePath.mk (a.drop 6).toString) else none) |>.getD (System.FilePath.mk "docs/project-map.md")
    let rc ← Shoumei.Codegen.ProjectMap.generate outPath
    if rc != 0 then IO.Process.exit rc.toUInt8
    return
  if args.contains "--visuals" || args.contains "--architecture-visuals" then
    Shoumei.Codegen.SoCDiagram.generate defaultCPUConfig
    Shoumei.Codegen.BenchmarkVisual.generateBenchmarks
    Shoumei.Codegen.ArchitectureVisuals.generateAllVisuals allCircuits (CPU_W2.mkCPU_W2 defaultCPUConfig)
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

  -- Generate SEC (Sequential Equivalence Checking) miters and scripts
  IO.println ""
  IO.println "Generating SEC miters and verification scripts..."
  let secOutputDir : System.FilePath := "output/sv-sec"
  IO.FS.createDirAll secOutputDir
  let miter160 := Shoumei.Codegen.SECMiter.generateSECMiter mkRegister160Flat mkRegister160Hierarchical "Register160_sec_miter"
  IO.FS.writeFile (secOutputDir / "Register160_sec_miter.sv") miter160
  let formality160 := Shoumei.Codegen.SECMiter.generateFormalityTcl "Register160Flat" "Register160" ["output/sv-from-lean/Register160Flat.sv"] ["output/sv-from-lean/Register64.sv", "output/sv-from-lean/Register32.sv", "output/sv-from-lean/Register160.sv"]
  IO.FS.writeFile (secOutputDir / "Register160_formality.tcl") formality160
  let yosys160 := Shoumei.Codegen.SECMiter.generateYosysTcl "Register160Flat" "Register160" ["output/sv-from-lean/Register160Flat.sv", "output/sv-from-lean/Register64.sv", "output/sv-from-lean/Register32.sv", "output/sv-from-lean/Register160.sv"]
  IO.FS.writeFile (secOutputDir / "Register160_yosys.tcl") yosys160
  let vcFormal160 := Shoumei.Codegen.SECMiter.generateVCFormalTcl "Register160_sec_miter" ["output/sv-from-lean/Register160Flat.sv", "output/sv-from-lean/Register64.sv", "output/sv-from-lean/Register32.sv", "output/sv-from-lean/Register160.sv", "output/sv-sec/Register160_sec_miter.sv"]
  IO.FS.writeFile (secOutputDir / "Register160_vc_formal.tcl") vcFormal160
  let svaFormal160 := Shoumei.Codegen.SECMiter.generateVCFormalTcl "Register160" ["output/sv-from-lean/Register64.sv", "output/sv-from-lean/Register32.sv", "output/sv-from-lean/Register160.sv"]
  IO.FS.writeFile (secOutputDir / "Register160_sva_formal.tcl") svaFormal160
  let svaFormalEn64 := Shoumei.Codegen.SECMiter.generateVCFormalTcl "RegisterEn64" ["output/sv-from-lean/RegisterEn64.sv"]
  IO.FS.writeFile (secOutputDir / "RegisterEn64_sva_formal.tcl") svaFormalEn64
  let svaFormalLogicUnit32 := Shoumei.Codegen.SECMiter.generateVCFormalTcl "LogicUnit32" ["output/sv-from-lean/LogicUnit32.sv"] "clock" "reset" (hasClock := false)
  IO.FS.writeFile (secOutputDir / "LogicUnit32_sva_formal.tcl") svaFormalLogicUnit32
  let svaFormalLogicUnit64 := Shoumei.Codegen.SECMiter.generateVCFormalTcl "LogicUnit64" ["output/sv-from-lean/LogicUnit64.sv"] "clock" "reset" (hasClock := false)
  IO.FS.writeFile (secOutputDir / "LogicUnit64_sva_formal.tcl") svaFormalLogicUnit64
  let svaFormalMux4x32 := Shoumei.Codegen.SECMiter.generateVCFormalTcl "Mux4x32" ["output/sv-from-lean/Mux4x32.sv"] "clock" "reset" (hasClock := false)
  IO.FS.writeFile (secOutputDir / "Mux4x32_sva_formal.tcl") svaFormalMux4x32
  let svaFormalMux8x32 := Shoumei.Codegen.SECMiter.generateVCFormalTcl "Mux8x32" ["output/sv-from-lean/Mux4x32.sv", "output/sv-from-lean/Mux8x32.sv"] "clock" "reset" (hasClock := false)
  IO.FS.writeFile (secOutputDir / "Mux8x32_sva_formal.tcl") svaFormalMux8x32
  let svaFormalPopcount8 := Shoumei.Codegen.SECMiter.generateVCFormalTcl "Popcount8" ["output/sv-from-lean/Popcount8.sv"] "clock" "reset" (hasClock := false)
  IO.FS.writeFile (secOutputDir / "Popcount8_sva_formal.tcl") svaFormalPopcount8
  IO.println "✓ Generated SEC miters and scripts in output/sv-sec/"

  -- Generate filelist.f for each output directory
  IO.println ""
  IO.println "Generating filelists..."
  writeFilelist svOutputDir ".sv"
  writeFilelist svNetlistOutputDir ".sv"
  writeFilelist cppSimOutputDir ".h"
  for pdk in allPdks do
    writeFilelist (pdkOutputDir pdk) ".sv"
  IO.println "✓ Generated filelist.f in each output directory"

  -- Generate physical synthesis filelists (target-PDK-priority merge)
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

  -- Architecture treemap & visuals, sized from the same registry the SV came from
  IO.println ""
  IO.println "Generating architecture treemap and visual suite..."
  Shoumei.Codegen.ArchitectureDiagram.generate allCircuits (CPU_W2.mkCPU_W2 defaultCPUConfig)
  Shoumei.Codegen.SoCDiagram.generate defaultCPUConfig
  Shoumei.Codegen.BenchmarkVisual.generateBenchmarks
  Shoumei.Codegen.ArchitectureVisuals.generateAllVisuals allCircuits (CPU_W2.mkCPU_W2 defaultCPUConfig)

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
  IO.println "  GF180:   output/sv-gf180/ (tech-mapped modules)"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
