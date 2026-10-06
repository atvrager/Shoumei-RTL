/-
CircuitRegistry.lean - Centralized Circuit Registry for Shoumei RTL

Maintains the complete list of circuits emitted by the RTL generators
and inspected by architecture visualization tools.
-/

import Shoumei.DSL
import Shoumei.LeafRegistry

-- Phase 4: RISC-V Components
import Shoumei.RISCV.CodegenTest
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

namespace Shoumei.CircuitRegistry

open Shoumei
open Shoumei.LeafRegistry
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
open Shoumei.Interconnect.TileLink
open Shoumei.Peripherals
open Shoumei.SoC

def riscvDecoderModules : List String :=
  ["RV64GDecoder"]

def renamingCircuits : List Circuit := [
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
  mkFPExcFile 64 5
]

def executionCircuits : List Circuit := [
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
  fpDoubleMiscCircuit,
  fpDoubleConverterCircuit,
  int64ToFPCircuit,
  fpUnpackDPCircuit,
  fpToIntAlignCircuit,
  fpToIntRoundNegCircuit,
  fpToIntClampCircuit,
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
  mkROB16,
  mkQueue16x32_DualPort
]

def memoryCircuits : List Circuit :=
  [mkStoreBuffer8,
   mkLSU] ++
  cacheGeomCircuits defaultCPUConfig.cacheGeom ++
  [mkL1ICache,
   mkL1DCache,
   mkL2Cache,
   mkMemoryHierarchy]

def controlCircuits : List Circuit := [
  microcodeDecoderCircuit,
  microcodeSequencerCircuit,
  trapSequencerCircuit,
  fallbackSequencerCircuitExport,
  mkALUOpDecoder defaultCPUConfig,
  mkMulDivOpDecoder defaultCPUConfig,
  mkFPUOpDecoder defaultCPUConfig,
  mkAMOOpDecoder defaultCPUConfig
]

def cpuCircuits : List Circuit := [
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

def allCircuits : List Circuit :=
  (allAdderCircuits ++ baseCircuits.filter
    (fun c => !(allAdderCircuits.map (·.name)).contains c.name)).foldl
    (fun acc c => if acc.any (fun c' => c'.name == c.name) then acc else acc ++ [c]) []

def emittedModuleNames : List String :=
  allCircuits.map (·.name) ++ riscvDecoderModules

def subsystemCircuitNames (subsystem : String) : Option (List String) :=
  if subsystem == "all" then
    some (allCircuits.map (·.name))
  else
    match leafSubsystemCircuitNames subsystem with
    | some names => some names
    | none =>
      let adderNames := allAdderCircuits.map (·.name)
      match subsystem with
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
      | _                     => none

def circuitsForSubsystem (subsystem : String) : Option (List Circuit) :=
  match subsystemCircuitNames subsystem with
  | some names => some (allCircuits.filter (fun c => names.contains c.name))
  | none => none

end Shoumei.CircuitRegistry
