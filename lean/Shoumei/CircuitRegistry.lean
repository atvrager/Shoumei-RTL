/-
CircuitRegistry.lean - Centralized Circuit Registry for Shoumei RTL

Maintains the complete list of circuits emitted by the RTL generators
and inspected by architecture visualization tools.
-/

import Shoumei.DSL
import Shoumei.Components.Select

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

def foundationBaseCircuits : List Circuit := [
  dff,
  fullAdderCircuit,
  mkRippleCarryAdder4,
  mkLogicUnit4,
  mkMux4x1,
  mkComparator4,
  q1w1,
  mkQueue1StructuralComplete 8,
  mkQueue1FlowStructural 39,
  mkQueue1FlowStructural 70,
  mkQueue1FlowStructural 71,
  mkQueue1FlowStructural 72,
  mkQueue1FlowStructural 103,
  mkQueue1FlowStructural 104,
  mkQueue1FlowStructural 43,
  mkQueue1FlowStructural 44,
  mkQueue1FlowStructural 75,
  mkQueue1FlowStructural 76
]

def combinationalCircuits : List Circuit := [
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
  mkDecoder 2,
  mkDecoder 3,
  mkDecoder 4,
  mkDecoder 5,
  mkDecoder 6,
  mkDecoder 7,
  mkComparatorN 6,
  mkEqualityComparatorN 6,
  mkEqualityComparator32,
  mkEqualityComparator64,
  mkMuxTree 4 32,
  mkMuxTree 4 64,
  mkMuxTree 8 2,
  mkMux8x32Hierarchical,
  mkMux8x64Hierarchical,
  mkMuxTree 16 5,
  mkMuxTree 16 6,
  mkMuxTree 16 32,
  mkMux32x6,
  mkMux64x32Hierarchical,
  mkMux64x64Hierarchical,
  mkMuxTree 64 5,
  mkPriorityArbiter2,
  mkPriorityArbiter8,
  mkPriorityArbiter64,
  mkOneHotEncoder64,
  mkPopcount8
]

def sequentialCircuits : List Circuit := [
  mkQueuePointer 3,
  mkQueuePointerLoadable 3,
  mkQueueCounterLoadable 4,
  mkRegisterN 1,
  mkRegisterN 2,
  mkRegisterN 3,
  mkRegisterN 4,
  mkRegisterN 6,
  mkRegisterN 8,
  mkRegisterN 12,
  mkRegisterN 16,
  mkRegisterN 5,
  mkRegisterN 24,
  mkRegisterN 32,
  mkRegisterN 64,
  mkRegisterEnN 1,
  mkRegisterEnN 2,
  mkRegisterEnN 4,
  mkRegisterEnN 8,
  mkRegisterEnN 16,
  mkRegisterEnN 32,
  mkRegisterEnN 64,
  mkRegisterNHierarchical 96,
  mkRegisterNHierarchical 98,
  mkRegisterNHierarchical 130,
  mkRegisterNHierarchical 157,
  mkRegisterNHierarchical 158,
  mkRegisterNHierarchical 159,
  mkRegisterNHierarchical 160,
  mkRegister160Flat
]

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

end Shoumei.CircuitRegistry
