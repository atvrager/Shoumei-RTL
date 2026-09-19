/-
Verification/CompositionalCerts.lean - Export CompositionalCert instances

This file defines CompositionalCert instances for modules that are too large
for direct equivalence checking. These modules are verified compositionally:
1. Their building blocks are verified (structural proofs in Lean, plus the
   certificates of the sub-modules they themselves instantiate)
2. Hierarchical composition with correct port wiring
3. Structural proofs in Lean

All certificates are collected in `allCerts` and validated against the emitted
circuit registry by `lake exe generate_all --export-certs`.
-/

import Shoumei.Verification.Compositional
import Shoumei.RISCV.Config

namespace Shoumei.Verification.CompositionalCerts

open Shoumei.Verification
open Shoumei.RISCV

/-! ## Combinational Circuits (Large Hierarchical Muxes) -/

/-- Mux64x32: 64:1 mux, 32-bit, hierarchical (9× Mux8x32 + select buffers) -/
def mux64x32_cert : CompositionalCert := {
  moduleName := "Mux64x32"
  proofReference := "Shoumei.Circuits.Combinational.MuxTreeProofs"
}

/-- Mux64x6: 64:1 mux, 6-bit, hierarchical (9× Mux8x6 + select buffers) -/
def mux64x6_cert : CompositionalCert := {
  moduleName := "Mux64x6"
  proofReference := "Shoumei.Circuits.Combinational.MuxTreeProofs"
}

/-- Mux8x32: 8:1 mux, 32-bit, hierarchical (2× Mux4x32 + select buffers) -/
def mux8x32_cert : CompositionalCert := {
  moduleName := "Mux8x32"
  proofReference := "Shoumei.Circuits.Combinational.MuxTreeProofs"
}

/-- Mux8x64: 8:1 mux, 64-bit, hierarchical (2× Mux4x64 + select buffers) -/
def mux8x64_cert : CompositionalCert := {
  moduleName := "Mux8x64"
  proofReference := "Shoumei.Circuits.Combinational.MuxTreeProofs"
}

/-- Mux64x64: 64:1 mux, 64-bit, hierarchical (9× Mux8x64 + select buffers) -/
def mux64x64_cert : CompositionalCert := {
  moduleName := "Mux64x64"
  proofReference := "Shoumei.Circuits.Combinational.MuxTreeProofs"
}

/-- PriorityArbiter64: 64-input priority arbiter, hierarchical (9× PriorityArbiter8) -/
def priorityArbiter64_cert : CompositionalCert := {
  moduleName := "PriorityArbiter64"
  proofReference := "Shoumei.Circuits.Combinational.Arbiter"
}

/-! ## Sequential Circuits -/

/-- Register91 = Register64 + Register16 + Register8 + Register2 + Register1 -/
def register91_cert : CompositionalCert := {
  moduleName := "Register91"
  proofReference := "Shoumei.Circuits.Sequential.RegisterProofs"
}

/-- Queue64_32: Large 64-entry queue with 32-bit data -/
def queue64_32_cert : CompositionalCert := {
  moduleName := "Queue64_32"
  proofReference := "Shoumei.Circuits.Sequential.QueueProofs"
}

/-- Queue64_6: Large 64-entry queue with 6-bit data -/
def queue64_6_cert : CompositionalCert := {
  moduleName := "Queue64_6"
  proofReference := "Shoumei.Circuits.Sequential.QueueProofs"
}

/-- QueueRAM_64x32: 64-entry RAM with 32-bit data -/
def queueRAM_64x32_cert : CompositionalCert := {
  moduleName := "QueueRAM_64x32"
  proofReference := "Shoumei.Circuits.Sequential.QueueProofs"
}

/-- QueueRAM_64x6: 64-entry RAM with 6-bit data -/
def queueRAM_64x6_cert : CompositionalCert := {
  moduleName := "QueueRAM_64x6"
  proofReference := "Shoumei.Circuits.Sequential.QueueProofs"
}

/-- QueueRAMInit_64x6: 64-entry RAM with 6-bit data and initial values -/
def queueRAMInit_64x6_cert : CompositionalCert := {
  moduleName := "QueueRAMInit_64x6"
  proofReference := "Shoumei.Circuits.Sequential.QueueProofs"
}

/-- Queue64_6_Flushable: 64-entry flushable queue with 6-bit data -/
def queue64_6_flushable_cert : CompositionalCert := {
  moduleName := "Queue64_6_Flushable"
  proofReference := "Shoumei.Circuits.Sequential.QueueProofs"
}

/-- FreeList_64_Flushable: Flushable free list with correct flush recovery -/
def freeListFlushable_cert : CompositionalCert := {
  moduleName := "FreeList_64_Flushable"
  proofReference := "Shoumei.RISCV.Renaming.FreeListProofs"
}

/-- QueueRAM_2x8: 2-entry RAM with 8-bit data (verified compositionally from its building blocks) -/
def queueRAM_2x8_cert : CompositionalCert := {
  moduleName := "QueueRAM_2x8"
  proofReference := "Shoumei.Circuits.Sequential.QueueProofs"
}

/-- QueueRAM_4x8: 4-entry RAM with 8-bit data (verified compositionally from its building blocks) -/
def queueRAM_4x8_cert : CompositionalCert := {
  moduleName := "QueueRAM_4x8"
  proofReference := "Shoumei.Circuits.Sequential.QueueProofs"
}

/-- Queue2_8: 2-entry queue with 8-bit data (verified compositionally from its building blocks) -/
def queue2_8_cert : CompositionalCert := {
  moduleName := "Queue2_8"
  proofReference := "Shoumei.Circuits.Sequential.QueueProofs"
}

/-- Queue4_8: 4-entry queue with 8-bit data (verified compositionally from its building blocks) -/
def queue4_8_cert : CompositionalCert := {
  moduleName := "Queue4_8"
  proofReference := "Shoumei.Circuits.Sequential.QueueProofs"
}

/-- QueueCounterUpDown_2: flat up/down counter (induction fails on count bits) -/
def queueCounterUpDown_2_cert : CompositionalCert := {
  moduleName := "QueueCounterUpDown_2"
  proofReference := "Shoumei.Circuits.Sequential.QueueProofs"
}

/-- QueueCounterUpDown_3: flat up/down counter (induction fails on count bits) -/
def queueCounterUpDown_3_cert : CompositionalCert := {
  moduleName := "QueueCounterUpDown_3"
  proofReference := "Shoumei.Circuits.Sequential.QueueProofs"
}

/-- QueueCounterUpDown_4: flat up/down counter (induction fails on count bits) -/
def queueCounterUpDown_4_cert : CompositionalCert := {
  moduleName := "QueueCounterUpDown_4"
  proofReference := "Shoumei.Circuits.Sequential.QueueProofs"
}

/-- QueueCounterUpDown_5: flat up/down counter (induction fails on count bits) -/
def queueCounterUpDown_5_cert : CompositionalCert := {
  moduleName := "QueueCounterUpDown_5"
  proofReference := "Shoumei.Circuits.Sequential.QueueProofs"
}

/-- QueueCounterUpDown_7: flat up/down counter (induction fails on count bits) -/
def queueCounterUpDown_7_cert : CompositionalCert := {
  moduleName := "QueueCounterUpDown_7"
  proofReference := "Shoumei.Circuits.Sequential.QueueProofs"
}

/-- QueuePointer_1: flat pointer counter (induction fails on count bits) -/
def queuePointer_1_cert : CompositionalCert := {
  moduleName := "QueuePointer_1"
  proofReference := "Shoumei.Circuits.Sequential.QueueProofs"
}

/-- QueuePointer_2: flat pointer counter (induction fails on count bits) -/
def queuePointer_2_cert : CompositionalCert := {
  moduleName := "QueuePointer_2"
  proofReference := "Shoumei.Circuits.Sequential.QueueProofs"
}

/-- QueuePointer_3: flat pointer counter (induction fails on count bits) -/
def queuePointer_3_cert : CompositionalCert := {
  moduleName := "QueuePointer_3"
  proofReference := "Shoumei.Circuits.Sequential.QueueProofs"
}

/-- QueuePointer_4: flat pointer counter (induction fails on count bits) -/
def queuePointer_4_cert : CompositionalCert := {
  moduleName := "QueuePointer_4"
  proofReference := "Shoumei.Circuits.Sequential.QueueProofs"
}

/-- QueuePointer_6: flat pointer counter (induction fails on count bits) -/
def queuePointer_6_cert : CompositionalCert := {
  moduleName := "QueuePointer_6"
  proofReference := "Shoumei.Circuits.Sequential.QueueProofs"
}

/-- Register256 = Register64 × 4 (hierarchical, cache line data storage) -/
def register256_cert : CompositionalCert := {
  moduleName := "Register256"
  proofReference := "Shoumei.Circuits.Sequential.RegisterProofs"
}

/-- Register24 = Register16 + Register8 (hierarchical) -/
def register24_cert : CompositionalCert := {
  moduleName := "Register24"
  proofReference := "Shoumei.Circuits.Sequential.RegisterProofs"
}

/-- Register66 = Register64 + Register2 (hierarchical) -/
def register66_cert : CompositionalCert := {
  moduleName := "Register66"
  proofReference := "Shoumei.Circuits.Sequential.RegisterProofs"
}

/-- Register68 = Register64 + Register4 (hierarchical) -/
def register68_cert : CompositionalCert := {
  moduleName := "Register68"
  proofReference := "Shoumei.Circuits.Sequential.RegisterProofs"
}

/-- Register98 = Register64 + Register32 + Register2 (hierarchical) -/
def register98_cert : CompositionalCert := {
  moduleName := "Register98"
  proofReference := "Shoumei.Circuits.Sequential.RegisterProofs"
}

/-- Register130 = Register64 + Register64 + Register2 (hierarchical) -/
def register130_cert : CompositionalCert := {
  moduleName := "Register130"
  proofReference := "Shoumei.Circuits.Sequential.RegisterProofs"
}

/-- Register96 = Register64 + Register32 (hierarchical) -/
def register96_cert : CompositionalCert := {
  moduleName := "Register96"
  proofReference := "Shoumei.Circuits.Sequential.RegisterProofs"
}

/-- Register157 = Register64 + Register64 + Register16 + Register8 + Register4 + Register1 (hierarchical) -/
def register157_cert : CompositionalCert := {
  moduleName := "Register157"
  proofReference := "Shoumei.Circuits.Sequential.RegisterProofs"
}

/-- Register158 = Register64 + Register64 + Register16 + Register8 + Register4 + Register2 (hierarchical) -/
def register158_cert : CompositionalCert := {
  moduleName := "Register158"
  proofReference := "Shoumei.Circuits.Sequential.RegisterProofs"
}

/-- Register159 = Register64 + Register64 + Register16 + Register8 + Register4 + Register2 + Register1 (hierarchical) -/
def register159_cert : CompositionalCert := {
  moduleName := "Register159"
  proofReference := "Shoumei.Circuits.Sequential.RegisterProofs"
}

/-- Register160 = Register64 + Register64 + Register32 (hierarchical) -/
def register160_cert : CompositionalCert := {
  moduleName := "Register160"
  proofReference := "Shoumei.Circuits.Sequential.RegisterProofs"
}


/-! ## RISC-V Renaming -/

/-- PhysRegFile_64x32: Physical register file (64 registers × 32 bits) -/
def physregfile_cert : CompositionalCert := {
  moduleName := "PhysRegFile_64x32"
  proofReference := "Shoumei.RISCV.Renaming.PhysRegFileProofs"
}

/-- PhysRegFile_64x64: Physical register file (64 registers × 64 bits) -/
def physregfile_64x64_cert : CompositionalCert := {
  moduleName := "PhysRegFile_64x64"
  proofReference := "Shoumei.RISCV.Renaming.PhysRegFileProofs"
}

/-- RAT_32x6: Register alias table (32 architectural → 64 physical) -/
def rat_cert : CompositionalCert := {
  moduleName := "RAT_32x6"
  proofReference := "Shoumei.RISCV.Renaming.RATProofs"
}

/-- CRAT_32x6: Committed register alias table (32 architectural → 64 physical) -/
def crat_cert : CompositionalCert := {
  moduleName := "CRAT_32x6"
  proofReference := "Shoumei.RISCV.Renaming.RATProofs"
}

/-- FreeList_64: Free physical register list (64-entry queue) -/
def freelist_cert : CompositionalCert := {
  moduleName := "FreeList_64"
  proofReference := "Shoumei.RISCV.Renaming.FreeListProofs"
}

/-- BitmapFreeList_64_W2: Dual-dequeue bitmap free list for N=2 -/
def bitmapFreelist_w2_cert : CompositionalCert := {
  moduleName := "BitmapFreeList_64_W2"
  proofReference := "Shoumei.RISCV.Renaming.BitmapFreeListProofs"
}

/-- IntRAT_32x6: Integer register alias table (no rs3) -/
def intRat_cert : CompositionalCert := {
  moduleName := "IntRAT_32x6"
  proofReference := "Shoumei.RISCV.Renaming.RATProofs"
}

/-- BitmapFreeList_64_W1: Single-dequeue bitmap free list for FP domain -/
def bitmapFreelist_w1_cert : CompositionalCert := {
  moduleName := "BitmapFreeList_64_W1"
  proofReference := "Shoumei.RISCV.Renaming.BitmapFreeListProofs"
}

/-- IntPhysRegFile_64x32: Integer physical register file (64 registers × 32 bits, 6 read ports) -/
def intPhysRegFile_cert : CompositionalCert := {
  moduleName := "IntPhysRegFile_64x32"
  proofReference := "Shoumei.RISCV.Renaming.PhysRegFileProofs"
}

/-- IntPhysRegFile_64x64: Integer physical register file (64 registers × 64 bits, 6 read ports) -/
def intPhysRegFile_64x64_cert : CompositionalCert := {
  moduleName := "IntPhysRegFile_64x64"
  proofReference := "Shoumei.RISCV.Renaming.PhysRegFileProofs"
}

/-- FPPhysRegFile_64x32: FP physical register file (64 registers × 32 bits, 3 read ports) -/
def fpPhysRegFile_cert : CompositionalCert := {
  moduleName := "FPPhysRegFile_64x32"
  proofReference := "Shoumei.RISCV.Renaming.PhysRegFileProofs"
}

/-- FPPhysRegFile_64x64: FP physical register file (64 registers × 64 bits, 3 read ports) -/
def fpPhysRegFile_64x64_cert : CompositionalCert := {
  moduleName := "FPPhysRegFile_64x64"
  proofReference := "Shoumei.RISCV.Renaming.PhysRegFileProofs"
}

/-! ## M-Extension -/

/-- PipelinedMultiplier: 3-stage pipelined array multiplier -/
def pipelinedMultiplier_cert : CompositionalCert := {
  moduleName := "PipelinedMultiplier"
  proofReference := "Shoumei.Circuits.Combinational.MultiplierProofs"
}

/-- PipelinedMultiplier64: 3-stage pipelined 64-bit multiplier -/
def pipelinedMultiplier64_cert : CompositionalCert := {
  moduleName := "PipelinedMultiplier64"
  proofReference := "Shoumei.Circuits.Combinational.MultiplierProofs"
}

/-- Divider32: 32-cycle restoring divider -/
def divider32_cert : CompositionalCert := {
  moduleName := "Divider32"
  proofReference := "Shoumei.Circuits.Sequential.DividerProofs"
}

/-- Divider64: 64-cycle restoring divider -/
def divider64_cert : CompositionalCert := {
  moduleName := "Divider64"
  proofReference := "Shoumei.Circuits.Sequential.DividerProofs"
}

/-- MulDivExecUnit: Combined multiply/divide execution unit -/
def muldivExecUnit_cert : CompositionalCert := {
  moduleName := "MulDivExecUnit"
  proofReference := "Shoumei.RISCV.Execution.MulDivExecUnitProofs"
}


/-- ReservationStation4_W2_64: 64-bit dual-issue reservation station -/
def rs4w2_64_cert : CompositionalCert := {
  moduleName := "ReservationStation4_W2_64"
  proofReference := "Shoumei.RISCV.Execution.ReservationStationProofs"
}

/-- IntReservationStation4_W2_64: 64-bit specialized integer reservation station -/
def intRs4w2_64_cert : CompositionalCert := {
  moduleName := "IntReservationStation4_W2_64"
  proofReference := "Shoumei.RISCV.Execution.ReservationStationProofs"
}

/-- ReservationStation2_W1_64: 64-bit specialized single-issue reservation station -/
def rs2w1_64_cert : CompositionalCert := {
  moduleName := "ReservationStation2_W1_64"
  proofReference := "Shoumei.RISCV.Execution.ReservationStationProofs"
}

/-- MemoryReservationStation2_W1_64: 64-bit specialized memory reservation station -/
def memRs2w1_64_cert : CompositionalCert := {
  moduleName := "MemoryReservationStation2_W1_64"
  proofReference := "Shoumei.RISCV.Execution.ReservationStationProofs"
}

/-- FPReservationStation2_W1_64: 64-bit specialized floating-point reservation station -/
def fpRs2w1_64_cert : CompositionalCert := {
  moduleName := "FPReservationStation2_W1_64"
  proofReference := "Shoumei.RISCV.Execution.ReservationStationProofs"
}

/-! ## RISC-V Retirement -/

/-- Queue16x32: 16-entry × 32-bit register array for RVVI PC/instruction queues -/
def queue16x32_cert : CompositionalCert := {
  moduleName := "Queue16x32"
  proofReference := "Shoumei.RISCV.Retirement.Queue16x32"
}

/-- Queue16x32_DualPort: Dual-port 16×32 queue (2 read + 2 write) -/
def queue16x32_dualport_cert : CompositionalCert := {
  moduleName := "Queue16x32_DualPort"
  proofReference := "Shoumei.RISCV.Retirement.Queue16x32"
}

/-- ROB16_W2: 16-entry reorder buffer for dual-issue in-order commit -/
def rob16_w2_cert : CompositionalCert := {
  moduleName := "ROB16_W2"
  proofReference := "Shoumei.RISCV.Retirement.ROBProofs"
}

/-! ## RISC-V Memory -/

/-- StoreBuffer8: 8-entry store buffer with forwarding (FIFO redesign) -/
def storeBuffer8_cert : CompositionalCert := {
  moduleName := "StoreBuffer8"
  proofReference := "Shoumei.RISCV.Memory.StoreBufferProofs"
}

/-- LSU: Load-Store Unit (address generation + store buffering) -/
def lsu_cert : CompositionalCert := {
  moduleName := "LSU"
  proofReference := "Shoumei.RISCV.Memory.LSUProofs"
}

/-- MemoryExecUnitDecoupled: independent STA/STD micro-op output groups. -/
def memoryExecUnitDecoupled_cert : CompositionalCert := {
  moduleName := "MemoryExecUnitDecoupled"
  proofReference := "Shoumei.RISCV.Execution.MemoryExecUnitCodegen"
}

/-! ## Cache Hierarchy -/

/-- L1ICache: Direct-mapped L1 instruction cache -/
def l1iCache_cert : CompositionalCert := {
  moduleName := "L1ICache"
  proofReference := "Shoumei.RISCV.Memory.Cache.L1ICacheProofs"
}

/-- L1DCache: 2-way set-associative L1 data cache -/
def l1dCache_cert : CompositionalCert := {
  moduleName := "L1DCache"
  proofReference := "Shoumei.RISCV.Memory.Cache.L1DCacheProofs"
}

/-- L2Cache: 2-way set-associative shared L2 cache -/
def l2Cache_cert : CompositionalCert := {
  moduleName := "L2Cache"
  proofReference := "Shoumei.RISCV.Memory.Cache.L2CacheProofs"
}

/-- MemoryHierarchy: L1I + L1D + L2 composition -/
def memoryHierarchy_cert : CompositionalCert := {
  moduleName := "MemoryHierarchy"
  proofReference := "Shoumei.RISCV.Memory.Cache.MemoryHierarchyProofs"
}

/-- CachedCPU: CPU + L1I + L1D + L2 composition -/
def cachedCPU_cert : CompositionalCert := {
  moduleName := Shoumei.RISCV.defaultCPUConfig.fullName
  proofReference := "Shoumei.RISCV.Memory.Cache.CachedCPUProofs"
}

/-- Shoumei SoC: CachedCPU + ResetSync + TLXbar8 + BootROM + ACLINT + APLIC + UART + GPIO + SRAM -/
def shoumeiSoC_cert : CompositionalCert := {
  moduleName := "Shoumei_SoC"
  proofReference := "Shoumei.SoC.ShoumeiSoCProofs"
}

/-! ## Decoders (LUT-based) -/

/-- RV32IMFDecoder: Pure LUT decoder.
    Verified by construction: the Lean DSL generates the truth table directly
    from the ISA spec, and the decoder proof shows it matches. -/
def rv32ifDecoder_cert : CompositionalCert := {
  moduleName := "RV32IFDecoder"
  proofReference := "Shoumei.RISCV.DecoderProofs"
}

def rv32imfDecoder_cert : CompositionalCert := {
  moduleName := "RV32IMFDecoder"
  proofReference := "Shoumei.RISCV.DecoderProofs"
}

def rv32gDecoder_cert : CompositionalCert := {
  moduleName := "RV32GDecoder"
  proofReference := "Shoumei.RISCV.DecoderProofs"
}

def rv64gDecoder_cert : CompositionalCert := {
  moduleName := "RV64GDecoder"
  proofReference := "Shoumei.RISCV.DecoderProofs"
}

/-! ## F-Extension -/

/-- FPAdder: IEEE 754 SP adder (sequential, pipeline DFFs cause induction failure) -/
def fpAdder_cert : CompositionalCert := {
  moduleName := "FPAdder"
  proofReference := "Shoumei.Circuits.Sequential.FPAdderProofs"
}

/-- FPMultiplier: IEEE 754 SP multiplier (sequential, pipeline DFFs cause induction failure) -/
def fpMultiplier_cert : CompositionalCert := {
  moduleName := "FPMultiplier"
  proofReference := "Shoumei.Circuits.Sequential.FPMultiplierProofs"
}

/-- FPFMA: IEEE 754 SP fused multiply-add (sequential, pipeline DFFs cause induction failure) -/
def fpFMA_cert : CompositionalCert := {
  moduleName := "FPFMA"
  proofReference := "Shoumei.Circuits.Sequential.FPFMAProofs"
}

/-- FPDivider: IEEE 754 SP divider (sequential, multi-cycle state machine) -/
def fpDivider_cert : CompositionalCert := {
  moduleName := "FPDivider"
  proofReference := "Shoumei.Circuits.Sequential.FPDividerProofs"
}

/-- FPSqrt: IEEE 754 SP square root (sequential, multi-cycle state machine) -/
def fpSqrt_cert : CompositionalCert := {
  moduleName := "FPSqrt"
  proofReference := "Shoumei.Circuits.Sequential.FPSqrtProofs"
}

/-- FPExecUnit: Combined FP execution unit (structural proof + leaf certs) -/
def fpExecUnit_cert : CompositionalCert := {
  moduleName := "FPExecUnit"
  proofReference := "Shoumei.RISCV.Execution.FPExecUnitProofs"
}

/-- FPMisc: FP sign injection, compare, classify, convert -/
def fpMisc_cert : CompositionalCert := {
  moduleName := "FPMisc"
  proofReference := "Shoumei.Circuits.Combinational.FPMiscProofs"
}

/-- FPDoubleMisc: Double-precision FP sign injection, compare, classify, min/max -/
def fpDoubleMisc_cert : CompositionalCert := {
  moduleName := "FPDoubleMisc"
  proofReference := "Shoumei.Circuits.Combinational.FPDoubleMiscProofs"
}

/-- FPDoubleConverter: Double-precision FP converters (float-int, float-float) -/
def fpDoubleConverter_cert : CompositionalCert := {
  moduleName := "FPDoubleConverter"
  proofReference := "Shoumei.Circuits.Combinational.FPDoubleConverterProofs"
}

/-- FPLongConverter: 64-bit FP/Integer converter (hierarchical: Int64ToFP + FPToInt64) -/
def fpLongConverter_cert : CompositionalCert := {
  moduleName := "FPLongConverter"
  proofReference := "Shoumei.Circuits.Combinational.FPLongConverterProofs"
}

/-- FPAdderD: IEEE 754 DP adder (sequential, multi-stage pipeline) -/
def fpAdderD_cert : CompositionalCert := {
  moduleName := "FPAdderD"
  proofReference := "Shoumei.Circuits.Sequential.FPAdderDProofs"
}

/-- FPMultiplierD: IEEE 754 DP multiplier (sequential, multi-stage pipeline) -/
def fpMultiplierD_cert : CompositionalCert := {
  moduleName := "FPMultiplierD"
  proofReference := "Shoumei.Circuits.Sequential.FPMultiplierDProofs"
}

/-- FPFMAD: IEEE 754 DP fused multiply-add (sequential, multi-stage pipeline) -/
def fpFMAD_cert : CompositionalCert := {
  moduleName := "FPFMAD"
  proofReference := "Shoumei.Circuits.Sequential.FPFMADProofs"
}

/-- FPDividerD: IEEE 754 DP divider (sequential, multi-cycle state machine) -/
def fpDividerD_cert : CompositionalCert := {
  moduleName := "FPDividerD"
  proofReference := "Shoumei.Circuits.Sequential.FPDividerDProofs"
}

/-- FPSqrtD: IEEE 754 DP square root (sequential, multi-cycle state machine) -/
def fpSqrtD_cert : CompositionalCert := {
  moduleName := "FPSqrtD"
  proofReference := "Shoumei.Circuits.Sequential.FPSqrtDProofs"
}

/-- FPExecUnit_D: Combined DP/SP FP execution unit (structural proof + leaf certs) -/
def fpExecUnit_d_cert : CompositionalCert := {
  moduleName := "FPExecUnit_D"
  proofReference := "Shoumei.RISCV.Execution.FPExecUnitProofs"
}

/-- RenameStage_W2: Composite rename stage for dual issue -/
def renameStage_w2_cert : CompositionalCert := {
  moduleName := "RenameStage_W2"
  proofReference := "Shoumei.RISCV.Renaming.RenameStageProofs"
}

/-- RenameStage_W2_64: Composite rename stage for dual issue (64-bit FP domain) -/
def renameStage_w2_64_cert : CompositionalCert := {
  moduleName := "RenameStage_W2_64"
  proofReference := "Shoumei.RISCV.Renaming.RenameStageProofs"
}

/-- IntRenameStage_W2: Integer rename stage for dual issue (32-bit) -/
def intRenameStage_w2_cert : CompositionalCert := {
  moduleName := "IntRenameStage_W2"
  proofReference := "Shoumei.RISCV.Renaming.RenameStageProofs"
}

/-- IntRenameStage_W2_64: Integer rename stage for dual issue (64-bit) -/
def intRenameStage_w2_64_cert : CompositionalCert := {
  moduleName := "IntRenameStage_W2_64"
  proofReference := "Shoumei.RISCV.Renaming.RenameStageProofs"
}

/-- FPRenameStage_W1: FP rename stage for single issue (32-bit) -/
def fpRenameStage_w1_cert : CompositionalCert := {
  moduleName := "FPRenameStage_W1"
  proofReference := "Shoumei.RISCV.Renaming.RenameStageProofs"
}

/-- FPRenameStage_W1_64: FP rename stage for single issue (64-bit) -/
def fpRenameStage_w1_64_cert : CompositionalCert := {
  moduleName := "FPRenameStage_W1_64"
  proofReference := "Shoumei.RISCV.Renaming.RenameStageProofs"
}

/-- MicrocodeSequencer: ROM-driven µop sequencer for CSR/FENCE.I -/
def microcodeSequencer_cert : CompositionalCert := {
  moduleName := "MicrocodeSequencer"
  proofReference := "Shoumei.RISCV.Microcode.MicrocodeSequencerProofs"
}

/-- TrapSequencer: Dedicated sequencer for TRAP_ENTRY and MRET sequences -/
def trapSequencer_cert : CompositionalCert := {
  moduleName := "TrapSequencer"
  proofReference := "Shoumei.RISCV.Microcode.TrapSequencerProofs"
}

/-- CSRFile: Control and Status Register file (12 32-bit registers + WARL/traps/counters) -/
def csrFile_cert : CompositionalCert := {
  moduleName := s!"CSRFile_{Shoumei.RISCV.defaultCPUConfig.isaString}"
  proofReference := "Shoumei.RISCV.CSRFileProofs"
}

/-- BusyTable_W2: Dual-port scoreboard busy bit table (64 DFFs + 4 read muxes + RAW hazard logic) -/
def busyTable_w2_cert : CompositionalCert := {
  moduleName := "BusyTable_W2"
  proofReference := "Shoumei.RISCV.CPU.BusyBitTableProofs"
}

/-- FPBusyTable: Single-port FP scoreboard busy bit table (64 DFFs + 3 read muxes) -/
def fpBusyTable_cert : CompositionalCert := {
  moduleName := "FPBusyTable"
  proofReference := "Shoumei.RISCV.CPU.BusyBitTableProofs"
}

/-- W=2 dual-issue microcoded CPU.  The module name is the config's, so enabling
    or renaming an extension renames the certificate with the circuit. -/
def cpu_microcoded_cert : CompositionalCert := {
  moduleName := s!"CPU_{Shoumei.RISCV.defaultCPUConfig.isaString}"
  proofReference := "Shoumei.RISCV.CPUProofs"
}

/-! ## Export All -/

def allCerts : List CompositionalCert := [
  -- Combinational (hierarchical muxes and arbiters)
  mux64x32_cert,
  mux8x32_cert,
  mux8x64_cert,
  mux64x64_cert,
  priorityArbiter64_cert,
  -- Sequential
  register24_cert,
  register96_cert,
  register98_cert,
  register130_cert,
  register157_cert,
  register158_cert,
  register159_cert,
  register160_cert,
  queuePointer_3_cert,
  -- Renaming
  physregfile_cert,
  physregfile_64x64_cert,
  intPhysRegFile_cert,
  intPhysRegFile_64x64_cert,
  fpPhysRegFile_cert,
  fpPhysRegFile_64x64_cert,
  rat_cert,
  intRat_cert,
  crat_cert,
  bitmapFreelist_w2_cert,
  bitmapFreelist_w1_cert,
  -- Execution
  -- M-Extension
  pipelinedMultiplier_cert,
  pipelinedMultiplier64_cert,
  divider32_cert,
  divider64_cert,
  muldivExecUnit_cert,
  rs4w2_64_cert,
  intRs4w2_64_cert,
  rs2w1_64_cert,
  memRs2w1_64_cert,
  fpRs2w1_64_cert,
  -- Retirement
  queue16x32_dualport_cert,
  rob16_w2_cert,
  -- Memory
  storeBuffer8_cert,
  lsu_cert,
  memoryExecUnitDecoupled_cert,
  -- Cache Hierarchy
  l1iCache_cert,
  l1dCache_cert,
  l2Cache_cert,
  memoryHierarchy_cert,
  -- Decoders
  rv64gDecoder_cert,
  -- F-Extension
  fpMisc_cert,
  fpAdder_cert,
  fpMultiplier_cert,
  fpFMA_cert,
  fpDivider_cert,
  fpSqrt_cert,
  fpExecUnit_cert,
  -- D-Extension
  fpDoubleMisc_cert,
  fpDoubleConverter_cert,
  fpLongConverter_cert,
  fpAdderD_cert,
  fpMultiplierD_cert,
  fpFMAD_cert,
  fpDividerD_cert,
  fpSqrtD_cert,
  fpExecUnit_d_cert,
  -- Phase 8: Top-Level Integration
  renameStage_w2_cert,
  renameStage_w2_64_cert,
  intRenameStage_w2_cert,
  intRenameStage_w2_64_cert,
  fpRenameStage_w1_cert,
  fpRenameStage_w1_64_cert,
  -- CSR File
  csrFile_cert,
  -- Scoreboard Busy Tables
  busyTable_w2_cert,
  fpBusyTable_cert,
  -- Microcode
  microcodeSequencer_cert,
  trapSequencer_cert,
  -- Microcoded variant
  cpu_microcoded_cert,
  -- Microcoded cached variant
  cachedCPU_cert,
  -- Shoumei SoC top-level
  shoumeiSoC_cert
]

end Shoumei.Verification.CompositionalCerts
