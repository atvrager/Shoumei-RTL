/-
Verification/CompositionalCerts.lean - Export CompositionalCert instances

This file defines CompositionalCert instances for modules that are too large
for direct LEC verification. These modules are verified compositionally:
1. LEC verification of power-of-2 building blocks
2. Hierarchical composition with correct port wiring  
3. Structural proofs in Lean

All certificates are exported via ExportVerificationCerts.lean.
-/

import Shoumei.Verification.Compositional

namespace Shoumei.Verification.CompositionalCerts

open Shoumei.Verification

/-! ## Sequential Circuits -/

/-- Register91 = Register64 + Register16 + Register8 + Register2 + Register1 -/
def register91_cert : CompositionalCert := {
  moduleName := "Register91"
  dependencies := ["Register64", "Register16", "Register8", "Register2", "Register1"]
  proofReference := "Shoumei.Circuits.Sequential.RegisterProofs"
}

/-- Queue64_32: Large 64-entry queue with 32-bit data -/
def queue64_32_cert : CompositionalCert := {
  moduleName := "Queue64_32"
  dependencies := ["QueueRAM_64x32", "QueuePointer_6", "QueueCounterUpDown_7"]
  proofReference := "Shoumei.Circuits.Sequential.QueueProofs"
}

/-- Queue64_6: Large 64-entry queue with 6-bit data -/
def queue64_6_cert : CompositionalCert := {
  moduleName := "Queue64_6"
  dependencies := ["QueueRAM_64x6", "QueuePointer_6", "QueueCounterUpDown_7"]
  proofReference := "Shoumei.Circuits.Sequential.QueueProofs"
}

/-- QueueRAM_64x32: 64-entry RAM with 32-bit data -/
def queueRAM_64x32_cert : CompositionalCert := {
  moduleName := "QueueRAM_64x32"
  dependencies := ["Decoder6", "Mux64x32"]
  proofReference := "Shoumei.Circuits.Sequential.QueueProofs"
}

/-- QueueRAM_64x6: 64-entry RAM with 6-bit data -/
def queueRAM_64x6_cert : CompositionalCert := {
  moduleName := "QueueRAM_64x6"
  dependencies := ["Decoder6", "Mux64x6"]
  proofReference := "Shoumei.Circuits.Sequential.QueueProofs"
}

/-- QueueRAMInit_64x6: 64-entry RAM with 6-bit data and initial values -/
def queueRAMInit_64x6_cert : CompositionalCert := {
  moduleName := "QueueRAMInit_64x6"
  dependencies := ["Decoder6", "Mux64x6"]
  proofReference := "Shoumei.Circuits.Sequential.QueueProofs"
}

/-- Queue64_6_Flushable: 64-entry flushable queue with 6-bit data -/
def queue64_6_flushable_cert : CompositionalCert := {
  moduleName := "Queue64_6_Flushable"
  dependencies := ["QueueRAMInit_64x6", "QueuePointerLoadable_6", "QueuePointerInit_6", "QueueCounterLoadableInit_7"]
  proofReference := "Shoumei.Circuits.Sequential.QueueProofs"
}

/-- FreeList_64_Flushable: Flushable free list with correct flush recovery -/
def freeListFlushable_cert : CompositionalCert := {
  moduleName := "FreeList_64_Flushable"
  dependencies := ["QueueRAMInit_64x6", "QueuePointerLoadable_6", "QueuePointerInit_6", "QueueCounterLoadableInit_7"]
  proofReference := "Shoumei.RISCV.Renaming.FreeListProofs"
}

/-- QueueRAM_2x8: 2-entry RAM with 8-bit data (structural differences prevent direct LEC) -/
def queueRAM_2x8_cert : CompositionalCert := {
  moduleName := "QueueRAM_2x8"
  dependencies := ["Decoder1", "Mux2x8"]
  proofReference := "Shoumei.Circuits.Sequential.QueueProofs"
}

/-- QueueRAM_4x8: 4-entry RAM with 8-bit data (structural differences prevent direct LEC) -/
def queueRAM_4x8_cert : CompositionalCert := {
  moduleName := "QueueRAM_4x8"
  dependencies := ["Decoder2", "Mux4x8"]
  proofReference := "Shoumei.Circuits.Sequential.QueueProofs"
}

/-- Queue2_8: 2-entry queue with 8-bit data (structural differences prevent direct LEC) -/
def queue2_8_cert : CompositionalCert := {
  moduleName := "Queue2_8"
  dependencies := ["QueueRAM_2x8", "QueuePointer_1", "QueueCounterUpDown_2"]
  proofReference := "Shoumei.Circuits.Sequential.QueueProofs"
}

/-- Queue4_8: 4-entry queue with 8-bit data (structural differences prevent direct LEC) -/
def queue4_8_cert : CompositionalCert := {
  moduleName := "Queue4_8"
  dependencies := ["QueueRAM_4x8", "QueuePointer_2", "QueueCounterUpDown_3"]
  proofReference := "Shoumei.Circuits.Sequential.QueueProofs"
}

/-- QueueCounterUpDown_2: flat up/down counter (induction fails on count bits) -/
def queueCounterUpDown_2_cert : CompositionalCert := {
  moduleName := "QueueCounterUpDown_2"
  dependencies := []
  proofReference := "Shoumei.Circuits.Sequential.QueueProofs"
}

/-- QueueCounterUpDown_3: flat up/down counter (induction fails on count bits) -/
def queueCounterUpDown_3_cert : CompositionalCert := {
  moduleName := "QueueCounterUpDown_3"
  dependencies := []
  proofReference := "Shoumei.Circuits.Sequential.QueueProofs"
}

/-- QueueCounterUpDown_4: flat up/down counter (induction fails on count bits) -/
def queueCounterUpDown_4_cert : CompositionalCert := {
  moduleName := "QueueCounterUpDown_4"
  dependencies := []
  proofReference := "Shoumei.Circuits.Sequential.QueueProofs"
}

/-- QueueCounterUpDown_5: flat up/down counter (induction fails on count bits) -/
def queueCounterUpDown_5_cert : CompositionalCert := {
  moduleName := "QueueCounterUpDown_5"
  dependencies := []
  proofReference := "Shoumei.Circuits.Sequential.QueueProofs"
}

/-- QueueCounterUpDown_7: flat up/down counter (induction fails on count bits) -/
def queueCounterUpDown_7_cert : CompositionalCert := {
  moduleName := "QueueCounterUpDown_7"
  dependencies := []
  proofReference := "Shoumei.Circuits.Sequential.QueueProofs"
}

/-- QueuePointer_1: flat pointer counter (induction fails on count bits) -/
def queuePointer_1_cert : CompositionalCert := {
  moduleName := "QueuePointer_1"
  dependencies := []
  proofReference := "Shoumei.Circuits.Sequential.QueueProofs"
}

/-- QueuePointer_2: flat pointer counter (induction fails on count bits) -/
def queuePointer_2_cert : CompositionalCert := {
  moduleName := "QueuePointer_2"
  dependencies := []
  proofReference := "Shoumei.Circuits.Sequential.QueueProofs"
}

/-- QueuePointer_3: flat pointer counter (induction fails on count bits) -/
def queuePointer_3_cert : CompositionalCert := {
  moduleName := "QueuePointer_3"
  dependencies := []
  proofReference := "Shoumei.Circuits.Sequential.QueueProofs"
}

/-- QueuePointer_4: flat pointer counter (induction fails on count bits) -/
def queuePointer_4_cert : CompositionalCert := {
  moduleName := "QueuePointer_4"
  dependencies := []
  proofReference := "Shoumei.Circuits.Sequential.QueueProofs"
}

/-- QueuePointer_6: flat pointer counter (induction fails on count bits) -/
def queuePointer_6_cert : CompositionalCert := {
  moduleName := "QueuePointer_6"
  dependencies := []
  proofReference := "Shoumei.Circuits.Sequential.QueueProofs"
}

/-- Register24 = Register16 + Register8 (hierarchical) -/
def register24_cert : CompositionalCert := {
  moduleName := "Register24"
  dependencies := ["Register16", "Register8"]
  proofReference := "Shoumei.Circuits.Sequential.RegisterProofs"
}

/-- Register66 = Register64 + Register2 (hierarchical) -/
def register66_cert : CompositionalCert := {
  moduleName := "Register66"
  dependencies := ["Register64", "Register2"]
  proofReference := "Shoumei.Circuits.Sequential.RegisterProofs"
}

/-- Register68 = Register64 + Register4 (hierarchical) -/
def register68_cert : CompositionalCert := {
  moduleName := "Register68"
  dependencies := ["Register64", "Register4"]
  proofReference := "Shoumei.Circuits.Sequential.RegisterProofs"
}

/-! ## RISC-V Renaming -/

/-- PhysRegFile_64x32: Physical register file (64 registers × 32 bits) -/
def physregfile_cert : CompositionalCert := {
  moduleName := "PhysRegFile_64x32"
  dependencies := ["Decoder6", "Mux64x32"]
  proofReference := "Shoumei.RISCV.Renaming.PhysRegFileProofs"
}

/-- RAT_32x6: Register alias table (32 architectural → 64 physical) -/
def rat_cert : CompositionalCert := {
  moduleName := "RAT_32x6"
  dependencies := ["Decoder5", "Mux32x6"]
  proofReference := "Shoumei.RISCV.Renaming.RATProofs"
}

/-- FreeList_64: Free physical register list (64-entry queue) -/
def freelist_cert : CompositionalCert := {
  moduleName := "FreeList_64"
  dependencies := ["QueueRAM_64x6", "QueuePointer_6", "QueueCounterUpDown_7", "Decoder6", "Mux64x6"]
  proofReference := "Shoumei.RISCV.Renaming.FreeListProofs"
}

/-- BitmapFreeList_64: Bitmap-based free list with correct flush recovery -/
def bitmapFreelist_cert : CompositionalCert := {
  moduleName := "BitmapFreeList_64"
  dependencies := ["Decoder6", "PriorityArbiter64", "OneHotEncoder64"]
  proofReference := "Shoumei.RISCV.Renaming.BitmapFreeListProofs"
}

/-! ## RISC-V Execution -/

/-- ReservationStation4: 4-entry Tomasulo reservation station -/
def rs4_cert : CompositionalCert := {
  moduleName := "ReservationStation4"
  dependencies := ["Register2", "Register91", "Comparator6", "Mux4x6", "Mux4x32", "Decoder2", "PriorityArbiter4"]
  proofReference := "Shoumei.RISCV.Execution.ReservationStationProofs"
}

/-! ## M-Extension -/

/-- PipelinedMultiplier: 3-stage pipelined array multiplier -/
def pipelinedMultiplier_cert : CompositionalCert := {
  moduleName := "PipelinedMultiplier"
  dependencies := ["CSACompressor64", "KoggeStoneAdder64", "Register32", "Subtractor32"]
  proofReference := "Shoumei.Circuits.Combinational.MultiplierProofs"
}

/-- Divider32: 32-cycle restoring divider -/
def divider32_cert : CompositionalCert := {
  moduleName := "Divider32"
  dependencies := ["Subtractor32"]
  proofReference := "Shoumei.Circuits.Sequential.DividerProofs"
}

/-- MulDivExecUnit: Combined multiply/divide execution unit -/
def muldivExecUnit_cert : CompositionalCert := {
  moduleName := "MulDivExecUnit"
  dependencies := ["PipelinedMultiplier", "Divider32"]
  proofReference := "Shoumei.RISCV.Execution.MulDivExecUnitProofs"
}

/-- MemoryRS4: Memory reservation station with store-load ordering -/
def memoryRS4_cert : CompositionalCert := {
  moduleName := "MemoryRS4"
  dependencies := ["Register2", "Register91", "Comparator6", "Mux4x6", "Mux4x32", "Decoder2", "PriorityArbiter4"]
  proofReference := "Shoumei.RISCV.Execution.ReservationStationProofs"
}

/-- MulDivRS4: Reservation station for MulDiv operations -/
def muldivRS4_cert : CompositionalCert := {
  moduleName := "MulDivRS4"
  dependencies := ["Register2", "Register91", "Comparator6", "Mux4x6", "Mux4x32", "Decoder2", "PriorityArbiter4"]
  proofReference := "Shoumei.RISCV.Execution.ReservationStationProofs"
}

/-! ## RISC-V Retirement -/

/-- Queue16x32: 16-entry × 32-bit register array for RVVI PC/instruction queues -/
def queue16x32_cert : CompositionalCert := {
  moduleName := "Queue16x32"
  dependencies := ["Register32", "Decoder4", "Mux16x32"]
  proofReference := "Shoumei.RISCV.Retirement.Queue16x32"
}

/-- ROB16: 16-entry reorder buffer for in-order commit -/
def rob16_cert : CompositionalCert := {
  moduleName := "ROB16"
  dependencies := ["Register24", "QueuePointer_4", "QueueCounterUpDown_5", "Decoder4", "Comparator6", "Mux16x6", "Mux16x5"]
  proofReference := "Shoumei.RISCV.Retirement.ROBProofs"
}

/-! ## RISC-V Memory -/

/-- StoreBuffer8: 8-entry store buffer with forwarding (FIFO redesign) -/
def storeBuffer8_cert : CompositionalCert := {
  moduleName := "StoreBuffer8"
  dependencies := ["Register66", "DFlipFlop", "QueuePointer_3", "QueuePointerLoadable_3", "QueueCounterLoadable_4", "Decoder3", "EqualityComparator32", "PriorityArbiter8", "Mux8x32", "Mux8x2", "Popcount8"]
  proofReference := "Shoumei.RISCV.Memory.StoreBufferProofs"
}

/-- LSU: Load-Store Unit (address generation + store buffering) -/
def lsu_cert : CompositionalCert := {
  moduleName := "LSU"
  dependencies := ["MemoryExecUnit", "StoreBuffer8"]
  proofReference := "Shoumei.RISCV.Memory.LSUProofs"
}

/-! ## Cache Hierarchy -/

/-- L1ICache: Direct-mapped L1 instruction cache -/
def l1iCache_cert : CompositionalCert := {
  moduleName := "L1ICache"
  dependencies := ["Register24", "EqualityComparator24", "Mux8x24", "Mux8x32"]
  proofReference := "Shoumei.RISCV.Memory.Cache.L1ICacheProofs"
}

/-- L1DCache: 2-way set-associative L1 data cache -/
def l1dCache_cert : CompositionalCert := {
  moduleName := "L1DCache"
  dependencies := ["Register25", "EqualityComparator25", "Mux4x25", "Mux8x32"]
  proofReference := "Shoumei.RISCV.Memory.Cache.L1DCacheProofs"
}

/-- L2Cache: 2-way set-associative shared L2 cache -/
def l2Cache_cert : CompositionalCert := {
  moduleName := "L2Cache"
  dependencies := ["Register24", "EqualityComparator24", "Mux8x24"]
  proofReference := "Shoumei.RISCV.Memory.Cache.L2CacheProofs"
}

/-- MemoryHierarchy: L1I + L1D + L2 composition -/
def memoryHierarchy_cert : CompositionalCert := {
  moduleName := "MemoryHierarchy"
  dependencies := ["L1ICache", "L1DCache", "L2Cache"]
  proofReference := "Shoumei.RISCV.Memory.Cache.MemoryHierarchyProofs"
}

/-- CachedCPU: CPU + MemoryHierarchy composition -/
def cachedCPU_cert : CompositionalCert := {
  moduleName := "CachedCPU_RV32IMF_Zicsr_Zifencei"
  dependencies := ["CPU_RV32IMF_Zicsr_Zifencei", "MemoryHierarchy"]
  proofReference := "Shoumei.RISCV.Memory.Cache.CachedCPUProofs"
}

/-! ## Decoders (LUT-based, no Chisel equivalent) -/

/-- RV32IMFDecoder: Pure LUT decoder — no Chisel equivalent exists.
    Verified by construction: the Lean DSL generates the truth table directly
    from the ISA spec, and the decoder proof shows it matches. -/
def rv32ifDecoder_cert : CompositionalCert := {
  moduleName := "RV32IFDecoder"
  dependencies := []
  proofReference := "Shoumei.RISCV.DecoderProofs"
}

def rv32imfDecoder_cert : CompositionalCert := {
  moduleName := "RV32IMFDecoder"
  dependencies := []
  proofReference := "Shoumei.RISCV.DecoderProofs"
}

/-! ## F-Extension -/

/-- FPAdder: IEEE 754 SP adder (sequential, pipeline DFFs cause induction failure) -/
def fpAdder_cert : CompositionalCert := {
  moduleName := "FPAdder"
  dependencies := []
  proofReference := "Shoumei.Circuits.Sequential.FPAdderProofs"
}

/-- FPMultiplier: IEEE 754 SP multiplier (sequential, pipeline DFFs cause induction failure) -/
def fpMultiplier_cert : CompositionalCert := {
  moduleName := "FPMultiplier"
  dependencies := []
  proofReference := "Shoumei.Circuits.Sequential.FPMultiplierProofs"
}

/-- FPFMA: Fused multiply-add (FPMultiplier + FPAdder) -/
def fpFMA_cert : CompositionalCert := {
  moduleName := "FPFMA"
  dependencies := ["FPMultiplier", "FPAdder"]
  proofReference := "Shoumei.Circuits.Sequential.FPFMAProofs"
}

/-- FPDivider: IEEE 754 SP divider (iterative, sequential) -/
def fpDivider_cert : CompositionalCert := {
  moduleName := "FPDivider"
  dependencies := []
  proofReference := "Shoumei.Circuits.Sequential.FPDividerProofs"
}

/-- FPSqrt: IEEE 754 SP square root (iterative, sequential) -/
def fpSqrt_cert : CompositionalCert := {
  moduleName := "FPSqrt"
  dependencies := []
  proofReference := "Shoumei.Circuits.Sequential.FPSqrtProofs"
}

/-- FPMisc: FP sign-inject, min/max, compare, classify, convert (combinational, JVM method size limit) -/
def fpMisc_cert : CompositionalCert := {
  moduleName := "FPMisc"
  dependencies := []
  proofReference := "Shoumei.Circuits.Combinational.FPMisc"
}

/-- FPExecUnit: Top-level FP execution unit (all FP sub-units) -/
def fpExecUnit_cert : CompositionalCert := {
  moduleName := "FPExecUnit"
  dependencies := ["FPMisc", "FPAdder", "FPMultiplier", "FPFMA", "FPDivider", "FPSqrt", "DFlipFlop"]
  proofReference := "Shoumei.RISCV.Execution.FPExecUnitProofs"
}

/-- CPU_RV32IMF: RV32IMF with F extension -/
def cpu_rv32imf_cert : CompositionalCert := {
  moduleName := "CPU_RV32IMF"
  dependencies := [
    "FPExecUnit", "FPMisc", "FPAdder", "FPMultiplier", "FPFMA", "FPDivider", "FPSqrt",
    "MulDivRS4", "MulDivExecUnit", "PipelinedMultiplier", "Divider32"
  ]
  proofReference := "Shoumei.RISCV.CPUProofs"
}

/-- CPU_RV32IF: RV32IF (F extension without M) -/
def cpu_rv32if_cert : CompositionalCert := {
  moduleName := "CPU_RV32IF"
  dependencies := [
    "FPExecUnit", "FPMisc", "FPAdder", "FPMultiplier", "FPFMA", "FPDivider", "FPSqrt"
  ]
  proofReference := "Shoumei.RISCV.CPUProofs"
}

/-! ## Phase 8: Top-Level Integration -/

/-- RenameStage_32x64: Composite rename stage (RAT + FreeList + PhysRegFile) -/
def renameStage_cert : CompositionalCert := {
  moduleName := "RenameStage_32x64"
  dependencies := ["RAT_32x6", "BitmapFreeList_64", "PhysRegFile_64x32"]
  proofReference := "Shoumei.RISCV.Renaming.RenameStageProofs"
}

/-- FetchStage: PC management and instruction fetch -/
def fetchStage_cert : CompositionalCert := {
  moduleName := "FetchStage"
  dependencies := ["Register32", "KoggeStoneAdder32"]
  proofReference := "Shoumei.RISCV.FetchProofs"
}

/-- CPU_RV32I: Complete RV32I Tomasulo processor (simplified MVP) -/
def cpu_rv32i_cert : CompositionalCert := {
  moduleName := "CPU_RV32I"
  dependencies := [
    "FetchStage",
    "RenameStage_32x64",
    -- Transitive dependencies through RenameStage:
    "RAT_32x6", "FreeList_64", "PhysRegFile_64x32",
    -- Transitive dependencies through Fetch:
    "Register32", "KoggeStoneAdder32",
    -- Additional dependencies (for full implementation):
    "ReservationStation4", "MemoryRS4", "IntegerExecUnit", "MemoryExecUnit",
    "ROB16", "LSU", "StoreBuffer8"
  ]
  proofReference := "Shoumei.RISCV.CPUProofs"
}

/-- CPU_RV32IM: RV32IM with multiply/divide extension (simplified MVP) -/
def cpu_rv32im_cert : CompositionalCert := {
  moduleName := "CPU_RV32IM"
  dependencies := [
    -- All CPU_RV32I dependencies, plus:
    "MulDivRS4", "MulDivExecUnit",
    "PipelinedMultiplier", "Divider32"
  ]
  proofReference := "Shoumei.RISCV.CPUProofs"
}

/-- CPU_RV32IM_Zifencei: RV32IM with Zifencei (FENCE.I drain FSM) -/
def cpu_rv32im_zifencei_cert : CompositionalCert := {
  moduleName := "CPU_RV32IM_Zifencei"
  dependencies := [
    "MulDivRS4", "MulDivExecUnit",
    "PipelinedMultiplier", "Divider32"
  ]
  proofReference := "Shoumei.RISCV.CPUProofs"
}

/-- CPU_RV32IMF_Zifencei: RV32IMF with Zifencei (FENCE.I drain FSM) -/
def cpu_rv32imf_zifencei_cert : CompositionalCert := {
  moduleName := "CPU_RV32IMF_Zifencei"
  dependencies := [
    "FPExecUnit", "FPMisc", "FPAdder", "FPMultiplier", "FPFMA", "FPDivider", "FPSqrt",
    "MulDivRS4", "MulDivExecUnit", "PipelinedMultiplier", "Divider32"
  ]
  proofReference := "Shoumei.RISCV.CPUProofs"
}

/-- MicrocodeSequencer: ROM-driven µop sequencer for CSR/FENCE.I -/
def microcodeSequencer_cert : CompositionalCert := {
  moduleName := "MicrocodeSequencer"
  dependencies := ["MicrocodeDecoder", "Register6", "Register32", "Register16"]
  proofReference := "Shoumei.RISCV.Microcode.MicrocodeSequencerProofs"
}

/-- CPU_RV32IM_Zicsr_Zifencei: RV32IM with Zicsr (CSR instructions) + Zifencei -/
def cpu_rv32im_zicsr_zifencei_cert : CompositionalCert := {
  moduleName := "CPU_RV32IM_Zicsr_Zifencei"
  dependencies := [
    "MulDivRS4", "MulDivExecUnit",
    "PipelinedMultiplier", "Divider32"
  ]
  proofReference := "Shoumei.RISCV.CPUProofs"
}

/-- CPU_RV32IF_Zicsr_Zifencei: RV32IF with Zicsr (CSR instructions) + Zifencei -/
def cpu_rv32if_zicsr_zifencei_cert : CompositionalCert := {
  moduleName := "CPU_RV32IF_Zicsr_Zifencei"
  dependencies := [
    "FPExecUnit", "FPMisc", "FPAdder", "FPMultiplier", "FPFMA", "FPDivider", "FPSqrt"
  ]
  proofReference := "Shoumei.RISCV.CPUProofs"
}

/-- CPU_RV32IMF_Zicsr_Zifencei: RV32IMF with Zicsr (CSR instructions) + Zifencei -/
def cpu_rv32imf_zicsr_zifencei_cert : CompositionalCert := {
  moduleName := "CPU_RV32IMF_Zicsr_Zifencei"
  dependencies := [
    "FPExecUnit", "FPMisc", "FPAdder", "FPMultiplier", "FPFMA", "FPDivider", "FPSqrt",
    "MulDivRS4", "MulDivExecUnit", "PipelinedMultiplier", "Divider32"
  ]
  proofReference := "Shoumei.RISCV.CPUProofs"
}

/-- CPU_RV32IMF_Zicsr_Zifencei_Microcoded: Microcoded variant with ROM-driven µop sequencer -/
def cpu_rv32imf_zicsr_zifencei_microcoded_cert : CompositionalCert := {
  moduleName := "CPU_RV32IMF_Zicsr_Zifencei_Microcoded"
  dependencies := [
    "FPExecUnit", "FPMisc", "FPAdder", "FPMultiplier", "FPFMA", "FPDivider", "FPSqrt",
    "MulDivRS4", "MulDivExecUnit", "PipelinedMultiplier", "Divider32",
    "MicrocodeSequencer"
  ]
  proofReference := "Shoumei.RISCV.CPUProofs"
}

/-! ## Export All -/

def allCerts : List CompositionalCert := [
  -- Sequential
  register24_cert,
  register66_cert,
  register68_cert,
  register91_cert,
  queue2_8_cert,
  queue64_32_cert,
  queue64_6_cert,
  queue4_8_cert,
  queueRAM_64x32_cert,
  queueRAM_64x6_cert,
  queueRAM_2x8_cert,
  queueRAM_4x8_cert,
  queueRAMInit_64x6_cert,
  queue64_6_flushable_cert,
  freeListFlushable_cert,
  queueCounterUpDown_2_cert,
  queueCounterUpDown_3_cert,
  queueCounterUpDown_4_cert,
  queueCounterUpDown_5_cert,
  queueCounterUpDown_7_cert,
  queuePointer_1_cert,
  queuePointer_2_cert,
  queuePointer_3_cert,
  queuePointer_4_cert,
  queuePointer_6_cert,
  -- Renaming
  physregfile_cert,
  rat_cert,
  freelist_cert,
  bitmapFreelist_cert,
  -- Execution
  rs4_cert,
  memoryRS4_cert,
  -- M-Extension
  pipelinedMultiplier_cert,
  divider32_cert,
  muldivExecUnit_cert,
  muldivRS4_cert,
  -- Retirement
  queue16x32_cert,
  rob16_cert,
  -- Memory
  storeBuffer8_cert,
  lsu_cert,
  -- Cache Hierarchy
  l1iCache_cert,
  l1dCache_cert,
  l2Cache_cert,
  memoryHierarchy_cert,
  cachedCPU_cert,
  -- Decoders
  rv32ifDecoder_cert,
  rv32imfDecoder_cert,
  -- F-Extension
  fpMisc_cert,
  fpAdder_cert,
  fpMultiplier_cert,
  fpFMA_cert,
  fpDivider_cert,
  fpSqrt_cert,
  fpExecUnit_cert,
  cpu_rv32imf_cert,
  cpu_rv32if_cert,
  -- Phase 8: Top-Level Integration
  renameStage_cert,
  fetchStage_cert,
  cpu_rv32i_cert,
  cpu_rv32im_cert,
  -- Zifencei variants
  cpu_rv32im_zifencei_cert,
  cpu_rv32imf_zifencei_cert,
  -- Microcode
  microcodeSequencer_cert,
  -- Zicsr + Zifencei variants
  cpu_rv32im_zicsr_zifencei_cert,
  cpu_rv32if_zicsr_zifencei_cert,
  cpu_rv32imf_zicsr_zifencei_cert,
  -- Microcoded variant
  cpu_rv32imf_zicsr_zifencei_microcoded_cert
]

end Shoumei.Verification.CompositionalCerts
