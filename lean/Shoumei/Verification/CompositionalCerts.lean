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

/-! ## M-Extension -/

/-- PipelinedMultiplier: 3-stage pipelined array multiplier -/
def pipelinedMultiplier_cert : CompositionalCert := {
  moduleName := "PipelinedMultiplier"
  proofReference := "Shoumei.Circuits.Combinational.MultiplierProofs"
}

/-- Divider32: 32-cycle restoring divider -/
def divider32_cert : CompositionalCert := {
  moduleName := "Divider32"
  proofReference := "Shoumei.Circuits.Sequential.DividerProofs"
}

/-- MulDivExecUnit: Combined multiply/divide execution unit -/
def muldivExecUnit_cert : CompositionalCert := {
  moduleName := "MulDivExecUnit"
  proofReference := "Shoumei.RISCV.Execution.MulDivExecUnitProofs"
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

/-- CachedCPU (Microcoded): Microcoded CPU + MemoryHierarchy composition.
    Both the name and its dependency come from the config, so the rename that
    turns on the A extension moves this certificate with them. -/
def cachedCPU_microcoded_cert : CompositionalCert := {
  moduleName := Shoumei.RISCV.defaultCPUConfig.fullName
  proofReference := "Shoumei.RISCV.Memory.Cache.CachedCPUProofs"
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

/-- FPFMA: Fused multiply-add (FPMultiplier + FPAdder) -/
def fpFMA_cert : CompositionalCert := {
  moduleName := "FPFMA"
  proofReference := "Shoumei.Circuits.Sequential.FPFMAProofs"
}

/-- FPDivider: IEEE 754 SP divider (iterative, sequential) -/
def fpDivider_cert : CompositionalCert := {
  moduleName := "FPDivider"
  proofReference := "Shoumei.Circuits.Sequential.FPDividerProofs"
}

/-- FPSqrt: IEEE 754 SP square root (iterative, sequential) -/
def fpSqrt_cert : CompositionalCert := {
  moduleName := "FPSqrt"
  proofReference := "Shoumei.Circuits.Sequential.FPSqrtProofs"
}

/-- FPMisc: FP sign-inject, min/max, compare, classify, convert (combinational, JVM method size limit) -/
def fpMisc_cert : CompositionalCert := {
  moduleName := "FPMisc"
  proofReference := "Shoumei.Circuits.Combinational.FPMisc"
}

/-- FPExecUnit: Top-level FP execution unit (all FP sub-units) -/
def fpExecUnit_cert : CompositionalCert := {
  moduleName := "FPExecUnit"
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
/-- MicrocodeSequencer: ROM-driven µop sequencer for CSR/FENCE.I -/
def microcodeSequencer_cert : CompositionalCert := {
  moduleName := "MicrocodeSequencer"
  proofReference := "Shoumei.RISCV.Microcode.MicrocodeSequencerProofs"
}

/-- W=2 dual-issue microcoded CPU.  The module name is the config's, so enabling
    or renaming an extension renames the certificate with the circuit. -/
def cpu_microcoded_cert : CompositionalCert := {
  moduleName := s!"CPU_{Shoumei.RISCV.defaultCPUConfig.isaString}"
  proofReference := "Shoumei.RISCV.CPUProofs"
}

/-! ## Export All -/

def allCerts : List CompositionalCert := [
  -- Combinational (hierarchical muxes)
  mux64x32_cert,
  mux64x64_cert,
  mux64x6_cert,
  mux8x32_cert,
  mux8x64_cert,
  -- Sequential
  register24_cert,
  register66_cert,
  register68_cert,
  register91_cert,
  register256_cert,
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
  physregfile_64x64_cert,
  rat_cert,
  freelist_cert,
  bitmapFreelist_w2_cert,
  -- Execution
  -- M-Extension
  pipelinedMultiplier_cert,
  divider32_cert,
  muldivExecUnit_cert,
  -- Retirement
  queue16x32_dualport_cert,
  queue16x32_cert,
  rob16_w2_cert,
  -- Memory
  storeBuffer8_cert,
  lsu_cert,
  -- Cache Hierarchy
  l1iCache_cert,
  l1dCache_cert,
  l2Cache_cert,
  memoryHierarchy_cert,
  -- Decoders
  rv32ifDecoder_cert,
  rv32imfDecoder_cert,
  rv32gDecoder_cert,
  -- F-Extension
  fpMisc_cert,
  fpAdder_cert,
  fpMultiplier_cert,
  fpFMA_cert,
  fpDivider_cert,
  fpSqrt_cert,
  fpExecUnit_cert,
  -- Phase 8: Top-Level Integration
  renameStage_w2_cert,
  renameStage_w2_64_cert,
  -- Zifencei variants
  -- Microcode
  microcodeSequencer_cert,
  -- Zicsr + Zifencei variants
  -- Microcoded variant
  cpu_microcoded_cert,
  -- Microcoded cached variant
  cachedCPU_microcoded_cert
]

end Shoumei.Verification.CompositionalCerts
