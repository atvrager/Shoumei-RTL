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

/-- Queue4_8: 4-entry queue with 8-bit data (structural differences prevent direct LEC) -/
def queue4_8_cert : CompositionalCert := {
  moduleName := "Queue4_8"
  dependencies := ["QueueRAM_4x8", "QueuePointer_2", "QueueCounterUpDown_3"]
  proofReference := "Shoumei.Circuits.Sequential.QueueProofs"
}

/-- Register24 = Register16 + Register8 (hierarchical) -/
def register24_cert : CompositionalCert := {
  moduleName := "Register24"
  dependencies := ["Register16", "Register8"]
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

/-! ## RISC-V Execution -/

/-- ReservationStation4: 4-entry Tomasulo reservation station -/
def rs4_cert : CompositionalCert := {
  moduleName := "ReservationStation4"
  dependencies := ["Register2", "Register91", "Comparator6", "Mux4x6", "Mux4x32", "Decoder2", "PriorityArbiter4"]
  proofReference := "Shoumei.RISCV.Execution.ReservationStationProofs"
}

/-! ## RISC-V Retirement -/

/-- ROB16: 16-entry reorder buffer for in-order commit -/
def rob16_cert : CompositionalCert := {
  moduleName := "ROB16"
  dependencies := ["Register24", "QueuePointer_4", "QueueCounterUpDown_5", "Decoder4", "Comparator6", "Mux16x6", "Mux16x5"]
  proofReference := "Shoumei.RISCV.Retirement.ROBProofs"
}

/-! ## Export All -/

def allCerts : List CompositionalCert := [
  -- Sequential
  register24_cert,
  register91_cert,
  queue64_32_cert,
  queue64_6_cert,
  queue4_8_cert,
  queueRAM_64x32_cert,
  queueRAM_64x6_cert,
  queueRAM_2x8_cert,
  queueRAM_4x8_cert,
  -- Renaming
  physregfile_cert,
  rat_cert,
  freelist_cert,
  -- Execution
  rs4_cert,
  -- Retirement
  rob16_cert
]

end Shoumei.Verification.CompositionalCerts
