/-
RISCV/Renaming/PhysRegFileProofs.lean - Proofs for Physical Register File

Structural proofs:
- Gate counts, port counts, circuit structure properties

Behavioral proofs:
- Read-after-write correctness
- Write independence (write to one tag doesn't affect others)
- Initialization to all zeros
- Last-write-wins semantics
- Dual-read consistency
-/

import Shoumei.RISCV.Renaming.PhysRegFile

namespace Shoumei.RISCV.Renaming.PhysRegFileProofs

open Shoumei
open Shoumei.RISCV.Renaming

/-! ## Structural Proofs (64×32 configuration) -/

/-- PhysRegFile64 has the expected name -/
theorem physregfile64_name : mkPhysRegFile64.name = "PhysRegFile_64x32" := by native_decide

/-- PhysRegFile64 has correct number of inputs:
    clock(1) + reset(1) + wr_en(1) + rd_tag1(6) + rd_tag2(6) + wr_tag(6) + wr_data(32) = 53 -/
theorem physregfile64_input_count : mkPhysRegFile64.inputs.length = 53 := by native_decide

/-- PhysRegFile64 has correct number of outputs:
    rd_data1(32) + rd_data2(32) = 64 -/
theorem physregfile64_output_count : mkPhysRegFile64.outputs.length = 64 := by native_decide

/-- PhysRegFile64 uses 3 submodule instances (1 decoder + 2 muxes) -/
theorem physregfile64_instance_count : mkPhysRegFile64.instances.length = 3 := by native_decide

/-- PhysRegFile64 gate count: 64 write-enable ANDs + 64×32×2 storage gates (MUX + DFF) = 4160 -/
theorem physregfile64_gate_count : mkPhysRegFile64.gates.length = 4160 := by native_decide

/-! ## Structural Proofs (4×8 test configuration) -/

/-- Small PRF for testing has expected name -/
theorem physregfile4x8_name : mkPhysRegFile4x8.name = "PhysRegFile_4x8" := by native_decide

/-- Small PRF: clock(1) + reset(1) + wr_en(1) + rd_tag1(2) + rd_tag2(2) + wr_tag(2) + wr_data(8) = 17 -/
theorem physregfile4x8_input_count : mkPhysRegFile4x8.inputs.length = 17 := by native_decide

/-- Small PRF: rd_data1(8) + rd_data2(8) = 16 -/
theorem physregfile4x8_output_count : mkPhysRegFile4x8.outputs.length = 16 := by native_decide

/-- Small PRF: 4 AND + 4×8×2 = 68 gates -/
theorem physregfile4x8_gate_count : mkPhysRegFile4x8.gates.length = 68 := by native_decide

/-! ## Behavioral Proofs -/

/-- All registers are zero after initialization -/
theorem physregfile_init_all_zero (tag : Fin 64) :
    (PhysRegFileState.init 64).read tag = 0 := by
  simp [PhysRegFileState.init, PhysRegFileState.read]

/-- Read-after-write: writing then reading the same tag returns the written value -/
theorem physregfile_read_after_write (prf : PhysRegFileState 64)
    (tag : Fin 64) (val : UInt32) :
    (prf.write tag val).read tag = val := by
  simp [PhysRegFileState.write, PhysRegFileState.read]

/-- Write independence: writing to one tag doesn't affect reads of a different tag -/
theorem physregfile_write_independence (prf : PhysRegFileState 64)
    (tag1 tag2 : Fin 64) (val : UInt32) (h : tag1 ≠ tag2) :
    (prf.write tag1 val).read tag2 = prf.read tag2 := by
  unfold PhysRegFileState.write PhysRegFileState.read
  simp
  intro h_eq
  simp [h_eq] at h

/-- Last-write-wins: sequential writes to the same tag, last value is visible -/
theorem physregfile_last_write_wins (prf : PhysRegFileState 64)
    (tag : Fin 64) (v1 v2 : UInt32) :
    ((prf.write tag v1).write tag v2).read tag = v2 := by
  simp [PhysRegFileState.write, PhysRegFileState.read]

/-- Independent writes: writing to different tags, both values visible -/
theorem physregfile_independent_writes (prf : PhysRegFileState 64)
    (t1 t2 : Fin 64) (v1 v2 : UInt32) (h : t1 ≠ t2) :
    let prf' := (prf.write t1 v1).write t2 v2
    prf'.read t1 = v1 ∧ prf'.read t2 = v2 := by
  constructor
  · unfold PhysRegFileState.write PhysRegFileState.read
    simp
    intro h_eq
    simp [h_eq] at h
  · simp [PhysRegFileState.write, PhysRegFileState.read]

/-- Dual read returns correct pair -/
theorem physregfile_readPair_correct (prf : PhysRegFileState 64) (t1 t2 : Fin 64) :
    prf.readPair t1 t2 = (prf.read t1, prf.read t2) := by
  simp [PhysRegFileState.readPair]

/-! ## Concrete Behavioral Proofs (native_decide on small config) -/

private def mkPRF4Init : PhysRegFileState 4 := PhysRegFileState.init 4

/-- After init, register 0 reads as 0 -/
theorem prf4_init_reg0 :
    mkPRF4Init.read ⟨0, by omega⟩ = 0 := by native_decide

/-- Write 42 to reg 1, read it back -/
theorem prf4_write_read :
    (mkPRF4Init.write ⟨1, by omega⟩ 42).read ⟨1, by omega⟩ = 42 := by native_decide

/-- Write to reg 1 doesn't change reg 0 -/
theorem prf4_write_independence :
    (mkPRF4Init.write ⟨1, by omega⟩ 42).read ⟨0, by omega⟩ = 0 := by native_decide

/-- Multiple writes: reg 0 = 10, reg 2 = 20, both visible -/
theorem prf4_multi_write :
    let prf1 := mkPRF4Init.write ⟨0, by omega⟩ 10
    let prf2 := prf1.write ⟨2, by omega⟩ 20
    prf2.read ⟨0, by omega⟩ = 10 ∧ prf2.read ⟨2, by omega⟩ = 20 := by native_decide

/-- Last write wins: write 10 then 20 to same reg -/
theorem prf4_last_write_wins :
    let prf1 := mkPRF4Init.write ⟨3, by omega⟩ 10
    let prf2 := prf1.write ⟨3, by omega⟩ 20
    prf2.read ⟨3, by omega⟩ = 20 := by native_decide

/-- Dual read after writes: read both ports -/
theorem prf4_dual_read :
    let prf1 := mkPRF4Init.write ⟨1, by omega⟩ 100
    let prf2 := prf1.write ⟨3, by omega⟩ 200
    prf2.readPair ⟨1, by omega⟩ ⟨3, by omega⟩ = (100, 200) := by native_decide

end Shoumei.RISCV.Renaming.PhysRegFileProofs
