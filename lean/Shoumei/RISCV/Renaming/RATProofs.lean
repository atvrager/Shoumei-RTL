/-
RISCV/Renaming/RATProofs.lean - Proofs for Register Alias Table

Structural proofs:
- Gate counts
- Port counts
- Circuit structure properties

Behavioral proofs:
- Lookup after allocate returns allocated value
- Lookup of unmodified register returns original value
- Init creates identity mapping
- x0 special case handling
-/

import Shoumei.RISCV.Renaming.RAT

namespace Shoumei.RISCV.Renaming.RATProofs

open Shoumei
open Shoumei.RISCV.Renaming

/-! ## Structural Proofs -/

/-- RAT64 has the expected name -/
theorem rat64_name : mkRAT64.name = "RAT_32x6" := by native_decide

/-- RAT64 has correct number of inputs:
    clock(1) + reset(1) + write_en(1) + write_addr(5) + write_data(6)
    + rs1_addr(5) + rs2_addr(5) = 24 -/
theorem rat64_input_count : mkRAT64.inputs.length = 24 := by native_decide

/-- RAT64 has correct number of outputs:
    rs1_data(6) + rs2_data(6) = 12 -/
theorem rat64_output_count : mkRAT64.outputs.length = 12 := by native_decide

/-- RAT64 uses 3 submodule instances (1 decoder + 2 muxes) -/
theorem rat64_instance_count : mkRAT64.instances.length = 3 := by native_decide

/-- RAT64 gate count: 32 write-enable ANDs + 32*6*2 storage gates (MUX + DFF) = 32 + 384 = 416 -/
theorem rat64_gate_count : mkRAT64.gates.length = 416 := by native_decide

/-! ## Behavioral Proofs -/

/-- Initial RAT maps register 0 to physical register 0 -/
theorem rat64_init_reg0 :
    (RATState.init (n := 64) (by omega)).lookup ⟨0, by omega⟩ = ⟨0, by omega⟩ := by
  simp [RATState.init, RATState.lookup]

/-- Initial RAT maps register 5 to physical register 5 -/
theorem rat64_init_reg5 :
    (RATState.init (n := 64) (by omega)).lookup ⟨5, by omega⟩ = ⟨5, by omega⟩ := by
  simp [RATState.init, RATState.lookup]; rfl

/-- Initial RAT maps register 31 to physical register 31 -/
theorem rat64_init_reg31 :
    (RATState.init (n := 64) (by omega)).lookup ⟨31, by omega⟩ = ⟨31, by omega⟩ := by
  simp [RATState.init, RATState.lookup]; rfl

/-- Allocate then lookup returns the allocated physical register -/
theorem rat_allocate_lookup (rat : RATState 64)
    (archReg : Fin 32) (physReg : Fin 64) :
    (rat.allocate archReg physReg).lookup archReg = physReg := by
  simp [RATState.allocate, RATState.lookup]

/-- Allocating to one register doesn't affect another -/
theorem rat_allocate_other (rat : RATState 64)
    (r1 r2 : Fin 32) (physReg : Fin 64) (h : r1 ≠ r2) :
    (rat.allocate r1 physReg).lookup r2 = rat.lookup r2 := by
  unfold RATState.allocate RATState.lookup
  simp
  intro h_eq
  simp [h_eq] at h

/-- Identity mapping is an identity function -/
theorem rat_init_is_identity :
    ∀ (r : Fin 32), ((RATState.init (n := 64) (by omega)).lookup r).val = r.val := by
  intro r
  simp [RATState.init, RATState.lookup]

/-- Pair lookup returns correct values for both registers -/
theorem rat_lookupPair_correct (rat : RATState 64) (rs1 rs2 : Fin 32) :
    rat.lookupPair rs1 rs2 = (rat.lookup rs1, rat.lookup rs2) := by
  simp [RATState.lookupPair]

/-- Sequential allocations: last write wins -/
theorem rat_last_write_wins (rat : RATState 64)
    (archReg : Fin 32) (p1 p2 : Fin 64) :
    ((rat.allocate archReg p1).allocate archReg p2).lookup archReg = p2 := by
  simp [RATState.allocate, RATState.lookup]

/-- Allocating different registers: both visible -/
theorem rat_independent_allocations (rat : RATState 64)
    (r1 r2 : Fin 32) (p1 p2 : Fin 64) (h : r1 ≠ r2) :
    let rat' := (rat.allocate r1 p1).allocate r2 p2
    rat'.lookup r1 = p1 ∧ rat'.lookup r2 = p2 := by
  constructor
  · unfold RATState.allocate RATState.lookup
    simp
    intro h_eq
    simp [h_eq] at h
  · simp [RATState.allocate, RATState.lookup]

end Shoumei.RISCV.Renaming.RATProofs
