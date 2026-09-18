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
    + rs1_addr(5) + rs2_addr(5) + rs3_addr(5) + restore_data(192)
    = 3 + 5 + 6 + 15 + 192 = 221 -/
theorem rat64_input_count : mkRAT64.inputs.length = 221 := by native_decide

/-- RAT64 has correct number of outputs:
    rs1_data(6) + rs2_data(6) + rs3_data(6) + old_rd_data(6) + dump_data(192)
    = 24 + 192 = 216 -/
theorem rat64_output_count : mkRAT64.outputs.length = 216 := by native_decide

/-- RAT64 uses 5 submodule instances (1 write decoder + 4 read muxes) -/
theorem rat64_instance_count : mkRAT64.instances.length = 5 := by native_decide

/-- RAT64 gate count: 32 write-enable ANDs + 20 reset buffers (4 root + 16 leaf)
    + 32*6*3 storage gates (write MUX, DFF, dump BUF)
    = 32 + 20 + 576 = 628 -/
theorem rat64_gate_count : mkRAT64.gates.length = 628 := by native_decide

/-- IntRAT64 has the expected name -/
theorem intrat64_name : mkIntRAT64.name = "IntRAT_32x6" := by native_decide

/-- IntRAT64 input count (221 - 5 rs3_addr wires = 216) -/
theorem intrat64_input_count : mkIntRAT64.inputs.length = 216 := by native_decide

/-- IntRAT64 output count (216 - 6 rs3_data wires = 210) -/
theorem intrat64_output_count : mkIntRAT64.outputs.length = 210 := by native_decide

/-- IntRAT64 uses 4 submodule instances (1 write dec + 3 read muxes: rs1, rs2, old_rd) -/
theorem intrat64_instance_count : mkIntRAT64.instances.length = 4 := by native_decide

/-- IntRAT64 gate count (same storage array = 628) -/
theorem intrat64_gate_count : mkIntRAT64.gates.length = 628 := by native_decide

/-- CRAT64 has the expected name -/
theorem crat64_name : mkCRAT64.name = "CRAT_32x6" := by native_decide

/-- CRAT64 has correct number of inputs: clock(1) + reset(1) + restore_data(192) = 194 -/
theorem crat64_input_count : mkCRAT64.inputs.length = 194 := by native_decide

/-- CRAT64 has correct number of outputs: dump_data(192) = 192 -/
theorem crat64_output_count : mkCRAT64.outputs.length = 192 := by native_decide

/-- CRAT64 is purely storage without submodules -/
theorem crat64_instance_count : mkCRAT64.instances.length = 0 := by native_decide

/-- CRAT64 gate count: 20 reset buffers + 192 DFFs = 212 -/
theorem crat64_gate_count : mkCRAT64.gates.length = 212 := by native_decide

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
