/-
RISCV/Renaming/RenameStageProofs.lean - Proofs for RenameStage

Structural proofs:
- Gate counts, port counts, instance counts, circuit structure properties

Behavioral proofs:
- Initialization correctness
- Single rename operations (simple, x0, no-dest, stall, freelist decrement)
- Dependent sequences (RAT forwarding, triple rename, old phys captured)
- PhysRegFile operations (writeback, retire, read operands)
- Generic properties (rename preserves PRF, read independence)
-/

import Shoumei.RISCV.Renaming.RenameStage

set_option maxRecDepth 8000

namespace Shoumei.RISCV.Renaming.RenameStageProofs

open Shoumei
open Shoumei.RISCV
open Shoumei.RISCV.Renaming

/-! ## Structural Proofs -/

/-- RenameStage has the expected name -/
theorem renamestage_name : mkRenameStage.name = "RenameStage_W2" := by native_decide

/-- RenameStage input count -/
theorem renamestage_input_count : mkRenameStage.inputs.length = 177 := by native_decide

/-- RenameStage output count -/
theorem renamestage_output_count : mkRenameStage.outputs.length = 256 := by native_decide

/-- RenameStage uses 6 submodule instances -/
theorem renamestage_instance_count : mkRenameStage.instances.length = 6 := by native_decide

/-- RenameStage gate count -/
theorem renamestage_gate_count : mkRenameStage.gates.length = 166 := by native_decide

/-! ## Behavioral Proofs - Initialization -/

/-- Initial RAT has identity mapping -/
theorem renamestage_init_rat_identity :
    ∀ r : Fin 32, (RenameStageState.init.rat.lookup r).val = r.val := by
  intro r
  simp [RenameStageState.init, RATState.init, RATState.lookup]

/-- Initial FreeList has 32 available registers (32-63) -/
theorem renamestage_init_freelist_count :
    RenameStageState.init.freeList.count = 32 := by native_decide

/-! ## Behavioral Proofs - Single Rename Operations -/

/-- Simple instruction: ADD x5, x1, x2 allocates phys reg 32 and decrements freelist -/
theorem renamestage_simple_rename :
    let instr := { opType := .ADD, rd := some ⟨5, by omega⟩, rs1 := some ⟨1, by omega⟩,
                   rs2 := some ⟨2, by omega⟩, imm := none, pc := 0 : DecodedInstruction }
    let (state', result) := renameInstruction RenameStageState.init instr
    result.isSome ∧
    result.get!.physRd = some ⟨32, by omega⟩ ∧
    state'.freeList.count = 31 := by native_decide

/-- x0 special case: ADD x0, x1, x2 (x0 is never allocated) -/
theorem renamestage_x0_no_alloc :
    let instr := { opType := .ADD, rd := some ⟨0, by omega⟩, rs1 := some ⟨1, by omega⟩,
                   rs2 := some ⟨2, by omega⟩, imm := none, pc := 0 }
    let (state', result) := renameInstruction RenameStageState.init instr
    result.isSome ∧
    result.get!.physRd = none ∧                              -- No physical register allocated
    state'.freeList.count = RenameStageState.init.freeList.count ∧  -- FreeList unchanged
    state'.rat.lookup ⟨0, by omega⟩ = ⟨0, by omega⟩ := by native_decide         -- RAT[0] still maps to 0

/-- No-destination instruction: SW (stores don't write to registers) -/
theorem renamestage_no_dest :
    let instr := { opType := .SW, rd := none, rs1 := some ⟨1, by omega⟩,
                   rs2 := some ⟨2, by omega⟩, imm := some 16, pc := 0 }
    let (state', result) := renameInstruction RenameStageState.init instr
    result.isSome ∧
    result.get!.physRd = none ∧
    state'.freeList.count = RenameStageState.init.freeList.count := by native_decide  -- No allocation

/-- After exhausting all 32 free regs, next rename returns None (stall) -/
theorem renamestage_stall_on_empty :
    let exhaust := (List.range 32).foldl (fun st i =>
      let instr : DecodedInstruction := { opType := .ADD, rd := some ⟨(i % 31) + 1, by omega⟩, rs1 := some ⟨1, by omega⟩, rs2 := some ⟨2, by omega⟩, imm := none, pc := 0 }
      (renameInstruction st instr).1) RenameStageState.init
    let instr : DecodedInstruction := { opType := .ADD, rd := some ⟨1, by omega⟩, rs1 := some ⟨1, by omega⟩, rs2 := some ⟨2, by omega⟩, imm := none, pc := 0 }
    (renameInstruction exhaust instr).2.isNone := by native_decide

/-- After one rename, freelist.count = 31 -/
theorem renamestage_freelist_decrement :
    let instr := { opType := .ADD, rd := some ⟨5, by omega⟩, rs1 := some ⟨1, by omega⟩,
                   rs2 := some ⟨2, by omega⟩, imm := none, pc := 0 : DecodedInstruction }
    (renameInstruction RenameStageState.init instr).1.freeList.count = 31 := by native_decide

/-! ## Behavioral Proofs - Dependent Sequences -/

/-- After renaming x5, RAT lookup for x5 returns the new phys reg 32 -/
theorem renamestage_rat_forwarding :
    let instr := { opType := .ADD, rd := some ⟨5, by omega⟩, rs1 := some ⟨1, by omega⟩,
                   rs2 := some ⟨2, by omega⟩, imm := none, pc := 0 : DecodedInstruction }
    let state' := (renameInstruction RenameStageState.init instr).1
    state'.rat.lookup ⟨5, by omega⟩ = ⟨32, by omega⟩ := by native_decide

/-- Three sequential renames all succeed with consecutive phys regs 32, 33, 34 -/
theorem renamestage_triple_rename :
    let i1 : DecodedInstruction := { opType := .ADD, rd := some ⟨5, by omega⟩, rs1 := some ⟨1, by omega⟩, rs2 := some ⟨2, by omega⟩, imm := none, pc := 0 }
    let i2 : DecodedInstruction := { opType := .ADD, rd := some ⟨6, by omega⟩, rs1 := some ⟨3, by omega⟩, rs2 := some ⟨4, by omega⟩, imm := none, pc := 4 }
    let i3 : DecodedInstruction := { opType := .ADD, rd := some ⟨7, by omega⟩, rs1 := some ⟨5, by omega⟩, rs2 := some ⟨6, by omega⟩, imm := none, pc := 8 }
    let (s1, r1) := renameInstruction RenameStageState.init i1
    let (s2, r2) := renameInstruction s1 i2
    let (_, r3) := renameInstruction s2 i3
    r1.isSome ∧ r2.isSome ∧ r3.isSome ∧
    r1.get!.physRd = some ⟨32, by omega⟩ ∧
    r2.get!.physRd = some ⟨33, by omega⟩ ∧
    r3.get!.physRd = some ⟨34, by omega⟩ := by native_decide

/-- Rename captures the old mapping (arch reg 5 → phys reg 5) before update -/
theorem renamestage_old_phys_captured :
    let instr := { opType := .ADD, rd := some ⟨5, by omega⟩, rs1 := some ⟨1, by omega⟩,
                   rs2 := some ⟨2, by omega⟩, imm := none, pc := 0 : DecodedInstruction }
    let result := (renameInstruction RenameStageState.init instr).2
    result.get!.oldPhysRd = some ⟨5, by omega⟩ := by native_decide

/-! ## Behavioral Proofs - PhysRegFile Operations -/

/-- WriteBack updates physical register -/
theorem renamestage_writeback :
    let state := RenameStageState.init
    let state' := writeBack state ⟨32, by omega⟩ 42
    state'.physRegFile.read ⟨32, by omega⟩ = 42 := by
  simp [writeBack, PhysRegFileState.write, PhysRegFileState.read]

/-- Retire returns tag to freelist, restoring count to 32 -/
theorem renamestage_retire :
    let instr := { opType := .ADD, rd := some ⟨5, by omega⟩, rs1 := some ⟨1, by omega⟩,
                   rs2 := some ⟨2, by omega⟩, imm := none, pc := 0 : DecodedInstruction }
    let (state', _) := renameInstruction RenameStageState.init instr
    let state'' := retire state' ⟨5, by omega⟩
    state''.freeList.count = 32 := by native_decide

/-- ReadOperands returns correct values from PhysRegFile -/
theorem renamestage_read_operands :
    let state := writeBack (writeBack RenameStageState.init ⟨32, by omega⟩ 100) ⟨33, by omega⟩ 200
    readOperands state ⟨32, by omega⟩ ⟨33, by omega⟩ = (100, 200) := by native_decide

/-! ## Generic Behavioral Proofs -/

/-- Rename doesn't modify PhysRegFile -/
theorem renamestage_rename_preserves_prf (state : RenameStageState) (instr : DecodedInstruction) :
    (renameInstruction state instr).1.physRegFile = state.physRegFile := by
  unfold renameInstruction
  simp only
  repeat (first | split | rfl)

/-- ReadOperands is independent of RAT/FreeList state (only depends on PhysRegFile) -/
theorem renamestage_read_independent (state : RenameStageState) (t1 t2 : Fin 64) :
    readOperands state t1 t2 = state.physRegFile.readPair t1 t2 := by
  simp [readOperands]

end Shoumei.RISCV.Renaming.RenameStageProofs
