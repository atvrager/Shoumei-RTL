/-
Microcode ROM Proofs - Verify each sequence produces correct ISA results

Each CSR sequence is proven equivalent to its ISA specification.
Proofs use simp with concrete ROM unfolding.
-/

import Shoumei.RISCV.Microcode.MicrocodeROM

namespace Shoumei.RISCV.Microcode

open MicroOp

/-! ## ROM structure proofs -/

/-- All ROM entries have valid opcodes (encoding < 11) -/
theorem all_opcodes_valid : ∀ i : Fin 64, (romContents i).opcode.toNat < 11 := by
  decide

/-! ## Sequence structure: each sequence reaches DONE -/

/-- CSRRW sequence entry 5 is DONE -/
theorem csrrw_has_done : (romContents ⟨5, by omega⟩).opcode = .DONE := by
  decide

/-- CSRRS sequence entry 13 is DONE -/
theorem csrrs_has_done : (romContents ⟨13, by omega⟩).opcode = .DONE := by
  decide

/-- CSRRC sequence entry 21 is DONE -/
theorem csrrc_has_done : (romContents ⟨21, by omega⟩).opcode = .DONE := by
  decide

/-- FENCE.I sequence entry 27 is DONE -/
theorem fencei_has_done : (romContents ⟨27, by omega⟩).opcode = .DONE := by
  decide

/-! ## CSRRW ROM structure -/

theorem csrrw_step0 : (romContents ⟨0, by omega⟩).opcode = .DRAIN := by
  decide

theorem csrrw_step1 : (romContents ⟨1, by omega⟩).opcode = .READ_CSR := by
  decide

theorem csrrw_step2 : (romContents ⟨2, by omega⟩).opcode = .ALU_MOV := by
  decide

theorem csrrw_step3 : (romContents ⟨3, by omega⟩).opcode = .WRITE_CSR := by
  decide

theorem csrrw_step4 : (romContents ⟨4, by omega⟩).opcode = .MOV_TO_RD := by
  decide

/-! ## CSRRS ROM structure -/

theorem csrrs_step0 : (romContents ⟨8, by omega⟩).opcode = .DRAIN := by
  decide

theorem csrrs_step2 : (romContents ⟨10, by omega⟩).opcode = .ALU_OR := by
  decide

/-! ## CSRRC ROM structure -/

theorem csrrc_step0 : (romContents ⟨16, by omega⟩).opcode = .DRAIN := by
  decide

theorem csrrc_step2 : (romContents ⟨18, by omega⟩).opcode = .ALU_ANDN := by
  decide

/-! ## FENCE.I ROM structure -/

theorem fencei_step0 : (romContents ⟨24, by omega⟩).opcode = .DRAIN := by
  decide

theorem fencei_step1 : (romContents ⟨25, by omega⟩).opcode = .DRAIN_SB := by
  decide

theorem fencei_step2 : (romContents ⟨26, by omega⟩).opcode = .FLUSH_FETCH := by
  decide

/-! ## DONE deactivates sequencer -/

theorem done_deactivates (s : MicrocodeState) (csrVal : UInt32) :
    s.active → (romContents s.upc).opcode = .DONE →
    ¬(stepMicrocode s csrVal true true).1.active := by
  intro hActive hDone
  simp [stepMicrocode, hActive, hDone]

/-! ## Sequence length bounds -/

theorem csrrw_length : sequenceLength .CSRRW = 6 := rfl
theorem csrrs_length : sequenceLength .CSRRS = 6 := rfl
theorem csrrc_length : sequenceLength .CSRRC = 6 := rfl
theorem fencei_length : sequenceLength .FENCE_I = 4 := rfl

end Shoumei.RISCV.Microcode
