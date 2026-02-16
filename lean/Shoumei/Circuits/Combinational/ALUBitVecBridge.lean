/-
Circuits/Combinational/ALUBitVecBridge.lean - BitVec Semantic Bridge for ALU32

Phase 2 of proof strategy (see docs/proof-strategies.md): word-level reasoning
about ALU32 operations using Lean 4's BitVec type and automated decision procedures.

Architecture:
  Gate-level DSL (Bool/Wire)  ←→  BitVec 32 interpretation  →  bv_decide proofs

Three proof layers:
  Layer 1: Bridge correctness (gate-level eval ≡ word-level semantics)
  Layer 2: Word-level properties (provable by bv_decide/bv_omega/grind)
  Layer 3: Concrete validation (specific inputs via native_decide)

Tactics used (Lean 4.27.0):
  - bv_omega: linear arithmetic on BitVec (fast, no SAT)
  - bv_decide: full QF_BV via SAT bitblasting (slower, handles bitwise)
  - grind: SMT-style tactic combining multiple theories (v4.22.0+)
  - native_decide: compile-and-evaluate for concrete instances
-/

import Std.Tactic.BVDecide
import Shoumei.Reflection.ALUSymbolic

namespace Shoumei.Circuits.Combinational.BitVecBridge

open Shoumei Shoumei.Reflection Shoumei.Reflection.ALUSymbolic

/-! ## Re-export definitions from ALUSymbolic for backward compatibility -/

-- ALUOp, aluSemantics, evalALU32, mkALU32Flat, mkALUInitMap are now
-- defined in Shoumei.Reflection.ALUSymbolic and re-exported here.

/-! ## Layer 1: Bridge Correctness

The bridge connects gate-level evaluation to word-level semantics.
Proven via verified symbolic circuit evaluation (see Reflection/ALUSymbolic.lean). -/

-- The bridge theorem is now proven (modulo per-opcode sorry's in ALUSymbolic)
-- and re-exported from ALUSymbolic.alu32_bridge.

/-! ## Layer 2: Word-Level Properties

These properties reason purely about the word-level semantics — no circuit
evaluation involved. Uses bv_omega for linear arithmetic and grind for
bitwise properties (both available in Lean 4.27.0). -/

section ArithmeticProperties

theorem alu_add_comm (a b : BitVec 32) :
    aluSemantics .ADD a b = aluSemantics .ADD b a := by
  simp [aluSemantics]; bv_omega

theorem alu_add_zero (a : BitVec 32) :
    aluSemantics .ADD a 0 = a := by
  simp [aluSemantics]

theorem alu_add_assoc (a b c : BitVec 32) :
    aluSemantics .ADD (aluSemantics .ADD a b) c =
    aluSemantics .ADD a (aluSemantics .ADD b c) := by
  simp [aluSemantics]; bv_omega

theorem alu_sub_self (a : BitVec 32) :
    aluSemantics .SUB a a = 0 := by
  simp [aluSemantics]

theorem alu_add_sub_cancel (a b : BitVec 32) :
    aluSemantics .SUB (aluSemantics .ADD a b) b = a := by
  simp [aluSemantics]; bv_omega

/-- RISC-V implementation: SUB uses two's complement (ADD with bitwise NOT + 1). -/
theorem alu_sub_is_add_neg (a b : BitVec 32) :
    aluSemantics .SUB a b = aluSemantics .ADD a (~~~b + 1) := by
  simp [aluSemantics]; bv_omega

end ArithmeticProperties

section LogicProperties

theorem alu_and_comm (a b : BitVec 32) :
    aluSemantics .AND a b = aluSemantics .AND b a := by
  simp [aluSemantics]; bv_decide

theorem alu_or_comm (a b : BitVec 32) :
    aluSemantics .OR a b = aluSemantics .OR b a := by
  simp [aluSemantics]; bv_decide

theorem alu_xor_comm (a b : BitVec 32) :
    aluSemantics .XOR a b = aluSemantics .XOR b a := by
  simp [aluSemantics]; bv_decide

theorem alu_and_self (a : BitVec 32) :
    aluSemantics .AND a a = a := by
  simp [aluSemantics]

theorem alu_or_self (a : BitVec 32) :
    aluSemantics .OR a a = a := by
  simp [aluSemantics]

theorem alu_xor_self (a : BitVec 32) :
    aluSemantics .XOR a a = 0 := by
  simp [aluSemantics]

/-- XOR with all-ones is bitwise NOT (used in RISC-V pseudoinstruction NOT). -/
theorem alu_xor_ones_is_not (a : BitVec 32) :
    aluSemantics .XOR a 0xFFFFFFFF#32 = ~~~a := by
  simp [aluSemantics]; bv_decide

/-- De Morgan's law: ~(a & b) = ~a | ~b. -/
theorem alu_demorgan_and (a b : BitVec 32) :
    ~~~(aluSemantics .AND a b) =
    aluSemantics .OR (~~~a) (~~~b) := by
  simp [aluSemantics]; bv_decide

/-- De Morgan's law: ~(a | b) = ~a & ~b. -/
theorem alu_demorgan_or (a b : BitVec 32) :
    ~~~(aluSemantics .OR a b) =
    aluSemantics .AND (~~~a) (~~~b) := by
  simp [aluSemantics]; bv_decide

/-- Absorption: a & (a | b) = a. -/
theorem alu_and_or_absorb (a b : BitVec 32) :
    aluSemantics .AND a (aluSemantics .OR a b) = a := by
  simp [aluSemantics]; bv_decide

/-- Distributivity: a & (b | c) = (a & b) | (a & c). -/
theorem alu_and_or_distrib (a b c : BitVec 32) :
    aluSemantics .AND a (aluSemantics .OR b c) =
    aluSemantics .OR (aluSemantics .AND a b) (aluSemantics .AND a c) := by
  simp [aluSemantics]; bv_decide

end LogicProperties

section ShiftProperties

theorem alu_sll_zero (a : BitVec 32) :
    aluSemantics .SLL a 0 = a := by
  simp [aluSemantics]

theorem alu_srl_zero (a : BitVec 32) :
    aluSemantics .SRL a 0 = a := by
  simp [aluSemantics]

theorem alu_sra_zero (a : BitVec 32) :
    aluSemantics .SRA a 0 = a := by
  simp [aluSemantics, BitVec.sshiftRight]

end ShiftProperties

section ComparisonProperties

theorem alu_sltu_irrefl (a : BitVec 32) :
    aluSemantics .SLTU a a = 0 := by
  simp [aluSemantics, BitVec.lt_irrefl]

theorem alu_slt_irrefl (a : BitVec 32) :
    aluSemantics .SLT a a = 0 := by
  simp [aluSemantics, Int.lt_irrefl]

end ComparisonProperties

/-! ## Layer 3: Concrete Validation -/

section ConcreteValidation

-- ADD: 5 + 3 = 8
theorem alu32_concrete_add :
    evalALU32 5 3 0x0 = 8 := by native_decide

-- SUB: 10 - 3 = 7
theorem alu32_concrete_sub :
    evalALU32 10 3 0x1 = 7 := by native_decide

-- AND: 0xFF00 & 0x0FF0 = 0x0F00
theorem alu32_concrete_and :
    evalALU32 0xFF00 0x0FF0 0x4 = 0x0F00 := by native_decide

-- OR: 0xFF00 | 0x00FF = 0xFFFF
theorem alu32_concrete_or :
    evalALU32 0xFF00 0x00FF 0x5 = 0xFFFF := by native_decide

-- XOR: 0xAAAA ^ 0x5555 = 0xFFFF
theorem alu32_concrete_xor :
    evalALU32 0xAAAA 0x5555 0x6 = 0xFFFF := by native_decide

-- SLT: signed(3) < signed(5) = 1
theorem alu32_concrete_slt :
    evalALU32 3 5 0x2 = 1 := by native_decide

-- SLTU: unsigned(3) < unsigned(5) = 1
theorem alu32_concrete_sltu :
    evalALU32 3 5 0x3 = 1 := by native_decide

-- SLL: 1 << 4 = 16
theorem alu32_concrete_sll :
    evalALU32 1 4 0x8 = 16 := by native_decide

-- SRL: 256 >>> 4 = 16
theorem alu32_concrete_srl :
    evalALU32 256 4 0x9 = 16 := by native_decide

-- SRA: 0xFFFFFF00 >> 4 = 0xFFFFFFF0 (sign-extends)
theorem alu32_concrete_sra :
    evalALU32 0xFFFFFF00 4 0xB = 0xFFFFFFF0 := by native_decide

end ConcreteValidation

end Shoumei.Circuits.Combinational.BitVecBridge
