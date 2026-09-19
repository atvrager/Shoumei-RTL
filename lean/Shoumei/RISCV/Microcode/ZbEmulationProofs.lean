/-
ZbEmulationProofs.lean - Behavioral correctness, equivalence, and fault preservation proofs.

Verifies:
1. Semantic equivalence: executing Zb* microcode matches the mathematical ISA specifications.
2. Fault preservation: any unallocated or non-Zb* instruction provably results in an architectural
   illegal instruction exception (mcause=2, mtval=insn, trapTaken=true).
-/

import Shoumei.RISCV.Microcode.ZbEmulationLibrary

namespace Shoumei.RISCV.Microcode

/-! ## 1. Concrete Instruction Encodings for Proving Ground -/

-- sh1add x1, x2, x3: funct7=0x10, rs2=3, rs1=2, funct3=2, rd=1, opcode=0x33
def insnSh1add : UInt32 := 0x203120b3

-- sh2add x1, x2, x3: funct7=0x10, rs2=3, rs1=2, funct3=4, rd=1, opcode=0x33
def insnSh2add : UInt32 := 0x203140b3

-- sh3add x1, x2, x3: funct7=0x10, rs2=3, rs1=2, funct3=6, rd=1, opcode=0x33
def insnSh3add : UInt32 := 0x203160b3

-- bset x1, x2, x3: funct7=0x14, rs2=3, rs1=2, funct3=1, rd=1, opcode=0x33
def insnBset : UInt32 := 0x283110b3

-- bclr x1, x2, x3: funct7=0x24, rs2=3, rs1=2, funct3=1, rd=1, opcode=0x33
def insnBclr : UInt32 := 0x483110b3

-- binv x1, x2, x3: funct7=0x34, rs2=3, rs1=2, funct3=1, rd=1, opcode=0x33
def insnBinv : UInt32 := 0x683110b3

-- andn x1, x2, x3: funct7=0x20, rs2=3, rs1=2, funct3=7, rd=1, opcode=0x33
def insnAndn : UInt32 := 0x403170b3

-- orn x1, x2, x3: funct7=0x20, rs2=3, rs1=2, funct3=6, rd=1, opcode=0x33
def insnOrn : UInt32 := 0x403160b3

-- xnor x1, x2, x3: funct7=0x20, rs2=3, rs1=2, funct3=4, rd=1, opcode=0x33
def insnXnor : UInt32 := 0x403140b3

-- min x1, x2, x3: funct7=0x05, rs2=3, rs1=2, funct3=4, rd=1, opcode=0x33
def insnMin : UInt32 := 0x0a3140b3

-- max x1, x2, x3: funct7=0x05, rs2=3, rs1=2, funct3=5, rd=1, opcode=0x33
def insnMax : UInt32 := 0x0a3150b3

-- ror x1, x2, x3: funct7=0x30, rs2=3, rs1=2, funct3=5, rd=1, opcode=0x33
def insnRor : UInt32 := 0x603150b3

-- rol x1, x2, x3: funct7=0x30, rs2=3, rs1=2, funct3=1, rd=1, opcode=0x33
def insnRol : UInt32 := 0x603110b3

-- clmul x1, x2, x3: funct7=0x05, rs2=3, rs1=2, funct3=1, rd=1, opcode=0x33
def insnClmul : UInt32 := 0x0a3110b3

-- Undefined / Illegal instruction: 0x00000000
def insnIllegalZero : UInt32 := 0x00000000

-- Unallocated custom opcode: 0x0000007b
def insnIllegalCustom : UInt32 := 0x0000007b

/-! ## 2. Behavioral Equivalence Theorems -/

/-- sh1add execution matches specification -/
theorem execute_sh1add_equiv (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    (executeFallback insnSh1add pc rs1 rs2 rd).temp2 = specSh1add rs1 rs2 := by
  rfl

/-- sh2add execution matches specification -/
theorem execute_sh2add_equiv (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    (executeFallback insnSh2add pc rs1 rs2 rd).temp2 = specSh2add rs1 rs2 := by
  rfl

/-- sh3add execution matches specification -/
theorem execute_sh3add_equiv (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    (executeFallback insnSh3add pc rs1 rs2 rd).temp2 = specSh3add rs1 rs2 := by
  rfl

/-- bset execution matches specification -/
theorem execute_bset_equiv (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    (executeFallback insnBset pc rs1 rs2 rd).temp2 = specBset rs1 rs2 := by
  rfl

/-- bclr execution matches specification -/
theorem execute_bclr_equiv (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    (executeFallback insnBclr pc rs1 rs2 rd).temp2 = specBclr rs1 rs2 := by
  rfl

/-- binv execution matches specification -/
theorem execute_binv_equiv (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    (executeFallback insnBinv pc rs1 rs2 rd).temp2 = specBinv rs1 rs2 := by
  rfl

/-- andn execution matches specification -/
theorem execute_andn_equiv (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    (executeFallback insnAndn pc rs1 rs2 rd).temp2 = specAndn rs1 rs2 := by
  rfl

/-- orn execution matches specification -/
theorem execute_orn_equiv (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    (executeFallback insnOrn pc rs1 rs2 rd).temp2 = specOrn rs1 rs2 := by
  rfl

/-- xnor execution matches specification -/
theorem execute_xnor_equiv (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    (executeFallback insnXnor pc rs1 rs2 rd).temp2 = specXnor rs1 rs2 := by
  rfl

/-- min execution matches specification -/
theorem execute_min_equiv (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    (executeFallback insnMin pc rs1 rs2 rd).temp2 = specMin rs1 rs2 := by
  rfl

/-- max execution matches specification -/
theorem execute_max_equiv (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    (executeFallback insnMax pc rs1 rs2 rd).temp2 = specMax rs1 rs2 := by
  rfl

/-- ror execution matches specification -/
theorem execute_ror_equiv (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    (executeFallback insnRor pc rs1 rs2 rd).temp2 = specRor rs1 rs2 := by
  rfl

/-- rol execution matches specification -/
theorem execute_rol_equiv (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    (executeFallback insnRol pc rs1 rs2 rd).temp2 = specRol rs1 rs2 := by
  rfl

/-- clmul execution matches specification -/
theorem execute_clmul_equiv (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    (executeFallback insnClmul pc rs1 rs2 rd).temp2 = specClmul rs1 rs2 := by
  rfl

/-! ## 3. Fault Preservation Theorems -/

/-- Zero instruction triggers illegal instruction trap -/
theorem fault_on_zero (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    let res := executeFallback insnIllegalZero pc rs1 rs2 rd
    res.trapTaken = true ∧ res.trapCause = 2 ∧ res.trapVal = 0 := by
  refine ⟨rfl, rfl, rfl⟩

/-- Unallocated custom opcode triggers illegal instruction trap -/
theorem fault_on_custom (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    let res := executeFallback insnIllegalCustom pc rs1 rs2 rd
    res.trapTaken = true ∧ res.trapCause = 2 ∧ res.trapVal = 0x7b := by
  refine ⟨rfl, rfl, rfl⟩

/-- General theorem: any instruction with dispatchZb = none causes an illegal trap -/
theorem dispatch_none_causes_trap (insn : UInt32) (pc : UInt64) (rs1 rs2 : UInt64) (rd : Fin 64) :
    dispatchZb insn = none →
    let res := executeFallback insn pc rs1 rs2 rd
    res.trapTaken = true ∧ res.trapCause = 2 ∧ res.trapVal = UInt64.ofNat insn.toNat ∧ res.done = true := by
  intro hNone
  unfold executeFallback
  unfold getFallbackRoutine
  rw [hNone]
  dsimp [runProgram, illegalInsnRoutine, stepFallback]
  exact ⟨rfl, rfl, rfl, rfl⟩

end Shoumei.RISCV.Microcode
