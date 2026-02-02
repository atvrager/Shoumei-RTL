/-
  RISC-V M Extension Semantic Correctness Proofs

  Proves key properties of the executeMulDiv function,
  including edge cases mandated by the RISC-V specification.
-/

import Shoumei.RISCV.Semantics

namespace Shoumei.RISCV.SemanticsProofs

open Shoumei.RISCV

/-! ## Division by Zero -/

/-- DIV by zero returns -1 (0xFFFFFFFF) per RISC-V spec -/
theorem div_by_zero (a : UInt32) :
    executeMulDiv .DIV a 0 = 0xFFFFFFFF := by
  simp [executeMulDiv]

/-- DIVU by zero returns 2^32-1 (0xFFFFFFFF) per RISC-V spec -/
theorem divu_by_zero (a : UInt32) :
    executeMulDiv .DIVU a 0 = 0xFFFFFFFF := by
  simp [executeMulDiv]

/-- REM by zero returns dividend per RISC-V spec -/
theorem rem_by_zero (a : UInt32) :
    executeMulDiv .REM a 0 = a := by
  simp [executeMulDiv]

/-- REMU by zero returns dividend per RISC-V spec -/
theorem remu_by_zero (a : UInt32) :
    executeMulDiv .REMU a 0 = a := by
  simp [executeMulDiv]

/-! ## MUL Properties -/

/-- MUL produces the lower 32 bits of the product -/
theorem mul_is_lower32 (a b : UInt32) :
    executeMulDiv .MUL a b = UInt32.ofNat ((a.toNat * b.toNat) % 2^32) := by
  simp [executeMulDiv]

/-- MULHU produces the upper 32 bits of the unsigned product -/
theorem mulhu_is_upper32 (a b : UInt32) :
    executeMulDiv .MULHU a b = UInt32.ofNat ((a.toNat * b.toNat) / 2^32) := by
  simp [executeMulDiv]

end Shoumei.RISCV.SemanticsProofs
