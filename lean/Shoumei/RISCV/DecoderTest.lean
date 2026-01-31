/-
  Comprehensive RISC-V Decoder Test Suite

  Tests all 40 RV32I instructions with hand-crafted encodings
-/

import Shoumei.RISCV.ISA
import Shoumei.RISCV.OpcodeParser
import Shoumei.RISCV.Decoder

namespace Shoumei.RISCV

/-- Test instruction encoding and decoding -/
def testInstruction (defs : List InstructionDef) (name : String) (encoding : UInt32) (expectedOp : OpType) : IO Bool := do
  match decodeInstruction defs encoding with
  | some decoded =>
    if decoded.opType == expectedOp then
      IO.println s!"✓ {name}: {decoded.opType}"
      return true
    else
      IO.println s!"✗ {name}: expected {expectedOp}, got {decoded.opType}"
      return false
  | none =>
    IO.println s!"✗ {name}: failed to decode 0x{encoding.toNat.toDigits 16}"
    return false

/-- Comprehensive test of all 40 RV32I instructions -/
def testAllInstructions (defs : List InstructionDef) : IO Unit := do
  IO.println "Testing all 40 RV32I instructions...\n"

  let mut passCount := 0
  let mut failCount := 0

  -- R-type ALU instructions
  IO.println "=== R-type ALU Operations ==="
  if ← testInstruction defs "ADD x1, x2, x3" 0x003100b3 .ADD then passCount := passCount + 1 else failCount := failCount + 1
  if ← testInstruction defs "SUB x5, x6, x7" 0x407302b3 .SUB then passCount := passCount + 1 else failCount := failCount + 1
  if ← testInstruction defs "AND x8, x9, x10" 0x00a4f433 .AND then passCount := passCount + 1 else failCount := failCount + 1
  if ← testInstruction defs "OR x11, x12, x13" 0x00d665b3 .OR then passCount := passCount + 1 else failCount := failCount + 1
  if ← testInstruction defs "XOR x14, x15, x16" 0x0107c733 .XOR then passCount := passCount + 1 else failCount := failCount + 1
  if ← testInstruction defs "SLL x17, x18, x19" 0x013918b3 .SLL then passCount := passCount + 1 else failCount := failCount + 1
  if ← testInstruction defs "SRL x20, x21, x22" 0x016ada33 .SRL then passCount := passCount + 1 else failCount := failCount + 1
  if ← testInstruction defs "SRA x23, x24, x25" 0x419c5bb3 .SRA then passCount := passCount + 1 else failCount := failCount + 1
  if ← testInstruction defs "SLT x26, x27, x28" 0x01cdad33 .SLT then passCount := passCount + 1 else failCount := failCount + 1
  if ← testInstruction defs "SLTU x29, x30, x31" 0x01ff3eb3 .SLTU then passCount := passCount + 1 else failCount := failCount + 1

  -- I-type ALU instructions
  IO.println "\n=== I-type ALU Operations ==="
  if ← testInstruction defs "ADDI x5, x0, 42" 0x02a00293 .ADDI then passCount := passCount + 1 else failCount := failCount + 1
  if ← testInstruction defs "ANDI x6, x7, 15" 0x00f3f313 .ANDI then passCount := passCount + 1 else failCount := failCount + 1
  if ← testInstruction defs "ORI x8, x9, 255" 0x0ff4e413 .ORI then passCount := passCount + 1 else failCount := failCount + 1
  if ← testInstruction defs "XORI x10, x11, -1" 0xfff5c513 .XORI then passCount := passCount + 1 else failCount := failCount + 1
  if ← testInstruction defs "SLLI x12, x13, 5" 0x00569613 .SLLI then passCount := passCount + 1 else failCount := failCount + 1
  if ← testInstruction defs "SRLI x14, x15, 10" 0x00a7d713 .SRLI then passCount := passCount + 1 else failCount := failCount + 1
  if ← testInstruction defs "SRAI x16, x17, 3" 0x4038d813 .SRAI then passCount := passCount + 1 else failCount := failCount + 1
  if ← testInstruction defs "SLTI x18, x19, 100" 0x0649a913 .SLTI then passCount := passCount + 1 else failCount := failCount + 1
  if ← testInstruction defs "SLTIU x20, x21, 200" 0x0c8aba13 .SLTIU then passCount := passCount + 1 else failCount := failCount + 1

  -- Load instructions
  IO.println "\n=== Load Operations ==="
  if ← testInstruction defs "LB x5, 0(x6)" 0x00030283 .LB then passCount := passCount + 1 else failCount := failCount + 1
  if ← testInstruction defs "LH x7, 4(x8)" 0x00441383 .LH then passCount := passCount + 1 else failCount := failCount + 1
  if ← testInstruction defs "LW x9, 8(x10)" 0x00852483 .LW then passCount := passCount + 1 else failCount := failCount + 1
  if ← testInstruction defs "LBU x11, 12(x12)" 0x00c64583 .LBU then passCount := passCount + 1 else failCount := failCount + 1
  if ← testInstruction defs "LHU x13, 16(x14)" 0x01075683 .LHU then passCount := passCount + 1 else failCount := failCount + 1

  -- Store instructions
  IO.println "\n=== Store Operations ==="
  if ← testInstruction defs "SB x5, 0(x6)" 0x00530023 .SB then passCount := passCount + 1 else failCount := failCount + 1
  if ← testInstruction defs "SH x7, 4(x8)" 0x00741223 .SH then passCount := passCount + 1 else failCount := failCount + 1
  if ← testInstruction defs "SW x9, 8(x10)" 0x00952423 .SW then passCount := passCount + 1 else failCount := failCount + 1

  -- Branch instructions
  IO.println "\n=== Branch Operations ==="
  if ← testInstruction defs "BEQ x1, x2, 8" 0x00208463 .BEQ then passCount := passCount + 1 else failCount := failCount + 1
  if ← testInstruction defs "BNE x3, x4, 12" 0x00419663 .BNE then passCount := passCount + 1 else failCount := failCount + 1
  if ← testInstruction defs "BLT x5, x6, 16" 0x0062c863 .BLT then passCount := passCount + 1 else failCount := failCount + 1
  if ← testInstruction defs "BGE x7, x8, 20" 0x0083da63 .BGE then passCount := passCount + 1 else failCount := failCount + 1
  if ← testInstruction defs "BLTU x9, x10, 24" 0x00a4ec63 .BLTU then passCount := passCount + 1 else failCount := failCount + 1
  if ← testInstruction defs "BGEU x11, x12, 28" 0x00c5fe63 .BGEU then passCount := passCount + 1 else failCount := failCount + 1

  -- Jump instructions
  IO.println "\n=== Jump Operations ==="
  if ← testInstruction defs "JAL x1, 20" 0x014000ef .JAL then passCount := passCount + 1 else failCount := failCount + 1
  if ← testInstruction defs "JALR x5, x6, 100" 0x06430267 .JALR then passCount := passCount + 1 else failCount := failCount + 1

  -- Upper immediate instructions
  IO.println "\n=== Upper Immediate Operations ==="
  if ← testInstruction defs "LUI x5, 0x12345" 0x123452b7 .LUI then passCount := passCount + 1 else failCount := failCount + 1
  if ← testInstruction defs "AUIPC x6, 0xabcde" 0xabcde317 .AUIPC then passCount := passCount + 1 else failCount := failCount + 1

  -- System instructions
  IO.println "\n=== System Operations ==="
  if ← testInstruction defs "FENCE" 0x0ff0000f .FENCE then passCount := passCount + 1 else failCount := failCount + 1
  if ← testInstruction defs "ECALL" 0x00000073 .ECALL then passCount := passCount + 1 else failCount := failCount + 1
  if ← testInstruction defs "EBREAK" 0x00100073 .EBREAK then passCount := passCount + 1 else failCount := failCount + 1

  IO.println "\n=================================================="
  IO.println s!"Test Results: {passCount}/40 passed, {failCount}/40 failed"
  if failCount == 0 then
    IO.println "✓ All RV32I instructions decode correctly!"
  else
    IO.println s!"✗ {failCount} instruction(s) failed to decode"

end Shoumei.RISCV
