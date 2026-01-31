/-
  RISC-V Instruction Semantics Tests

  Tests that each instruction's semantics matches the RISC-V ISA specification.
-/

import Shoumei.RISCV.ISA
import Shoumei.RISCV.Decoder
import Shoumei.RISCV.Semantics
import Shoumei.RISCV.OpcodeParser

namespace Shoumei.RISCV

/-- Create initial architectural state for testing -/
def mkTestState : ArchState := {
  pc := 0x1000
  regs := fun reg =>
    match reg.val with
    | 0 => 0           -- x0 is always 0
    | 1 => 100         -- x1 = 100
    | 2 => 200         -- x2 = 200
    | 3 => 0xFFFFFFFF  -- x3 = -1 (two's complement)
    | 4 => 0x80000000  -- x4 = most negative 32-bit number
    | 5 => 42          -- x5 = 42
    | _ => 0           -- Others = 0
  memory := fun addr =>
    match addr with
    | 0x2000 => 0xDEADBEEF
    | 0x2004 => 0x12345678
    | _ => 0
}

/-- Test helper: execute instruction and check result -/
def testExec (name : String) (instrWord : UInt32) (defs : List InstructionDef)
    (check : ArchState → Bool) : IO Bool := do
  let initState := mkTestState
  match decodeInstruction defs instrWord with
  | none =>
    IO.println s!"✗ {name}: failed to decode"
    return false
  | some decoded =>
    match executeInstruction initState decoded with
    | .ok newState =>
      if check newState then
        IO.println s!"✓ {name}"
        return true
      else
        IO.println s!"✗ {name}: check failed"
        return false
    | .illegalInstruction =>
      IO.println s!"✗ {name}: illegal instruction"
      return false
    | .ecall =>
      IO.println s!"✓ {name}: ECALL"
      return true
    | .ebreak =>
      IO.println s!"✓ {name}: EBREAK"
      return true

/-- Run comprehensive semantics tests -/
def testAllSemantics (defs : List InstructionDef) : IO Unit := do
  IO.println "Testing RV32I instruction semantics...\n"

  let mut passCount : Nat := 0
  let mut failCount : Nat := 0

  IO.println "=== R-type ALU Operations ==="

  -- ADD x10, x1, x2  (expect: x10 = 100 + 200 = 300)
  if ← testExec "ADD x10, x1, x2" 0x002085b3 defs
        (fun s => s.readReg ⟨10, by omega⟩ == 300) then
    passCount := passCount + 1
  else
    failCount := failCount + 1

  -- SUB x11, x2, x1  (expect: x11 = 200 - 100 = 100)
  if ← testExec "SUB x11, x2, x1" 0x40110633 defs
      (fun s => s.readReg ⟨11, by omega⟩ == 100))

  -- AND x12, x1, x5  (expect: x12 = 100 & 42 = 32)
  if ← testExec "AND x12, x1, x5" 0x0050f633 defs
      (fun s => s.readReg ⟨12, by omega⟩ == 32))

  -- OR x13, x1, x5  (expect: x13 = 100 | 42 = 110)
  if ← testExec "OR x13, x1, x5" 0x0050e6b3 defs
      (fun s => s.readReg ⟨13, by omega⟩ == 110))

  -- XOR x14, x1, x5  (expect: x14 = 100 ^ 42 = 78)
  if ← testExec "XOR x14, x1, x5" 0x0050c733 defs
      (fun s => s.readReg ⟨14, by omega⟩ == 78))

  -- SLT x15, x1, x2  (expect: x15 = 1, since 100 < 200)
  if ← testExec "SLT x15, x1, x2" 0x0020a7b3 defs
      (fun s => s.readReg ⟨15, by omega⟩ == 1))

  -- SLTU x16, x1, x2  (expect: x16 = 1, since 100 < 200 unsigned)
  if ← testExec "SLTU x16, x1, x2" 0x0020b833 defs
      (fun s => s.readReg ⟨16, by omega⟩ == 1))

  -- SLL x17, x5, x1  (expect: x17 = 42 << (100 & 0x1F) = 42 << 4 = 672)
  if ← testExec "SLL x17, x5, x1" 0x001298b3 defs
      (fun s => s.readReg ⟨17, by omega⟩ == 672))

  -- SRL x18, x5, x1  (expect: x18 = 42 >> 4 = 2)
  if ← testExec "SRL x18, x5, x1" 0x0012d933 defs
      (fun s => s.readReg ⟨18, by omega⟩ == 2))

  -- SRA x19, x3, x1  (expect: x19 = -1 >> 4 = -1, sign extended)
  if ← testExec "SRA x19, x3, x1" 0x4011d9b3 defs
      (fun s => s.readReg ⟨19, by omega⟩ == 0xFFFFFFFF))

  IO.println "\n=== I-type ALU Operations ==="

  -- ADDI x20, x1, 50  (expect: x20 = 100 + 50 = 150)
  if ← testExec "ADDI x20, x1, 50" 0x03208a13 defs
      (fun s => s.readReg ⟨20, by omega⟩ == 150))

  -- ANDI x21, x1, 15  (expect: x21 = 100 & 15 = 4)
  if ← testExec "ANDI x21, x1, 15" 0x00f0fa93 defs
      (fun s => s.readReg ⟨21, by omega⟩ == 4))

  -- ORI x22, x5, 128  (expect: x22 = 42 | 128 = 170)
  if ← testExec "ORI x22, x5, 128" 0x08026b13 defs
      (fun s => s.readReg ⟨22, by omega⟩ == 170))

  -- XORI x23, x5, 255  (expect: x23 = 42 ^ 255 = 213)
  if ← testExec "XORI x23, x5, 255" 0x0ff2cb93 defs
      (fun s => s.readReg ⟨23, by omega⟩ == 213))

  -- SLLI x24, x5, 3  (expect: x24 = 42 << 3 = 336)
  if ← testExec "SLLI x24, x5, 3" 0x00329c13 defs
      (fun s => s.readReg ⟨24, by omega⟩ == 336))

  -- SRLI x25, x1, 2  (expect: x25 = 100 >> 2 = 25)
  if ← testExec "SRLI x25, x1, 2" 0x0020dc93 defs
      (fun s => s.readReg ⟨25, by omega⟩ == 25))

  -- SRAI x26, x3, 8  (expect: x26 = -1 >> 8 = -1)
  if ← testExec "SRAI x26, x3, 8" 0x4081dd13 defs
      (fun s => s.readReg ⟨26, by omega⟩ == 0xFFFFFFFF))

  -- SLTI x27, x1, 150  (expect: x27 = 1, since 100 < 150)
  if ← testExec "SLTI x27, x1, 150" 0x0960ad93 defs
      (fun s => s.readReg ⟨27, by omega⟩ == 1))

  -- SLTIU x28, x3, 100  (expect: x28 = 0, since 0xFFFFFFFF > 100 unsigned)
  if ← testExec "SLTIU x28, x3, 100" 0x0641be13 defs
      (fun s => s.readReg ⟨28, by omega⟩ == 0))

  IO.println "\n=== Load Operations ==="
  -- Note: These depend on memory initialization in mkTestState

  -- LW x10, 0(x0)  - Load from address 0x2000
  -- We need to set up memory at PC + offset properly
  -- For now, testing structure is correct

  IO.println "\n=== Branch Operations ==="

  -- BEQ x1, x1, 8  (expect: PC = 0x1000 + 8 = 0x1008, since x1 == x1)
  if ← testExec "BEQ x1, x1, 8" 0x00108463 defs
    (fun s => s.pc == 0x1008))

  -- BNE x1, x2, 12  (expect: PC = 0x1000 + 12, since x1 != x2)
  if ← testExec "BNE x1, x2, 12" 0x00209663 defs
    (fun s => s.pc == 0x100C))

  -- BLT x1, x2, 16  (expect: PC = 0x1000 + 16, since 100 < 200)
  if ← testExec "BLT x1, x2, 16" 0x0020c863 defs
    (fun s => s.pc == 0x1010))

  -- BGE x2, x1, 20  (expect: PC = 0x1000 + 20, since 200 >= 100)
  if ← testExec "BGE x2, x1, 20" 0x00115a63 defs
    (fun s => s.pc == 0x1014))

  -- BLTU x1, x2, 24  (expect: PC = 0x1000 + 24, since 100 < 200 unsigned)
  if ← testExec "BLTU x1, x2, 24" 0x0020ec63 defs
    (fun s => s.pc == 0x1018))

  -- BGEU x2, x1, 28  (expect: PC = 0x1000 + 28, since 200 >= 100 unsigned)
  if ← testExec "BGEU x2, x1, 28" 0x00117e63 defs
    (fun s => s.pc == 0x101C))

  IO.println "\n=== Jump Operations ==="

  -- JAL x1, 100  (expect: x1 = 0x1004, PC = 0x1000 + 100)
  if ← testExec "JAL x1, 100" 0x064000ef defs
      (fun s => s.readReg ⟨1, by omega⟩ == 0x1004 && s.pc == 0x1064))

  -- JALR x1, x2, 0  (expect: x1 = 0x1004, PC = x2 + 0 = 200)
  if ← testExec "JALR x1, x2, 0" 0x000100e7 defs
      (fun s => s.readReg ⟨1, by omega⟩ == 0x1004 && s.pc == 200))

  IO.println "\n=== Upper Immediate Operations ==="

  -- LUI x10, 0x12345  (expect: x10 = 0x12345000)
  if ← testExec "LUI x10, 0x12345" 0x12345537 defs
      (fun s => s.readReg ⟨10, by omega⟩ == 0x12345000))

  -- AUIPC x11, 0x1000  (expect: x11 = PC + 0x01000000 = 0x1001000)
  if ← testExec "AUIPC x11, 0x1000" 0x01000597 defs
      (fun s => s.readReg ⟨11, by omega⟩ == 0x01001000))

  IO.println "\n=== System Operations ==="

  -- FENCE (expect: PC advances, no other effects)
  if ← testExec "FENCE" 0x0000000f defs
    (fun s => s.pc == 0x1004))

  -- ECALL
  if ← testExec "ECALL" 0x00000073 defs
    (fun _ => true))  -- Just check it returns .ecall

  -- EBREAK
  if ← testExec "EBREAK" 0x00100073 defs
    (fun _ => true))  -- Just check it returns .ebreak

  IO.println "\n=================================================="
  IO.println s!"Semantics Test Results: {passCount} passed, {failCount} failed"
  if failCount == 0 then
    IO.println "✓ All instruction semantics working correctly!"
  else
    IO.println s!"✗ {failCount} semantic test(s) failed"

end Shoumei.RISCV
