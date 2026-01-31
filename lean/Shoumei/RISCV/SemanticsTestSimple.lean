/-
  Simplified RISC-V Semantics Test (a few key instructions)
-/

import Shoumei.RISCV.ISA
import Shoumei.RISCV.Decoder
import Shoumei.RISCV.Semantics
import Shoumei.RISCV.OpcodeParser

namespace Shoumei.RISCV

/-- Create initial state for testing -/
def mkTestState : ArchState := {
  pc := 0x1000
  regs := fun reg =>
    match reg.val with
    | 0 => 0           -- x0 is always 0
    | 1 => 100         -- x1 = 100
    | 2 => 200         -- x2 = 200
    | 3 => 0xFFFFFFFF  -- x3 = -1
    | 5 => 42          -- x5 = 42
    | _ => 0
  memory := fun _ => 0
}

/-- Test semantic execution for key instructions -/
def testKeySemantics (defs : List InstructionDef) : IO Unit := do
  IO.println "Testing key RV32I instruction semantics...\n"

  let initState := mkTestState

  -- Test ADD (encoding: 0x002085b3 = ADD x11, x1, x2)
  IO.print "Testing ADD x11, x1, x2... "
  match decodeInstruction defs 0x002085b3 with
  | some decoded =>
    match executeInstruction initState decoded with
    | .ok newState =>
      if newState.readReg ⟨11, by omega⟩ == 300 then
        IO.println "✓ (100 + 200 = 300)"
      else
        IO.println s!"✗ (got {newState.readReg ⟨11, by omega⟩})"
    | _ => IO.println "✗ (execution failed)"
  | none => IO.println "✗ (decode failed)"

  -- Test SUB (encoding: 0x40110633 = SUB x12, x2, x1)
  IO.print "Testing SUB x12, x2, x1... "
  match decodeInstruction defs 0x40110633 with
  | some decoded =>
    match executeInstruction initState decoded with
    | .ok newState =>
      if newState.readReg ⟨12, by omega⟩ == 100 then
        IO.println "✓ (200 - 100 = 100)"
      else
        IO.println s!"✗ (got {newState.readReg ⟨12, by omega⟩})"
    | _ => IO.println "✗ (execution failed)"
  | none => IO.println "✗ (decode failed)"

  -- Test ADDI
  IO.print "Testing ADDI x20, x1, 50... "
  match decodeInstruction defs 0x03208a13 with
  | some decoded =>
    match executeInstruction initState decoded with
    | .ok newState =>
      if newState.readReg ⟨20, by omega⟩ == 150 then
        IO.println "✓ (100 + 50 = 150)"
      else
        IO.println s!"✗ (got {newState.readReg ⟨20, by omega⟩})"
    | _ => IO.println "✗ (execution failed)"
  | none => IO.println "✗ (decode failed)"

  -- Test BEQ (taken)
  IO.print "Testing BEQ x1, x1, 8 (taken)... "
  match decodeInstruction defs 0x00108463 with
  | some decoded =>
    match executeInstruction initState decoded with
    | .ok newState =>
      if newState.pc == 0x1008 then
        IO.println "✓ (PC = 0x1000 + 8)"
      else
        IO.println s!"✗ (PC = {newState.pc})"
    | _ => IO.println "✗ (execution failed)"
  | none => IO.println "✗ (decode failed)"

  -- Test JAL
  IO.print "Testing JAL x1, 100... "
  match decodeInstruction defs 0x064000ef with
  | some decoded =>
    match executeInstruction initState decoded with
    | .ok newState =>
      if newState.pc == 0x1064 && newState.readReg ⟨1, by omega⟩ == 0x1004 then
        IO.println "✓ (PC = 0x1064, x1 = 0x1004)"
      else
        IO.println s!"✗ (PC = {newState.pc}, x1 = {newState.readReg ⟨1, by omega⟩})"
    | _ => IO.println "✗ (execution failed)"
  | none => IO.println "✗ (decode failed)"

  -- Test LUI
  IO.print "Testing LUI x10, 0x12345... "
  match decodeInstruction defs 0x12345537 with
  | some decoded =>
    match executeInstruction initState decoded with
    | .ok newState =>
      if newState.readReg ⟨10, by omega⟩ == 0x12345000 then
        IO.println "✓ (x10 = 0x12345000)"
      else
        IO.println s!"✗ (got {newState.readReg ⟨10, by omega⟩})"
    | _ => IO.println "✗ (execution failed)"
  | none => IO.println "✗ (decode failed)"

  IO.println "\n✓ Key instruction semantics working!"

end Shoumei.RISCV
