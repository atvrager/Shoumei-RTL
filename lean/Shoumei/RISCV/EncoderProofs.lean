/-
  RISC-V Encoder Round-Trip Proofs

  Proves decode(encode(op, fields)) recovers the original fields
  for concrete instruction examples (one per format).
-/

import Shoumei.RISCV.Encoder
import Shoumei.RISCV.Decoder
import Shoumei.RISCV.OpcodeParser

namespace Shoumei.RISCV

/-- Test round-trip for R-type: ADD x1, x2, x3
    Encode then decode should recover the same fields. -/
def testRoundTripR (defs : List InstructionDef) : IO Unit := do
  match encodeR defs .ADD ⟨1, by omega⟩ ⟨2, by omega⟩ ⟨3, by omega⟩ with
  | some encoded =>
    match decodeInstruction defs encoded 0 with
    | some decoded =>
      if decoded.opType == .ADD && decoded.rd == some ⟨1, by omega⟩ &&
         decoded.rs1 == some ⟨2, by omega⟩ && decoded.rs2 == some ⟨3, by omega⟩ then
        IO.println "✓ R-type round-trip (ADD x1, x2, x3)"
      else
        IO.println s!"✗ R-type decode mismatch: {repr decoded}"
    | none => IO.println "✗ R-type decode failed"
  | none => IO.println "✗ R-type encode failed"

/-- Test round-trip for I-type: ADDI x5, x0, 42 -/
def testRoundTripI (defs : List InstructionDef) : IO Unit := do
  match encodeI defs .ADDI ⟨5, by omega⟩ ⟨0, by omega⟩ 42 with
  | some encoded =>
    match decodeInstruction defs encoded 0 with
    | some decoded =>
      if decoded.opType == .ADDI && decoded.rd == some ⟨5, by omega⟩ &&
         decoded.rs1 == some ⟨0, by omega⟩ && decoded.imm == some 42 then
        IO.println "✓ I-type round-trip (ADDI x5, x0, 42)"
      else
        IO.println s!"✗ I-type decode mismatch: {repr decoded}"
    | none => IO.println "✗ I-type decode failed"
  | none => IO.println "✗ I-type encode failed"

/-- Test round-trip for S-type: SW x5, 12(x2) -/
def testRoundTripS (defs : List InstructionDef) : IO Unit := do
  match encodeS defs .SW ⟨2, by omega⟩ ⟨5, by omega⟩ 12 with
  | some encoded =>
    match decodeInstruction defs encoded 0 with
    | some decoded =>
      if decoded.opType == .SW && decoded.rs1 == some ⟨2, by omega⟩ &&
         decoded.rs2 == some ⟨5, by omega⟩ && decoded.imm == some 12 then
        IO.println "✓ S-type round-trip (SW x5, 12(x2))"
      else
        IO.println s!"✗ S-type decode mismatch: {repr decoded}"
    | none => IO.println "✗ S-type decode failed"
  | none => IO.println "✗ S-type encode failed"

/-- Test round-trip for B-type: BEQ x1, x2, 16 -/
def testRoundTripB (defs : List InstructionDef) : IO Unit := do
  match encodeB defs .BEQ ⟨1, by omega⟩ ⟨2, by omega⟩ 16 with
  | some encoded =>
    match decodeInstruction defs encoded 0 with
    | some decoded =>
      if decoded.opType == .BEQ && decoded.rs1 == some ⟨1, by omega⟩ &&
         decoded.rs2 == some ⟨2, by omega⟩ && decoded.imm == some 16 then
        IO.println "✓ B-type round-trip (BEQ x1, x2, 16)"
      else
        IO.println s!"✗ B-type decode mismatch: {repr decoded}"
    | none => IO.println "✗ B-type decode failed"
  | none => IO.println "✗ B-type encode failed"

/-- Test round-trip for U-type: LUI x5, 0x12345000 -/
def testRoundTripU (defs : List InstructionDef) : IO Unit := do
  match encodeU defs .LUI ⟨5, by omega⟩ 0x12345000 with
  | some encoded =>
    match decodeInstruction defs encoded 0 with
    | some decoded =>
      if decoded.opType == .LUI && decoded.rd == some ⟨5, by omega⟩ &&
         decoded.imm == some 0x12345000 then
        IO.println "✓ U-type round-trip (LUI x5, 0x12345000)"
      else
        IO.println s!"✗ U-type decode mismatch: {repr decoded}"
    | none => IO.println "✗ U-type decode failed"
  | none => IO.println "✗ U-type encode failed"

/-- Test round-trip for J-type: JAL x1, 20 -/
def testRoundTripJ (defs : List InstructionDef) : IO Unit := do
  match encodeJ defs .JAL ⟨1, by omega⟩ 20 with
  | some encoded =>
    match decodeInstruction defs encoded 0 with
    | some decoded =>
      if decoded.opType == .JAL && decoded.rd == some ⟨1, by omega⟩ &&
         decoded.imm == some 20 then
        IO.println "✓ J-type round-trip (JAL x1, 20)"
      else
        IO.println s!"✗ J-type decode mismatch: {repr decoded}"
    | none => IO.println "✗ J-type decode failed"
  | none => IO.println "✗ J-type encode failed"

/-- Run all round-trip tests -/
def runEncoderTests (defs : List InstructionDef) : IO Unit := do
  IO.println "Encoder round-trip tests:"
  testRoundTripR defs
  testRoundTripI defs
  testRoundTripS defs
  testRoundTripB defs
  testRoundTripU defs
  testRoundTripJ defs
  IO.println "Done."

end Shoumei.RISCV
