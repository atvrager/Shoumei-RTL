/-
  RISC-V Encoder Round-Trip Tests

  Proves decode(encode(op, fields)) recovers the original fields for concrete
  instruction examples, one per format, in both directions of the immediate
  range.  A failure throws: `lake exe gen_tests` runs this before generating
  anything, so a broken encoder stops the generator rather than emitting a
  corpus of silently mis-encoded programs.
-/

import Shoumei.RISCV.Encoder
import Shoumei.RISCV.Decoder
import Shoumei.RISCV.OpcodeParser

namespace Shoumei.RISCV

/-- Encode, decode and check one case; throws with the decoded fields on
    mismatch. -/
def checkRoundTrip (defs : List InstructionDef) (what : String) (enc : Option UInt32)
    (ok : DecodedInstruction → Bool) : IO Unit := do
  match enc with
  | none => throw (IO.userError s!"{what}: encode failed")
  | some w =>
    match decodeInstruction defs w 0 with
    | none => throw (IO.userError s!"{what}: decode failed (word {w})")
    | some d =>
      unless ok d do
        throw (IO.userError s!"{what}: decoded {repr d}")
      IO.println s!"✓ {what}"

/-- R-type: ADD x1, x2, x3 -/
def testRoundTripR (defs : List InstructionDef) : IO Unit :=
  checkRoundTrip defs "R-type ADD x1, x2, x3"
    (encodeR defs .ADD ⟨1, by omega⟩ ⟨2, by omega⟩ ⟨3, by omega⟩)
    (fun d => d.opType == .ADD && d.rd == some ⟨1, by omega⟩ &&
              d.rs1 == some ⟨2, by omega⟩ && d.rs2 == some ⟨3, by omega⟩)

/-- I-type: ADDI x5, x0, 42 and its negative twin -/
def testRoundTripI (defs : List InstructionDef) : IO Unit := do
  checkRoundTrip defs "I-type ADDI x5, x0, 42"
    (encodeI defs .ADDI ⟨5, by omega⟩ ⟨0, by omega⟩ 42)
    (fun d => d.opType == .ADDI && d.rd == some ⟨5, by omega⟩ &&
              d.rs1 == some ⟨0, by omega⟩ && d.imm == some 42)
  checkRoundTrip defs "I-type ADDI x5, x0, -1"
    (encodeI defs .ADDI ⟨5, by omega⟩ ⟨0, by omega⟩ (-1))
    (fun d => d.opType == .ADDI && d.imm == some (-1))

/-- S-type: SW x5, 12(x2) and its negative twin -/
def testRoundTripS (defs : List InstructionDef) : IO Unit := do
  checkRoundTrip defs "S-type SW x5, 12(x2)"
    (encodeS defs .SW ⟨2, by omega⟩ ⟨5, by omega⟩ 12)
    (fun d => d.opType == .SW && d.rs1 == some ⟨2, by omega⟩ &&
              d.rs2 == some ⟨5, by omega⟩ && d.imm == some 12)
  checkRoundTrip defs "S-type SW x5, -4(x2)"
    (encodeS defs .SW ⟨2, by omega⟩ ⟨5, by omega⟩ (-4))
    (fun d => d.opType == .SW && d.imm == some (-4))

/-- B-type: BEQ x1, x2, 16 and its negative twin -/
def testRoundTripB (defs : List InstructionDef) : IO Unit := do
  checkRoundTrip defs "B-type BEQ x1, x2, 16"
    (encodeB defs .BEQ ⟨1, by omega⟩ ⟨2, by omega⟩ 16)
    (fun d => d.opType == .BEQ && d.rs1 == some ⟨1, by omega⟩ &&
              d.rs2 == some ⟨2, by omega⟩ && d.imm == some 16)
  checkRoundTrip defs "B-type BEQ x1, x2, -16"
    (encodeB defs .BEQ ⟨1, by omega⟩ ⟨2, by omega⟩ (-16))
    (fun d => d.opType == .BEQ && d.imm == some (-16))

/-- U-type: LUI x5, 0x12345000 -/
def testRoundTripU (defs : List InstructionDef) : IO Unit :=
  checkRoundTrip defs "U-type LUI x5, 0x12345000"
    (encodeU defs .LUI ⟨5, by omega⟩ 0x12345000)
    (fun d => d.opType == .LUI && d.rd == some ⟨5, by omega⟩ &&
              d.imm == some 0x12345000)

/-- J-type: JAL x1, 20 and its negative twin -/
def testRoundTripJ (defs : List InstructionDef) : IO Unit := do
  checkRoundTrip defs "J-type JAL x1, 20"
    (encodeJ defs .JAL ⟨1, by omega⟩ 20)
    (fun d => d.opType == .JAL && d.rd == some ⟨1, by omega⟩ && d.imm == some 20)
  checkRoundTrip defs "J-type JAL x1, -20"
    (encodeJ defs .JAL ⟨1, by omega⟩ (-20))
    (fun d => d.opType == .JAL && d.imm == some (-20))

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
