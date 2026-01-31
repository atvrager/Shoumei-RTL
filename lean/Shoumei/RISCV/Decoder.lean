/-
  RISC-V Instruction Decoder

  Decodes 32-bit instruction words into operation type and extracted fields.
  Uses mask/match patterns from instruction definitions.
-/

import Shoumei.RISCV.ISA
import Shoumei.RISCV.OpcodeParser

namespace Shoumei.RISCV

/-- Decoded instruction with operation type and extracted fields -/
structure DecodedInstruction where
  /-- Operation type (ADD, SUB, etc.) -/
  opType : OpType
  /-- Destination register (5 bits, bits 11:7) -/
  rd : Option (Fin 32)
  /-- Source register 1 (5 bits, bits 19:15) -/
  rs1 : Option (Fin 32)
  /-- Source register 2 (5 bits, bits 24:20) -/
  rs2 : Option (Fin 32)
  /-- Immediate value (sign-extended to 32 bits) -/
  imm : Option Int
  deriving Repr

/-- Extract a bit field from a 32-bit instruction word -/
def extractBits (instr : UInt32) (hi : Nat) (lo : Nat) : UInt32 :=
  let width := hi - lo + 1
  let mask : UInt32 := (1 <<< UInt32.ofNat width) - 1
  let shifted := instr >>> UInt32.ofNat lo
  shifted &&& mask

/-- Extract register field (5 bits) as Fin 32 -/
def extractReg (instr : UInt32) (hi : Nat) (lo : Nat) : Fin 32 :=
  ⟨(extractBits instr hi lo).toNat % 32, by omega⟩

/-- Extract rd field (bits 11:7) -/
def extractRd (instr : UInt32) : Fin 32 := extractReg instr 11 7

/-- Extract rs1 field (bits 19:15) -/
def extractRs1 (instr : UInt32) : Fin 32 := extractReg instr 19 15

/-- Extract rs2 field (bits 24:20) -/
def extractRs2 (instr : UInt32) : Fin 32 := extractReg instr 24 20

/-- Sign-extend a value from N bits to 32 bits -/
def signExtend (value : UInt32) (bits : Nat) : Int :=
  let signBitPos := bits - 1
  let signBit := (value >>> UInt32.ofNat signBitPos) &&& 1
  if signBit == 1 then
    -- Negative: set upper bits
    Int.ofNat value.toNat - Int.ofNat (1 <<< bits)
  else
    -- Positive
    Int.ofNat value.toNat

/-- Extract I-type immediate (bits 31:20, sign-extended) -/
def extractImmI (instr : UInt32) : Int :=
  signExtend (extractBits instr 31 20) 12

/-- Extract S-type immediate (bits 31:25 | 11:7, sign-extended) -/
def extractImmS (instr : UInt32) : Int :=
  let imm11_5 := extractBits instr 31 25
  let imm4_0 := extractBits instr 11 7
  let imm := (imm11_5 <<< UInt32.ofNat 5) ||| imm4_0
  signExtend imm 12

/-- Extract B-type immediate (bits for branch offset, sign-extended) -/
def extractImmB (instr : UInt32) : Int :=
  let imm12 := extractBits instr 31 31
  let imm10_5 := extractBits instr 30 25
  let imm4_1 := extractBits instr 11 8
  let imm11 := extractBits instr 7 7
  let imm := (imm12 <<< UInt32.ofNat 12) ||| (imm11 <<< UInt32.ofNat 11) |||
             (imm10_5 <<< UInt32.ofNat 5) ||| (imm4_1 <<< UInt32.ofNat 1)
  signExtend imm 13

/-- Extract U-type immediate (bits 31:12, shifted left by 12) -/
def extractImmU (instr : UInt32) : Int :=
  Int.ofNat ((extractBits instr 31 12) <<< UInt32.ofNat 12).toNat

/-- Extract J-type immediate (bits for jump offset, sign-extended) -/
def extractImmJ (instr : UInt32) : Int :=
  let imm20 := extractBits instr 31 31
  let imm10_1 := extractBits instr 30 21
  let imm11 := extractBits instr 20 20
  let imm19_12 := extractBits instr 19 12
  let imm := (imm20 <<< UInt32.ofNat 20) ||| (imm19_12 <<< UInt32.ofNat 12) |||
             (imm11 <<< UInt32.ofNat 11) ||| (imm10_1 <<< UInt32.ofNat 1)
  signExtend imm 21

/--
  Decode a 32-bit instruction word using a list of instruction definitions.
  Returns None if instruction doesn't match any definition.
-/
def decodeInstruction (defs : List InstructionDef) (instr : UInt32) : Option DecodedInstruction :=
  -- Find matching instruction definition
  let matchingDef := defs.find? (fun instrDef => instrDef.matches instr)

  matchingDef.map fun instrDef =>
    -- Extract fields based on variable_fields
    let hasRd := instrDef.variableFields.contains .rd
    let hasRs1 := instrDef.variableFields.contains .rs1
    let hasRs2 := instrDef.variableFields.contains .rs2

    -- Determine immediate type from variable fields
    let imm :=
      if instrDef.variableFields.contains .imm12 then
        some (extractImmI instr)
      else if instrDef.variableFields.contains .imm12hi || instrDef.variableFields.contains .imm12lo then
        some (extractImmS instr)
      else if instrDef.variableFields.contains .bimm12hi || instrDef.variableFields.contains .bimm12lo then
        some (extractImmB instr)
      else if instrDef.variableFields.contains .imm20 then
        some (extractImmU instr)
      else if instrDef.variableFields.contains .jimm20 then
        some (extractImmJ instr)
      else
        none

    {
      opType := instrDef.opType
      rd := if hasRd then some (extractRd instr) else none
      rs1 := if hasRs1 then some (extractRs1 instr) else none
      rs2 := if hasRs2 then some (extractRs2 instr) else none
      imm := imm
    }

/--
  Decoder test: decode sample instructions from various formats
-/
def testDecoder (defs : List InstructionDef) : IO Unit := do
  IO.println "Testing RISC-V decoder...\n"

  -- R-type: ADD x1, x2, x3 (0x003100b3)
  let addInstr : UInt32 := 0x003100b3
  match decodeInstruction defs addInstr with
  | some decoded =>
    IO.println s!"✓ ADD x1, x2, x3: op={decoded.opType}, rd={decoded.rd}, rs1={decoded.rs1}, rs2={decoded.rs2}"
  | none =>
    IO.println "✗ Failed to decode ADD"

  -- I-type: ADDI x5, x0, 42 (0x02a00293)
  let addiInstr : UInt32 := 0x02a00293
  match decodeInstruction defs addiInstr with
  | some decoded =>
    IO.println s!"✓ ADDI x5, x0, 42: op={decoded.opType}, rd={decoded.rd}, rs1={decoded.rs1}, imm={decoded.imm}"
  | none =>
    IO.println "✗ Failed to decode ADDI"

  -- Load: LW x10, 8(x2) (0x00812503)
  let lwInstr : UInt32 := 0x00812503
  match decodeInstruction defs lwInstr with
  | some decoded =>
    IO.println s!"✓ LW x10, 8(x2): op={decoded.opType}, rd={decoded.rd}, rs1={decoded.rs1}, imm={decoded.imm}"
  | none =>
    IO.println "✗ Failed to decode LW"

  -- Store: SW x5, 12(x2) (0x00512623)
  let swInstr : UInt32 := 0x00512623
  match decodeInstruction defs swInstr with
  | some decoded =>
    IO.println s!"✓ SW x5, 12(x2): op={decoded.opType}, rs1={decoded.rs1}, rs2={decoded.rs2}, imm={decoded.imm}"
  | none =>
    IO.println "✗ Failed to decode SW"

  -- Branch: BEQ x1, x2, 16 (0x00208863)
  let beqInstr : UInt32 := 0x00208863
  match decodeInstruction defs beqInstr with
  | some decoded =>
    IO.println s!"✓ BEQ x1, x2, 16: op={decoded.opType}, rs1={decoded.rs1}, rs2={decoded.rs2}, imm={decoded.imm}"
  | none =>
    IO.println "✗ Failed to decode BEQ"

  -- Jump: JAL x1, 20 (0x014000ef)
  let jalInstr : UInt32 := 0x014000ef
  match decodeInstruction defs jalInstr with
  | some decoded =>
    IO.println s!"✓ JAL x1, 20: op={decoded.opType}, rd={decoded.rd}, imm={decoded.imm}"
  | none =>
    IO.println "✗ Failed to decode JAL"

  -- U-type: LUI x5, 0x12345 (0x12345297)
  let luiInstr : UInt32 := 0x12345297
  match decodeInstruction defs luiInstr with
  | some decoded =>
    IO.println s!"✓ LUI x5, 0x12345: op={decoded.opType}, rd={decoded.rd}, imm={decoded.imm}"
  | none =>
    IO.println "✗ Failed to decode LUI"

  IO.println "\nDecoder test complete!"

end Shoumei.RISCV
