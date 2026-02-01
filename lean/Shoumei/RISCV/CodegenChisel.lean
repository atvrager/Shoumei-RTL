/-
  Chisel Code Generator for RV32I Decoder

  Generates Chisel (Scala) decoder module from
  instruction definitions parsed from riscv-opcodes.
-/

import Shoumei.RISCV.ISA
import Shoumei.RISCV.Decoder

namespace Shoumei.RISCV

/-! ## Helper Functions for Chisel Code Generation -/

/-- Convert Nat to hexadecimal string -/
private def natToHex (n : Nat) : String :=
  let rec aux (n : Nat) (acc : String) : String :=
    if h : n == 0 then
      if acc.isEmpty then "0" else acc
    else
      have hn : n > 0 := by
        cases n with
        | zero => contradiction
        | succ n' => omega
      have : n / 16 < n := Nat.div_lt_self hn (by decide : 1 < 16)
      let digit := n % 16
      let hexChar := if digit < 10 then
        Char.ofNat (digit + 48)  -- '0' to '9'
      else
        Char.ofNat (digit - 10 + 97)  -- 'a' to 'f'
      aux (n / 16) (String.ofList [hexChar] ++ acc)
    termination_by n
  aux n ""

/-- Generate Chisel identifier (sanitize for Scala) -/
def sanitizeChiselIdentifier (name : String) : String :=
  name.toUpper.replace "." "_"

/-- Generate OpType enum declaration for Chisel -/
def genChiselOpTypeEnum (defs : List InstructionDef) : String :=
  let opcodes := defs.map (fun instrDef => "  val " ++ sanitizeChiselIdentifier instrDef.name ++ " = Value")
  let enumItems := String.intercalate "\n" opcodes
  "object OpType extends ChiselEnum {\n" ++ enumItems ++ "\n}"

/-- Generate immediate extraction logic for Chisel -/
def genChiselImmediateExtractor (immType : String) : String :=
  match immType with
  | "I" =>
    "  val immI = Cat(Fill(20, instr(31)), instr(31, 20)).asSInt"
  | "S" =>
    "  val immS = Cat(Fill(20, instr(31)), instr(31, 25), instr(11, 7)).asSInt"
  | "B" =>
    "  val immB = Cat(Fill(19, instr(31)), instr(31), instr(7), instr(30, 25), instr(11, 8), 0.U(1.W)).asSInt"
  | "U" =>
    "  val immU = Cat(instr(31, 12), 0.U(12.W)).asSInt"
  | "J" =>
    "  val immJ = Cat(Fill(11, instr(31)), instr(31), instr(19, 12), instr(20), instr(30, 21), 0.U(1.W)).asSInt"
  | _ => ""

/-- Generate decoder case for one instruction (Chisel) -/
def genChiselDecoderCase (instrDef : InstructionDef) : String :=
  let maskHex := "\"h" ++ natToHex instrDef.maskBits.toNat ++ "\""
  let matchHex := "\"h" ++ natToHex instrDef.matchBits.toNat ++ "\""
  let opName := sanitizeChiselIdentifier instrDef.name
  "    .elsewhen((instr & " ++ maskHex ++ ".U) === " ++ matchHex ++ ".U) {\n      io.optype := OpType." ++ opName ++ "\n      io.valid := true.B\n    }"

/-- Generate complete Chisel decoder module -/
def genChiselDecoder (defs : List InstructionDef) : String :=
  let header :=
"//==============================================================================
// RV32I Instruction Decoder
// Generated from riscv-opcodes definitions
//
// This module decodes 32-bit RISC-V instructions and extracts:
// - Operation type (OpType enum)
// - Register operands (rd, rs1, rs2)
// - Immediate values (sign-extended to 32 bits)
//==============================================================================

package shoumei.riscv

import chisel3._
import chisel3.util._

"

  let enumDecl := genChiselOpTypeEnum defs

  let bundleDecl :=
"

class DecoderIO extends Bundle {
  val instr  = Input(UInt(32.W))    // 32-bit instruction word
  val optype = Output(OpType())     // Decoded operation type
  val rd     = Output(UInt(5.W))    // Destination register
  val rs1    = Output(UInt(5.W))    // Source register 1
  val rs2    = Output(UInt(5.W))    // Source register 2
  val imm    = Output(SInt(32.W))   // Immediate value (sign-extended)
  val valid  = Output(Bool())       // Instruction is valid RV32I
}

class RV32IDecoder extends RawModule {
  val io = IO(new DecoderIO)

  val instr = io.instr

  // Extract register fields
  io.rd  := instr(11, 7)
  io.rs1 := instr(19, 15)
  io.rs2 := instr(24, 20)

  // Extract immediate values for each format
"

  let immExtractors := String.intercalate "\n" [
    genChiselImmediateExtractor "I",
    genChiselImmediateExtractor "S",
    genChiselImmediateExtractor "B",
    genChiselImmediateExtractor "U",
    genChiselImmediateExtractor "J"
  ]

  let defaultOp := match defs.head? with
    | some firstDef => sanitizeChiselIdentifier firstDef.name
    | none => "ADD"  -- Fallback (should never happen with RV32I)

  let decoderLogic :=
"

  // Default: invalid instruction
  io.optype := OpType." ++ defaultOp ++ "
  io.imm := 0.S
  io.valid := false.B

  // Decode instruction using mask/match patterns
  when(false.B) {
    // Placeholder
  }"

  let decoderCases := String.intercalate "\n" (defs.map genChiselDecoderCase)

  let immMux :=
"

  // Select appropriate immediate based on instruction format
  switch(instr(6, 0)) {
    is(\"b0010011\".U, \"b0000011\".U, \"b1100111\".U) { io.imm := immI }  // I-type
    is(\"b0100011\".U)                                 { io.imm := immS }  // S-type
    is(\"b1100011\".U)                                 { io.imm := immB }  // B-type
    is(\"b0110111\".U, \"b0010111\".U)                { io.imm := immU }  // U-type
    is(\"b1101111\".U)                                 { io.imm := immJ }  // J-type
  }
}
"

  String.intercalate "\n" [
    header,
    enumDecl,
    bundleDecl,
    immExtractors,
    decoderLogic,
    decoderCases,
    immMux
  ]

/-- Write Chisel decoder to file -/
def writeChiselDecoder (defs : List InstructionDef) (outputPath : String) : IO Unit := do
  let chiselCode := genChiselDecoder defs
  IO.FS.writeFile outputPath chiselCode
  IO.println s!"Generated Chisel decoder: {outputPath}"

end Shoumei.RISCV
