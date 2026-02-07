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
  "    .elsewhen((instr & " ++ maskHex ++ ".U) === " ++ matchHex ++ ".U) {\n      io_optype := OpType." ++ opName ++ ".asUInt\n      io_valid := true.B\n    }"

/-- Check if decoder includes M-extension instructions (Chisel) -/
private def hasMChisel (defs : List InstructionDef) : Bool :=
  defs.any (fun d => d.extension.any (· == "rv_m"))

/-- Generate complete Chisel decoder module -/
private def ceilLog2 (n : Nat) : Nat :=
  if n <= 2 then 1
  else if n <= 4 then 2
  else if n <= 8 then 3
  else if n <= 16 then 4
  else if n <= 32 then 5
  else if n <= 64 then 6
  else if n <= 128 then 7
  else 8

def genChiselDecoder (defs : List InstructionDef) (moduleName : String := "RV32IDecoder") : String :=
  -- Derive unique package name per decoder to avoid OpType conflicts
  let packageName := "shoumei.riscv." ++ moduleName.toLower
  let optypeWidth := ceilLog2 defs.length
  let header :=
s!"//==============================================================================
// {moduleName} - Instruction Decoder
// Generated from riscv-opcodes definitions
//
// This module decodes 32-bit RISC-V instructions and extracts:
// - Operation type (OpType enum)
// - Register operands (rd, rs1, rs2)
// - Immediate values (sign-extended to 32 bits)
// - has_rd: whether the instruction writes a register
// - Dispatch classification: is_integer, is_memory, is_branch, is_muldiv
//==============================================================================

package {packageName}

import chisel3._
import chisel3.util._

"

  let enumDecl := genChiselOpTypeEnum defs

  let muldivPort := if hasMChisel defs then
    "  val io_is_muldiv  = IO(Output(Bool()))       // M-extension multiply/divide\n" else ""

  let moduleDecl :=
    "\n\nclass " ++ moduleName ++ " extends RawModule {\n" ++
    "  val io_instr      = IO(Input(UInt(32.W)))    // 32-bit instruction word\n" ++
    "  val io_optype     = IO(Output(UInt(" ++ toString optypeWidth ++ ".W)))     // Decoded operation type\n" ++
    "  val io_rd         = IO(Output(UInt(5.W)))    // Destination register\n" ++
    "  val io_rs1        = IO(Output(UInt(5.W)))    // Source register 1\n" ++
    "  val io_rs2        = IO(Output(UInt(5.W)))    // Source register 2\n" ++
    "  val io_imm        = IO(Output(SInt(32.W)))   // Immediate value (sign-extended)\n" ++
    "  val io_valid      = IO(Output(Bool()))       // Instruction is valid\n" ++
    "  val io_has_rd     = IO(Output(Bool()))       // Instruction writes a register\n" ++
    "  val io_is_integer = IO(Output(Bool()))       // Dispatch to integer ALU\n" ++
    "  val io_is_memory  = IO(Output(Bool()))       // Dispatch to load/store unit\n" ++
    "  val io_is_branch  = IO(Output(Bool()))       // Dispatch to branch unit\n" ++
    muldivPort ++
    "\n" ++
    "  val instr = io_instr\n" ++
    "  val opcode = instr(6, 0)\n\n" ++
    "  // Extract register fields\n" ++
    "  io_rd  := instr(11, 7)\n" ++
    "  io_rs1 := instr(19, 15)\n" ++
    "  io_rs2 := instr(24, 20)\n\n" ++
    "  // Extract immediate values for each format\n"

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
  io_optype := OpType." ++ defaultOp ++ ".asUInt
  io_imm := 0.S
  io_valid := false.B

  // Decode instruction using mask/match patterns
  when(false.B) {
    // Placeholder
  }"

  let decoderCases := String.intercalate "\n" (defs.map genChiselDecoderCase)

  let muldivClassify := if hasMChisel defs then
    "\n  io_is_muldiv  := io_valid && (opcode === \"b0110011\".U) && instr(25)" else ""

  let integerMuldivExclude := if hasMChisel defs then " && !instr(25)" else ""

  let immMux :=
"

  // Select appropriate immediate based on instruction format
  switch(opcode) {
    is(\"b0010011\".U, \"b0000011\".U, \"b1100111\".U) { io_imm := immI }  // I-type
    is(\"b0100011\".U)                                 { io_imm := immS }  // S-type
    is(\"b1100011\".U)                                 { io_imm := immB }  // B-type
    is(\"b0110111\".U, \"b0010111\".U)                { io_imm := immU }  // U-type
    is(\"b1101111\".U)                                 { io_imm := immJ }  // J-type
  }

  // Dispatch classification
  io_has_rd := io_valid &&
    (opcode =/= \"b0100011\".U) &&  // not STORE
    (opcode =/= \"b1100011\".U) &&  // not BRANCH
    (opcode =/= \"b0001111\".U) &&  // not FENCE
    (opcode =/= \"b1110011\".U)     // not ECALL/EBREAK

  io_is_integer := io_valid && (
    (opcode === \"b0110011\".U" ++ integerMuldivExclude ++ ") ||  // R-type
    (opcode === \"b0010011\".U) ||  // I-type ALU
    (opcode === \"b0110111\".U) ||  // LUI
    (opcode === \"b0010111\".U)     // AUIPC
  )

  io_is_memory := io_valid && (
    (opcode === \"b0000011\".U) ||  // LOAD
    (opcode === \"b0100011\".U)     // STORE
  )

  io_is_branch := io_valid && (
    (opcode === \"b1100011\".U) ||  // BRANCH
    (opcode === \"b1101111\".U) ||  // JAL
    (opcode === \"b1100111\".U)     // JALR
  )
" ++ muldivClassify ++ "
}
"

  String.intercalate "\n" [
    header,
    enumDecl,
    moduleDecl,
    immExtractors,
    decoderLogic,
    decoderCases,
    immMux
  ]

/-- Write Chisel decoder to file -/
def writeChiselDecoder (defs : List InstructionDef) (outputPath : String) (moduleName : String := "RV32IDecoder") : IO Unit := do
  let chiselCode := genChiselDecoder defs moduleName
  IO.FS.writeFile outputPath chiselCode
  IO.println s!"Generated Chisel decoder: {outputPath}"

end Shoumei.RISCV
