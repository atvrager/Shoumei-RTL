/-
  SystemVerilog Code Generator for RV32I Decoder

  Generates a synthesizable SystemVerilog decoder module from
  instruction definitions parsed from riscv-opcodes.
-/

import Shoumei.RISCV.ISA
import Shoumei.RISCV.Decoder

namespace Shoumei.RISCV

/-! ## Helper Functions for Code Generation -/

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
      aux (n / 16) (String.mk [hexChar] ++ acc)
    termination_by n
  aux n ""

/-- Generate SystemVerilog identifier (sanitize special characters) -/
def sanitizeSVIdentifier (name : String) : String :=
  name.toLower.replace "." "_"

/-- Generate OpType enum declaration -/
def genOpTypeEnum (defs : List InstructionDef) : String :=
  let opcodes := defs.map (fun instrDef => sanitizeSVIdentifier instrDef.name)
  let enumItems := String.intercalate (",\n    ") opcodes
  "typedef enum logic [5:0] {\n    " ++ enumItems ++ "\n} optype_t;"

/-- Generate immediate extraction logic for one type -/
def genImmediateExtractor (immType : String) : String :=
  match immType with
  | "I" =>
    "assign imm_i = {{20{instr[31]}}, instr[31:20]};"
  | "S" =>
    "assign imm_s = {{20{instr[31]}}, instr[31:25], instr[11:7]};"
  | "B" =>
    "assign imm_b = {{19{instr[31]}}, instr[31], instr[7], instr[30:25], instr[11:8], 1'b0};"
  | "U" =>
    "assign imm_u = {instr[31:12], 12'b0};"
  | "J" =>
    "assign imm_j = {{11{instr[31]}}, instr[31], instr[19:12], instr[20], instr[30:21], 1'b0};"
  | _ => ""

/-- Generate decoder case for one instruction -/
def genDecoderCase (instrDef : InstructionDef) : String :=
  let maskHex := "32'h" ++ natToHex instrDef.maskBits.toNat
  let matchHex := "32'h" ++ natToHex instrDef.matchBits.toNat
  let opName := sanitizeSVIdentifier instrDef.name
  "        if ((instr & " ++ maskHex ++ ") == " ++ matchHex ++ ") begin\n            optype = " ++ opName ++ ";\n            valid = 1'b1;\n        end"

/-- Generate complete SystemVerilog decoder module -/
def genSystemVerilogDecoder (defs : List InstructionDef) : String :=
  let header :=
"//==============================================================================
// RV32I Instruction Decoder
// Generated from riscv-opcodes definitions
//
// This module decodes 32-bit RISC-V instructions and extracts:
// - Operation type (optype_t enum)
// - Register operands (rd, rs1, rs2)
// - Immediate values (sign-extended to 32 bits)
//==============================================================================

"

  let enumDecl := genOpTypeEnum defs

  let moduleDecl :=
"
module rv32i_decoder (
    input  logic [31:0] instr,      // 32-bit instruction word
    output optype_t     optype,     // Decoded operation type
    output logic [4:0]  rd,         // Destination register
    output logic [4:0]  rs1,        // Source register 1
    output logic [4:0]  rs2,        // Source register 2
    output logic [31:0] imm,        // Immediate value (sign-extended)
    output logic        valid       // Instruction is valid RV32I
);

// Extract register fields
assign rd  = instr[11:7];
assign rs1 = instr[19:15];
assign rs2 = instr[24:20];

// Extract immediate values for each format
logic signed [31:0] imm_i, imm_s, imm_b, imm_u, imm_j;
"

  let immExtractors := String.intercalate "\n" [
    genImmediateExtractor "I",
    genImmediateExtractor "S",
    genImmediateExtractor "B",
    genImmediateExtractor "U",
    genImmediateExtractor "J"
  ]

  let defaultOp := match defs.head? with
    | some firstDef => sanitizeSVIdentifier firstDef.name
    | none => "add"  -- Fallback (should never happen with RV32I)

  let decoderLogic :=
"
// Decode instruction using mask/match patterns
always_comb begin
    // Default: invalid instruction
    optype = " ++ defaultOp ++ ";
    imm = 32'b0;
    valid = 1'b0;

    // Check each instruction pattern
"

  let decoderCases := String.intercalate "\n" (defs.map genDecoderCase)

  let immMux :=
"
    // Select appropriate immediate based on instruction format
    casez (instr[6:0])
        7'b0010011, 7'b0000011, 7'b1100111: imm = imm_i;  // I-type (ALU-I, LOAD, JALR)
        7'b0100011:                          imm = imm_s;  // S-type (STORE)
        7'b1100011:                          imm = imm_b;  // B-type (BRANCH)
        7'b0110111, 7'b0010111:              imm = imm_u;  // U-type (LUI, AUIPC)
        7'b1101111:                          imm = imm_j;  // J-type (JAL)
        default:                             imm = 32'b0;
    endcase
end

endmodule
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

/-- Write SystemVerilog decoder to file -/
def writeSystemVerilogDecoder (defs : List InstructionDef) (outputPath : String) : IO Unit := do
  let svCode := genSystemVerilogDecoder defs
  IO.FS.writeFile outputPath svCode
  IO.println s!"Generated SystemVerilog decoder: {outputPath}"

end Shoumei.RISCV
