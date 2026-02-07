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
      aux (n / 16) (String.ofList [hexChar] ++ acc)
    termination_by n
  aux n ""

/-- Generate SystemVerilog identifier (sanitize special characters) -/
def sanitizeSVIdentifier (name : String) : String :=
  name.toUpper.replace "." "_"

/-- Generate OpType enum declaration (scoped by module name to avoid conflicts) -/
def genOpTypeEnum (defs : List InstructionDef) (moduleName : String := "RV32IDecoder") : String :=
  let pfx := moduleName.toLower ++ "_"
  let opcodes := defs.map (fun instrDef => pfx ++ sanitizeSVIdentifier instrDef.name)
  let enumItems := String.intercalate (",\n    ") opcodes
  "typedef enum logic [5:0] {\n    " ++ enumItems ++ "\n} " ++ moduleName.toLower ++ "_optype_t;"

/-- Generate immediate extraction logic for one type -/
def genImmediateExtractor (immType : String) : String :=
  match immType with
  | "I" =>
    "assign imm_i = {{20{io_instr[31]}}, io_instr[31:20]};"
  | "S" =>
    "assign imm_s = {{20{io_instr[31]}}, io_instr[31:25], io_instr[11:7]};"
  | "B" =>
    "assign imm_b = {{19{io_instr[31]}}, io_instr[31], io_instr[7], io_instr[30:25], io_instr[11:8], 1'b0};"
  | "U" =>
    "assign imm_u = {io_instr[31:12], 12'b0};"
  | "J" =>
    "assign imm_j = {{11{io_instr[31]}}, io_instr[31], io_instr[19:12], io_instr[20], io_instr[30:21], 1'b0};"
  | _ => ""

/-- Generate decoder case for one instruction -/
def genDecoderCase (instrDef : InstructionDef) (pfx : String := "") : String :=
  let maskHex := "32'h" ++ natToHex instrDef.maskBits.toNat
  let matchHex := "32'h" ++ natToHex instrDef.matchBits.toNat
  let opName := pfx ++ sanitizeSVIdentifier instrDef.name
  "        if ((io_instr & " ++ maskHex ++ ") == " ++ matchHex ++ ") begin\n            io_optype = " ++ opName ++ ";\n            io_valid = 1'b1;\n        end"

/-- Check if decoder includes M-extension instructions -/
private def hasM (defs : List InstructionDef) : Bool :=
  defs.any (fun d => d.extension.any (· == "rv_m"))

/-- Generate complete SystemVerilog decoder module -/
def genSystemVerilogDecoder (defs : List InstructionDef) (moduleName : String := "RV32IDecoder") : String :=
  let header :=
s!"//==============================================================================
// {moduleName} - Instruction Decoder
// Generated from riscv-opcodes definitions
//
// This module decodes 32-bit RISC-V instructions and extracts:
// - Operation type (optype_t enum)
// - Register operands (rd, rs1, rs2)
// - Immediate values (sign-extended to 32 bits)
// - has_rd: whether the instruction writes a register
// - Dispatch classification: is_integer, is_memory, is_branch, is_muldiv
//==============================================================================

"

  let enumDecl := genOpTypeEnum defs moduleName
  let enumPfx := moduleName.toLower ++ "_"

  let muldivPort := if hasM defs then
    "\n    output logic        io_is_muldiv   // M-extension multiply/divide" else ""

  let moduleDecl :=
s!"
module {moduleName} (
    input  logic [31:0] io_instr,      // 32-bit instruction word
    output logic [5:0]  io_optype,     // Decoded operation type
    output logic [4:0]  io_rd,         // Destination register
    output logic [4:0]  io_rs1,        // Source register 1
    output logic [4:0]  io_rs2,        // Source register 2
    output logic [31:0] io_imm,        // Immediate value (sign-extended)
    output logic        io_valid,      // Instruction is valid
    output logic        io_has_rd,     // Instruction writes a register
    output logic        io_is_integer, // Dispatch to integer ALU
    output logic        io_is_memory,  // Dispatch to load/store unit
    output logic        io_is_branch,  // Dispatch to branch unit
    output logic        io_is_store,   // Instruction is a store (SB/SH/SW)
    output logic        io_use_imm{if hasM defs then "," else ""}    // Instruction uses immediate (not R-type)" ++ muldivPort ++ "
);

// Extract register fields
assign io_rd  = io_instr[11:7];
assign io_rs1 = io_instr[19:15];
assign io_rs2 = io_instr[24:20];

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
    | some firstDef => enumPfx ++ sanitizeSVIdentifier firstDef.name
    | none => "add"  -- Fallback (should never happen with RV32I)

  let decoderLogic :=
"
// Decode instruction using mask/match patterns
always_comb begin
    // Default: invalid instruction
    io_optype = " ++ defaultOp ++ ";
    io_imm = 32'b0;
    io_valid = 1'b0;

    // Check each instruction pattern
"

  let decoderCases := String.intercalate "\n" (defs.map fun d => genDecoderCase d enumPfx)

  let muldivClassify := if hasM defs then
    "\n// MulDiv: R-type (0110011) with funct7[0]=1 (M-extension encoding)\nassign io_is_muldiv = io_valid && (io_instr[6:0] == 7'b0110011) && io_instr[25];"
  else ""

  let integerMuldivExclude := if hasM defs then " && !io_instr[25]" else ""

  let immMux :=
"
    // Select appropriate immediate based on instruction format
    casez (io_instr[6:0])
        7'b0010011, 7'b0000011, 7'b1100111: io_imm = imm_i;  // I-type (ALU-I, LOAD, JALR)
        7'b0100011:                          io_imm = imm_s;  // S-type (STORE)
        7'b1100011:                          io_imm = imm_b;  // B-type (BRANCH)
        7'b0110111, 7'b0010111:              io_imm = imm_u;  // U-type (LUI, AUIPC)
        7'b1101111:                          io_imm = imm_j;  // J-type (JAL)
        default:                             io_imm = 32'b0;
    endcase
end

// Dispatch classification (active only when instruction is valid)
// has_rd: all instructions except stores, branches, and system (FENCE/ECALL/EBREAK)
assign io_has_rd = io_valid &&
    (io_instr[6:0] != 7'b0100011) &&  // not STORE
    (io_instr[6:0] != 7'b1100011) &&  // not BRANCH
    (io_instr[6:0] != 7'b0001111) &&  // not FENCE
    (io_instr[6:0] != 7'b1110011);    // not ECALL/EBREAK

// Integer: R-type ALU (0110011, excluding M-ext), I-type ALU (0010011), LUI (0110111), AUIPC (0010111)
assign io_is_integer = io_valid && (
    (io_instr[6:0] == 7'b0110011" ++ integerMuldivExclude ++ ") ||  // R-type (ADD, SUB, AND, etc.)
    (io_instr[6:0] == 7'b0010011) ||  // I-type (ADDI, ANDI, etc.)
    (io_instr[6:0] == 7'b0110111) ||  // LUI
    (io_instr[6:0] == 7'b0010111)     // AUIPC
);

// Memory: LOAD (0000011) and STORE (0100011)
assign io_is_memory = io_valid && (
    (io_instr[6:0] == 7'b0000011) ||  // LOAD (LB, LH, LW, LBU, LHU)
    (io_instr[6:0] == 7'b0100011)     // STORE (SB, SH, SW)
);

// Branch: BRANCH (1100011), JAL (1101111), JALR (1100111)
assign io_is_branch = io_valid && (
    (io_instr[6:0] == 7'b1100011) ||  // BRANCH (BEQ, BNE, BLT, BGE, etc.)
    (io_instr[6:0] == 7'b1101111) ||  // JAL
    (io_instr[6:0] == 7'b1100111)     // JALR
);

// Store: STORE (0100011)
assign io_is_store = io_valid && (io_instr[6:0] == 7'b0100011);

// Use immediate: all instructions except R-type (OP = 0110011) and R-type M-ext (same opcode)
assign io_use_imm = io_valid && (io_instr[6:0] != 7'b0110011);
" ++ muldivClassify ++ "

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
def writeSystemVerilogDecoder (defs : List InstructionDef) (outputPath : String) (moduleName : String := "RV32IDecoder") : IO Unit := do
  let svCode := genSystemVerilogDecoder defs moduleName
  IO.FS.writeFile outputPath svCode
  IO.println s!"Generated SystemVerilog decoder: {outputPath}"

end Shoumei.RISCV
