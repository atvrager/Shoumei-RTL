/-
  SystemVerilog Code Generator for RISC-V Decoder

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
  let width := if defs.length > 64 then 7 else 6
  s!"typedef enum logic [{width - 1}:0] \{\n    " ++ enumItems ++ "\n} " ++ moduleName.toLower ++ "_optype_t;"

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

/-- Check if decoder includes F-extension instructions -/
private def hasF (defs : List InstructionDef) : Bool :=
  defs.any (fun d => d.extension.any (· == "rv_f"))

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

  let hasM := hasM defs
  let hasF := hasF defs
  let hasTrailingPorts := hasM || hasF

  let muldivComma := if hasF then "," else ""
  let muldivPort := if hasM then
    s!"\n    output logic        io_is_muldiv{muldivComma}  // M-extension multiply/divide" else ""

  let fpPorts := if hasF then
    "\n    output logic [4:0]  io_rs3,        // Source register 3 (R4-type, bits 31:27)" ++
    "\n    output logic [2:0]  io_rm,         // Rounding mode (bits 14:12)" ++
    "\n    output logic        io_is_fp,      // FP arithmetic (dispatch to FP RS)" ++
    "\n    output logic        io_has_fp_rd,  // Writes FP register file" ++
    "\n    output logic        io_fp_rs1_read, // rs1 from FP register file" ++
    "\n    output logic        io_fp_rs2_read, // rs2 from FP register file" ++
    "\n    output logic        io_fp_rs3_used, // Needs rs3 (R4-type fused ops)" ++
    "\n    output logic        io_is_fp_load, // FP load (FLW)" ++
    "\n    output logic        io_is_fp_store // FP store (FSW)"
  else ""

  -- Determine comma/no-comma for io_use_imm line
  let useImmComma := if hasTrailingPorts then "," else ""

  let moduleDecl :=
s!"
module {moduleName} (
    input  logic [31:0] io_instr,      // 32-bit instruction word
    output logic [{if hasF then "6" else "5"}:0]  io_optype,     // Decoded operation type
    output logic [4:0]  io_rd,         // Destination register
    output logic [4:0]  io_rs1,        // Source register 1
    output logic [4:0]  io_rs2,        // Source register 2
    output logic [31:0] io_imm,        // Immediate value (sign-extended)
    output logic        io_valid,      // Instruction is valid
    output logic        io_has_rd,     // Instruction writes a register
    output logic        io_is_integer, // Dispatch to integer ALU
    output logic        io_is_memory,  // Dispatch to load/store unit
    output logic        io_is_branch,  // Dispatch to branch unit
    output logic        io_is_store,   // Instruction is a store (SB/SH/SW/FSW)
    output logic        io_use_imm{useImmComma}    // Instruction uses immediate (not R-type)" ++ muldivPort ++ fpPorts ++ "
);

// Extract register fields
assign io_rd  = io_instr[11:7];
assign io_rs1 = io_instr[19:15];
assign io_rs2 = io_instr[24:20];
" ++ (if hasF then "assign io_rs3 = io_instr[31:27];\nassign io_rm  = io_instr[14:12];\n" else "") ++ "
// Extract immediate values for each format
logic [31:0] imm_i, imm_s, imm_b, imm_u, imm_j;
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

  let muldivClassify := if hasM then
    "\n// MulDiv: R-type (0110011) with funct7[0]=1 (M-extension encoding)\nassign io_is_muldiv = io_valid && (io_instr[6:0] == 7'b0110011) && io_instr[25];"
  else ""

  let integerMuldivExclude := if hasM then " && !io_instr[25]" else ""

  -- FP load/store immediate mux entries
  let fpImmMux := if hasF then
    "\n        7'b0000111:                          io_imm = imm_i;  // FLW (I-type)" ++
    "\n        7'b0100111:                          io_imm = imm_s;  // FSW (S-type)"
  else ""

  -- Memory classification: include FLW/FSW opcodes when F present
  let fpMemory := if hasF then
    " ||\n    (io_instr[6:0] == 7'b0000111) ||  // FLW\n    (io_instr[6:0] == 7'b0100111)     // FSW"
  else ""

  -- Store classification: include FSW
  let fpStore := if hasF then
    " || (io_instr[6:0] == 7'b0100111)" else ""

  -- has_rd: FSW doesn't write rd; FP ops that write FP rd still have has_rd=1 (for ROB tracking)
  -- Add FSW to exclusion list
  let fpHasRdExclude := if hasF then
    " &&\n    (io_instr[6:0] != 7'b0100111)" else ""

  let fpClassify := if hasF then
    "\n\n// FP classification outputs" ++
    "\n// is_fp: OP-FP (1010011), FMADD (1000011), FMSUB (1000111), FNMADD (1001011), FNMSUB (1001111)" ++
    "\nassign io_is_fp = io_valid && (" ++
    "\n    (io_instr[6:0] == 7'b1010011) ||  // OP-FP (FADD, FSUB, FMUL, etc.)" ++
    "\n    (io_instr[6:0] == 7'b1000011) ||  // FMADD" ++
    "\n    (io_instr[6:0] == 7'b1000111) ||  // FMSUB" ++
    "\n    (io_instr[6:0] == 7'b1001011) ||  // FNMADD" ++
    "\n    (io_instr[6:0] == 7'b1001111)     // FNMSUB" ++
    "\n);" ++
    "\n" ++
    "\n// has_fp_rd: FP arithmetic + fused + sign-inject + min/max + FCVT_S_W/WU + FMV_W_X + FLW" ++
    "\n// Excludes: FEQ/FLT/FLE, FCVT_W_S/WU_S, FMV_X_W, FCLASS (write int rd)" ++
    "\nassign io_has_fp_rd = io_valid && (" ++
    "\n    (io_instr[6:0] == 7'b1000011) ||  // FMADD" ++
    "\n    (io_instr[6:0] == 7'b1000111) ||  // FMSUB" ++
    "\n    (io_instr[6:0] == 7'b1001011) ||  // FNMADD" ++
    "\n    (io_instr[6:0] == 7'b1001111) ||  // FNMSUB" ++
    "\n    (io_instr[6:0] == 7'b0000111) ||  // FLW" ++
    "\n    (io_instr[6:0] == 7'b1010011 &&   // OP-FP, but NOT compare/classify/FP->int" ++
    "\n     io_instr[31:27] != 5'b10100 &&   // not FCMP (FEQ/FLT/FLE)" ++
    "\n     io_instr[31:27] != 5'b11000 &&   // not FCVT.W.S / FCVT.WU.S" ++
    "\n     io_instr[31:27] != 5'b11100)     // not FMV.X.W / FCLASS" ++
    "\n);" ++
    "\n" ++
    "\n// fp_rs1_read: all OP-FP ops read FP rs1 EXCEPT FCVT.S.W/WU and FMV.W.X (read int rs1)" ++
    "\n// Also: fused ops (FMADD/FMSUB/FNMADD/FNMSUB), FSW reads FP rs1 as store data addr is int" ++
    "\n// Wait - FSW uses int rs1 for address. FSW reads FP rs2 for store data." ++
    "\n// FLW uses int rs1 for address, no FP rs1." ++
    "\nassign io_fp_rs1_read = io_valid && (" ++
    "\n    (io_instr[6:0] == 7'b1000011) ||  // FMADD" ++
    "\n    (io_instr[6:0] == 7'b1000111) ||  // FMSUB" ++
    "\n    (io_instr[6:0] == 7'b1001011) ||  // FNMADD" ++
    "\n    (io_instr[6:0] == 7'b1001111) ||  // FNMSUB" ++
    "\n    (io_instr[6:0] == 7'b1010011 &&   // OP-FP, excluding int→FP moves/converts" ++
    "\n     io_instr[31:27] != 5'b11010 &&   // not FCVT.S.W/WU (int rs1)" ++
    "\n     io_instr[31:27] != 5'b11110)     // not FMV.W.X (int rs1)" ++
    "\n);" ++
    "\n" ++
    "\n// fp_rs2_read: FP arithmetic with 2 FP sources, fused ops, compare, sign-inject, min/max, FSW" ++
    "\nassign io_fp_rs2_read = io_valid && (" ++
    "\n    (io_instr[6:0] == 7'b0100111) ||  // FSW (store data from FP rs2)" ++
    "\n    (io_instr[6:0] == 7'b1000011) ||  // FMADD" ++
    "\n    (io_instr[6:0] == 7'b1000111) ||  // FMSUB" ++
    "\n    (io_instr[6:0] == 7'b1001011) ||  // FNMADD" ++
    "\n    (io_instr[6:0] == 7'b1001111) ||  // FNMSUB" ++
    "\n    (io_instr[6:0] == 7'b1010011 &&   // OP-FP 2-source ops" ++
    "\n     (io_instr[31:27] == 5'b00000 ||  // FADD" ++
    "\n      io_instr[31:27] == 5'b00001 ||  // FSUB" ++
    "\n      io_instr[31:27] == 5'b00010 ||  // FMUL
      io_instr[31:27] == 5'b00011 ||  // FDIV" ++
    "\n      io_instr[31:27] == 5'b10100 ||  // FCMP (FEQ/FLT/FLE)" ++
    "\n      io_instr[31:27] == 5'b00100 ||  // FSGNJ/FSGNJN/FSGNJX" ++
    "\n      io_instr[31:27] == 5'b00101))   // FMIN/FMAX" ++
    "\n);" ++
    "\n" ++
    "\n// fp_rs3_used: R4-type fused ops only (FMADD, FMSUB, FNMADD, FNMSUB)" ++
    "\nassign io_fp_rs3_used = io_valid && (" ++
    "\n    (io_instr[6:0] == 7'b1000011) ||  // FMADD" ++
    "\n    (io_instr[6:0] == 7'b1000111) ||  // FMSUB" ++
    "\n    (io_instr[6:0] == 7'b1001011) ||  // FNMADD" ++
    "\n    (io_instr[6:0] == 7'b1001111)     // FNMSUB" ++
    "\n);" ++
    "\n" ++
    "\n// FP load (FLW): I-type, opcode 0000111" ++
    "\nassign io_is_fp_load = io_valid && (io_instr[6:0] == 7'b0000111);" ++
    "\n" ++
    "\n// FP store (FSW): S-type, opcode 0100111" ++
    "\nassign io_is_fp_store = io_valid && (io_instr[6:0] == 7'b0100111);"
  else ""

  let immMux :=
"
    // Select appropriate immediate based on instruction format
    casez (io_instr[6:0])
        7'b0010011, 7'b0000011, 7'b1100111, 7'b1110011: io_imm = imm_i;  // I-type (ALU-I, LOAD, JALR, SYSTEM/CSR)" ++ fpImmMux ++ "
        7'b0100011:                          io_imm = imm_s;  // S-type (STORE)" ++ (if hasF then "\n        7'b0100111:                          io_imm = imm_s;  // FSW (S-type)" else "") ++ "
        7'b1100011:                          io_imm = imm_b;  // B-type (BRANCH)
        7'b0110111, 7'b0010111:              io_imm = imm_u;  // U-type (LUI, AUIPC)
        7'b1101111:                          io_imm = imm_j;  // J-type (JAL)
        default:                             io_imm = 32'b0;
    endcase
end

// Dispatch classification (active only when instruction is valid)
// has_rd: all instructions except stores, branches, FENCE, and non-CSR SYSTEM (ECALL/EBREAK/MRET)
// Note: ECALL/EBREAK/MRET all have rd=x0, caught by the rd!=x0 check.
// CSR instructions (SYSTEM with funct3!=0) DO write to rd.
assign io_has_rd = io_valid &&
    (io_instr[11:7] != 5'b00000) &&   // not rd=x0 (writes to x0 are discarded)
    (io_instr[6:0] != 7'b0100011) &&  // not STORE
    (io_instr[6:0] != 7'b1100011) &&  // not BRANCH
    (io_instr[6:0] != 7'b0001111)" ++ fpHasRdExclude ++ ";  // not FENCE

// Integer: R-type ALU (0110011, excluding M-ext), I-type ALU (0010011), LUI (0110111), AUIPC (0010111)
assign io_is_integer = io_valid && (
    (io_instr[6:0] == 7'b0110011" ++ integerMuldivExclude ++ ") ||  // R-type (ADD, SUB, AND, etc.)
    (io_instr[6:0] == 7'b0010011) ||  // I-type (ADDI, ANDI, etc.)
    (io_instr[6:0] == 7'b0110111) ||  // LUI
    (io_instr[6:0] == 7'b0010111)     // AUIPC
);

// Memory: LOAD (0000011) and STORE (0100011)" ++ (if hasF then " + FLW (0000111) + FSW (0100111)" else "") ++ "
assign io_is_memory = io_valid && (
    (io_instr[6:0] == 7'b0000011) ||  // LOAD (LB, LH, LW, LBU, LHU)
    (io_instr[6:0] == 7'b0100011)" ++ fpMemory ++ "     // STORE (SB, SH, SW)
);

// Branch: BRANCH (1100011), JAL (1101111), JALR (1100111)
assign io_is_branch = io_valid && (
    (io_instr[6:0] == 7'b1100011) ||  // BRANCH (BEQ, BNE, BLT, BGE, etc.)
    (io_instr[6:0] == 7'b1101111) ||  // JAL
    (io_instr[6:0] == 7'b1100111)     // JALR
);

// Store: STORE (0100011)" ++ (if hasF then " + FSW (0100111)" else "") ++ "
assign io_is_store = io_valid && (io_instr[6:0] == 7'b0100011" ++ fpStore ++ ");

// Use immediate: all instructions except R-type (OP = 0110011) and branches (OP = 1100011)" ++ (if hasF then " and OP-FP/fused" else "") ++ "
assign io_use_imm = io_valid && (io_instr[6:0] != 7'b0110011) && (io_instr[6:0] != 7'b1100011)" ++ (if hasF then " && (io_instr[6:0] != 7'b1010011) && (io_instr[6:0] != 7'b1000011) && (io_instr[6:0] != 7'b1000111) && (io_instr[6:0] != 7'b1001011) && (io_instr[6:0] != 7'b1001111)" else "") ++ ";" ++
muldivClassify ++ fpClassify ++ "

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
