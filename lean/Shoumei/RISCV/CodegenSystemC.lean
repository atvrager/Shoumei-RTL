/-
  SystemC Code Generator for RV32I Decoder

  Generates a SystemC simulation model from instruction definitions
  parsed from riscv-opcodes. Produces both .h (header) and .cpp files.

  Target: SystemC 2.3.3+ (ISO/IEC 1666-2011)
-/

import Shoumei.DSL
import Shoumei.RISCV.ISA
import Shoumei.RISCV.Decoder

namespace Shoumei.RISCV

/-! ## Helper Functions for SystemC Code Generation -/

/-- Convert Nat to hexadecimal string -/
private def natToHexSC (n : Nat) : String :=
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
        Char.ofNat (digit + 48)
      else
        Char.ofNat (digit - 10 + 97)
      aux (n / 16) (String.ofList [hexChar] ++ acc)
    termination_by n
  aux n ""

/-- Generate SystemC identifier (sanitize special characters) -/
def sanitizeSCIdentifier (name : String) : String :=
  name.toUpper.replace "." "_"

/-- Generate OpType enum declaration for SystemC -/
def genSCOpTypeEnum (defs : List InstructionDef) : String :=
  let opcodes := defs.map (fun instrDef => "  " ++ sanitizeSCIdentifier instrDef.name)
  let enumItems := String.intercalate ",\n" opcodes
  "enum optype_t {\n" ++ enumItems ++ "\n};"

/-- Generate decoder case for one instruction (SystemC) -/
def genSCDecoderCase (instrDef : InstructionDef) (isFirst : Bool) : String :=
  let maskHex := "0x" ++ natToHexSC instrDef.maskBits.toNat
  let matchHex := "0x" ++ natToHexSC instrDef.matchBits.toNat
  let opName := sanitizeSCIdentifier instrDef.name
  let pfx := if isFirst then "    if" else "    else if"
  pfx ++ " ((instr & " ++ maskHex ++ ") == " ++ matchHex ++ ") {\n" ++
  "      io_optype.write(" ++ opName ++ ");\n" ++
  "      io_valid.write(true);\n" ++
  "    }"

/-- Check if decoder includes M-extension instructions (SystemC) -/
private def hasMSC (defs : List InstructionDef) : Bool :=
  defs.any (fun d => d.extension.any (· == "rv_m"))

/-- Generate complete SystemC decoder header file (.h) -/
def genSystemCDecoderHeader (defs : List InstructionDef) (moduleName : String := "RV32IDecoder") : String :=
  let enumDecl := genSCOpTypeEnum defs
  let guardName := moduleName.toUpper ++ "_H"

  let muldivPort := if hasMSC defs then
    "\n  sc_out<bool>        io_is_muldiv;  // M-extension multiply/divide" else ""

  String.intercalate "\n" [
    "//==============================================================================",
    s!"// {moduleName} - Instruction Decoder - SystemC Model",
    "// Generated from riscv-opcodes definitions",
    "//==============================================================================",
    "",
    s!"#ifndef {guardName}",
    s!"#define {guardName}",
    "",
    "#include <systemc.h>",
    "",
    enumDecl,
    "",
    s!"SC_MODULE({moduleName}) " ++ "{",
    "  // Ports",
    "  sc_in<sc_uint<32>>  io_instr;      // 32-bit instruction word",
    "  sc_out<sc_uint<6>>  io_optype;     // Decoded operation type",
    "  sc_out<sc_uint<5>>  io_rd;         // Destination register",
    "  sc_out<sc_uint<5>>  io_rs1;        // Source register 1",
    "  sc_out<sc_uint<5>>  io_rs2;        // Source register 2",
    "  sc_out<sc_int<32>>  io_imm;        // Immediate value (sign-extended)",
    "  sc_out<bool>        io_valid;      // Instruction is valid",
    "  sc_out<bool>        io_has_rd;     // Instruction writes a register",
    "  sc_out<bool>        io_is_integer; // Dispatch to integer ALU",
    "  sc_out<bool>        io_is_memory;  // Dispatch to load/store unit",
    "  sc_out<bool>        io_is_branch;  // Dispatch to branch unit",
    "  sc_out<bool>        io_is_store;   // Instruction is a store",
    "  sc_out<bool>        io_use_imm;    // Uses immediate (not R-type)" ++ muldivPort,
    "",
    "  // Process methods",
    "  void comb_logic();",
    "",
    "  // Constructor",
    s!"  SC_CTOR({moduleName}) " ++ "{",
    "    SC_METHOD(comb_logic);",
    "    sensitive << io_instr;",
    "  }",
    "};",
    "",
    s!"#endif // {guardName}",
    ""
  ]

/-- Generate complete SystemC decoder implementation file (.cpp) -/
def genSystemCDecoderImpl (defs : List InstructionDef) (moduleName : String := "RV32IDecoder") : String :=
  let defaultOp := match defs.head? with
    | some firstDef => sanitizeSCIdentifier firstDef.name
    | none => "ADD"

  let decoderCases := defs.enum.map (fun ⟨idx, instrDef⟩ =>
    genSCDecoderCase instrDef (idx == 0))
  let decoderCasesStr := String.intercalate "\n" decoderCases

  String.intercalate "\n" [
    s!"#include \"{moduleName}.h\"",
    "",
    s!"void {moduleName}::comb_logic() " ++ "{",
    "  sc_uint<32> instr = io_instr.read();",
    "",
    "  // Extract register fields",
    "  io_rd.write(instr.range(11, 7));",
    "  io_rs1.write(instr.range(19, 15));",
    "  io_rs2.write(instr.range(24, 20));",
    "",
    "  // Extract immediate values for each format",
    "  sc_int<32> imm_i = (sc_int<32>)(((sc_int<32>)instr) >> 20);",
    "  sc_int<32> imm_s = (sc_int<32>)(((sc_int<32>)(instr & 0xfe000000)) >> 20) |",
    "                     (sc_int<32>)(instr.range(11, 7));",
    "  sc_int<32> imm_b = (sc_int<32>)(((sc_int<32>)(instr & 0x80000000)) >> 19) |",
    "                     (sc_int<32>)((instr[7] << 11) | (instr.range(30, 25) << 5) |",
    "                     (instr.range(11, 8) << 1));",
    "  sc_int<32> imm_u = (sc_int<32>)(instr & 0xfffff000);",
    "  sc_int<32> imm_j = (sc_int<32>)(((sc_int<32>)(instr & 0x80000000)) >> 11) |",
    "                     (sc_int<32>)((instr & 0x000ff000) | ((instr >> 9) & 0x800) |",
    "                     ((instr >> 20) & 0x7fe));",
    "",
    "  // Default: invalid instruction",
    s!"  io_optype.write({defaultOp});",
    "  io_imm.write(0);",
    "  io_valid.write(false);",
    "",
    "  // Decode instruction using mask/match patterns",
    decoderCasesStr,
    "",
    "  // Select appropriate immediate based on instruction format",
    "  sc_uint<7> opcode = instr.range(6, 0);",
    "  switch (opcode.to_uint()) {",
    "    case 0x13: case 0x03: case 0x67:  // I-type (ALU-I, LOAD, JALR)",
    "      io_imm.write(imm_i); break;",
    "    case 0x23:                         // S-type (STORE)",
    "      io_imm.write(imm_s); break;",
    "    case 0x63:                         // B-type (BRANCH)",
    "      io_imm.write(imm_b); break;",
    "    case 0x37: case 0x17:             // U-type (LUI, AUIPC)",
    "      io_imm.write(imm_u); break;",
    "    case 0x6f:                         // J-type (JAL)",
    "      io_imm.write(imm_j); break;",
    "    default:",
    "      io_imm.write(0); break;",
    "  }",
    "",
    "  // Dispatch classification",
    "  bool valid = io_valid.read();",
    "  bool is_store  = (opcode == 0x23);",
    "  bool is_branch_op = (opcode == 0x63);",
    "  bool is_fence  = (opcode == 0x0f);",
    "  bool is_system = (opcode == 0x73);",
    "  io_has_rd.write(valid && !is_store && !is_branch_op && !is_fence && !is_system);",
    "",
    "  bool is_rtype = (opcode == 0x33);",
    if hasMSC defs then
    "  bool is_mext = is_rtype && ((instr >> 25) & 1);"
    else "",
    "  io_is_integer.write(valid && (",
    if hasMSC defs then
    "    (is_rtype && !is_mext) ||"
    else
    "    is_rtype ||",
    "    (opcode == 0x13) || (opcode == 0x37) || (opcode == 0x17)));",
    "  io_is_memory.write(valid && ((opcode == 0x03) || (opcode == 0x23)));",
    "  io_is_branch.write(valid && ((opcode == 0x63) || (opcode == 0x6f) || (opcode == 0x67)));",
    "  io_is_store.write(valid && (opcode == 0x23));",
    "  io_use_imm.write(valid && (opcode != 0x33));",
    if hasMSC defs then
    "  io_is_muldiv.write(valid && is_mext);"
    else "",
    "}",
    ""
  ]

/-- Write SystemC decoder header to file -/
def writeSystemCDecoderHeader (defs : List InstructionDef) (outputPath : String) (moduleName : String := "RV32IDecoder") : IO Unit := do
  let scCode := genSystemCDecoderHeader defs moduleName
  IO.FS.writeFile outputPath scCode
  IO.println s!"Generated SystemC header:         {outputPath}"

/-- Write SystemC decoder implementation to file -/
def writeSystemCDecoderImpl (defs : List InstructionDef) (outputPath : String) (moduleName : String := "RV32IDecoder") : IO Unit := do
  let scCode := genSystemCDecoderImpl defs moduleName
  IO.FS.writeFile outputPath scCode
  IO.println s!"Generated SystemC implementation:  {outputPath}"

end Shoumei.RISCV
