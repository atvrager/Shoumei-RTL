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

/-- Generate complete SystemC decoder header file (.h) -/
def genSystemCDecoderHeader (defs : List InstructionDef) : String :=
  let enumDecl := genSCOpTypeEnum defs

  String.intercalate "\n" [
    "//==============================================================================",
    "// RV32I Instruction Decoder - SystemC Model",
    "// Generated from riscv-opcodes definitions",
    "//==============================================================================",
    "",
    "#ifndef RV32IDECODER_H",
    "#define RV32IDECODER_H",
    "",
    "#include <systemc.h>",
    "",
    enumDecl,
    "",
    "SC_MODULE(RV32IDecoder) {",
    "  // Ports",
    "  sc_in<sc_uint<32>>  io_instr;   // 32-bit instruction word",
    "  sc_out<sc_uint<6>>  io_optype;  // Decoded operation type",
    "  sc_out<sc_uint<5>>  io_rd;      // Destination register",
    "  sc_out<sc_uint<5>>  io_rs1;     // Source register 1",
    "  sc_out<sc_uint<5>>  io_rs2;     // Source register 2",
    "  sc_out<sc_int<32>>  io_imm;     // Immediate value (sign-extended)",
    "  sc_out<bool>        io_valid;   // Instruction is valid RV32I",
    "",
    "  // Process methods",
    "  void comb_logic();",
    "",
    "  // Constructor",
    "  SC_CTOR(RV32IDecoder) {",
    "    SC_METHOD(comb_logic);",
    "    sensitive << io_instr;",
    "  }",
    "};",
    "",
    "#endif // RV32IDECODER_H",
    ""
  ]

/-- Generate complete SystemC decoder implementation file (.cpp) -/
def genSystemCDecoderImpl (defs : List InstructionDef) : String :=
  let defaultOp := match defs.head? with
    | some firstDef => sanitizeSCIdentifier firstDef.name
    | none => "ADD"

  let decoderCases := defs.enum.map (fun ⟨idx, instrDef⟩ =>
    genSCDecoderCase instrDef (idx == 0))
  let decoderCasesStr := String.intercalate "\n" decoderCases

  String.intercalate "\n" [
    "#include \"RV32IDecoder.h\"",
    "",
    "void RV32IDecoder::comb_logic() {",
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
    "}",
    ""
  ]

/-- Write SystemC decoder header to file -/
def writeSystemCDecoderHeader (defs : List InstructionDef) (outputPath : String) : IO Unit := do
  let scCode := genSystemCDecoderHeader defs
  IO.FS.writeFile outputPath scCode
  IO.println s!"Generated SystemC header:         {outputPath}"

/-- Write SystemC decoder implementation to file -/
def writeSystemCDecoderImpl (defs : List InstructionDef) (outputPath : String) : IO Unit := do
  let scCode := genSystemCDecoderImpl defs
  IO.FS.writeFile outputPath scCode
  IO.println s!"Generated SystemC implementation:  {outputPath}"

end Shoumei.RISCV
