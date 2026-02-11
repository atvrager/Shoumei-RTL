/-
  SystemC Code Generator for RV32I Decoder

  Generates a SystemC simulation model from instruction definitions
  parsed from riscv-opcodes. Produces both .h (header) and .cpp files.
  Uses individual sc_in<bool>/sc_out<bool> ports matching the Lean DSL
  gate-level representation.

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
  "      optype = " ++ opName ++ ";\n" ++
  "      valid = true;\n" ++
  "    }"

/-- Check if decoder includes M-extension instructions (SystemC) -/
private def hasMSC (defs : List InstructionDef) : Bool :=
  defs.any (fun d => d.extension.any (· == "rv_m"))

/-- Generate individual bool port declarations for a multi-bit signal -/
private def genBoolPorts (dir : String) (baseName : String) (width : Nat) : String :=
  let ports := (List.range width).map fun i =>
    s!"  {dir}<bool> {baseName}_{i};"
  String.intercalate "\n" ports

/-- Generate sensitivity list for all input bool ports -/
private def genSensitivity (baseName : String) (width : Nat) : String :=
  let ports := (List.range width).map fun i => s!"{baseName}_{i}"
  String.intercalate " << " ports

/-- Generate complete SystemC decoder header file (.h) with individual bool ports -/
def genSystemCDecoderHeader (defs : List InstructionDef) (moduleName : String := "RV32IDecoder") : String :=
  let enumDecl := genSCOpTypeEnum defs
  let guardName := moduleName.toUpper ++ "_H"
  let lb := "{"
  let rb := "}"

  let muldivPort := if hasMSC defs then
    "\n  sc_out<bool> io_is_muldiv;" else ""

  String.intercalate "\n" [
    s!"#ifndef {guardName}",
    s!"#define {guardName}",
    "",
    "#include <systemc.h>",
    "",
    enumDecl,
    "",
    s!"SC_MODULE({moduleName}) {lb}",
    "  // Input: 32-bit instruction word",
    genBoolPorts "sc_in" "io_instr" 32,
    "",
    "  // Output: decoded operation type (6 bits)",
    genBoolPorts "sc_out" "io_optype" 6,
    "",
    "  // Output: register fields",
    genBoolPorts "sc_out" "io_rd" 5,
    genBoolPorts "sc_out" "io_rs1" 5,
    genBoolPorts "sc_out" "io_rs2" 5,
    "",
    "  // Output: immediate value (32 bits, sign-extended)",
    genBoolPorts "sc_out" "io_imm" 32,
    "",
    "  // Output: control signals",
    "  sc_out<bool> io_valid;",
    "  sc_out<bool> io_has_rd;",
    "  sc_out<bool> io_is_integer;",
    "  sc_out<bool> io_is_memory;",
    "  sc_out<bool> io_is_branch;",
    "  sc_out<bool> io_is_store;",
    "  sc_out<bool> io_use_imm;" ++ muldivPort,
    "",
    "  void comb_logic();",
    "  void eval_comb_all();",
    "  void eval_seq_all();",
    "",
    s!"  SC_CTOR({moduleName}) {lb}",
    s!"  {rb}",
    s!"{rb};",
    "",
    s!"#endif // {guardName}",
    ""
  ]

/-- Generate complete SystemC decoder implementation file (.cpp) with individual bool ports -/
def genSystemCDecoderImpl (defs : List InstructionDef) (moduleName : String := "RV32IDecoder") : String :=
  let defaultOp := match defs.head? with
    | some firstDef => sanitizeSCIdentifier firstDef.name
    | none => "ADD"

  let decoderCases := defs.enum.map (fun ⟨idx, instrDef⟩ =>
    genSCDecoderCase instrDef (idx == 0))
  let decoderCasesStr := String.intercalate "\n" decoderCases

  let lb := "{"
  let rb := "}"

  -- Gather input bits into uint32_t
  let gatherInstr := "  uint32_t instr = 0;\n" ++
    String.intercalate "\n" ((List.range 32).map fun i =>
      s!"  instr |= (io_instr_{i}.read() ? 1u : 0u) << {i};")

  -- Scatter multi-bit outputs
  let scatterField (name : String) (width : Nat) (varName : String) : String :=
    String.intercalate "\n" ((List.range width).map fun i =>
      s!"  {name}_{i}.write(({varName} >> {i}) & 1);")

  String.intercalate "\n" [
    s!"#include \"{moduleName}.h\"",
    "",
    s!"void {moduleName}::comb_logic() {lb}",
    "  // Gather instruction bits",
    gatherInstr,
    "",
    "  // Extract register fields",
    "  uint32_t rd  = (instr >> 7) & 0x1f;",
    "  uint32_t rs1 = (instr >> 15) & 0x1f;",
    "  uint32_t rs2 = (instr >> 20) & 0x1f;",
    "",
    "  // Extract immediate values for each format",
    "  int32_t imm_i = ((int32_t)instr) >> 20;",
    "  int32_t imm_s = (((int32_t)(instr & 0xfe000000)) >> 20) |",
    "                  ((instr >> 7) & 0x1f);",
    "  int32_t imm_b = (((int32_t)(instr & 0x80000000)) >> 19) |",
    "                  (((instr >> 7) & 1) << 11) | (((instr >> 25) & 0x3f) << 5) |",
    "                  (((instr >> 8) & 0xf) << 1);",
    "  int32_t imm_u = (int32_t)(instr & 0xfffff000);",
    "  int32_t imm_j = (((int32_t)(instr & 0x80000000)) >> 11) |",
    "                  (instr & 0x000ff000) | (((instr >> 9) & 0x800)) |",
    "                  (((instr >> 20) & 0x7fe));",
    "",
    "  // Default: invalid instruction",
    s!"  uint32_t optype = {defaultOp};",
    "  bool valid = false;",
    "",
    "  // Decode instruction using mask/match patterns",
    decoderCasesStr,
    "",
    "  // Select appropriate immediate based on instruction format",
    "  uint32_t opcode = instr & 0x7f;",
    "  int32_t imm = 0;",
    s!"  switch (opcode) {lb}",
    "    case 0x13: case 0x03: case 0x67:  // I-type",
    "      imm = imm_i; break;",
    "    case 0x23:  // S-type",
    "      imm = imm_s; break;",
    "    case 0x63:  // B-type",
    "      imm = imm_b; break;",
    "    case 0x37: case 0x17:  // U-type",
    "      imm = imm_u; break;",
    "    case 0x6f:  // J-type",
    "      imm = imm_j; break;",
    "    default: imm = 0; break;",
    s!"  {rb}",
    "",
    "  // Scatter outputs to individual bool ports",
    scatterField "io_optype" 6 "optype",
    scatterField "io_rd" 5 "rd",
    scatterField "io_rs1" 5 "rs1",
    scatterField "io_rs2" 5 "rs2",
    "  uint32_t imm_u32 = (uint32_t)imm;",
    scatterField "io_imm" 32 "imm_u32",
    "",
    "  // Control signals",
    "  io_valid.write(valid);",
    "",
    "  // Dispatch classification",
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
    "  io_use_imm.write(valid && (opcode != 0x33) && (opcode != 0x63));",
    if hasMSC defs then
    "  io_is_muldiv.write(valid && is_mext);"
    else "",
    s!"{rb}",
    "",
    s!"void {moduleName}::eval_comb_all() {lb}",
    "  comb_logic();",
    s!"{rb}",
    "",
    s!"void {moduleName}::eval_seq_all() {lb}",
    s!"{rb}",
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
