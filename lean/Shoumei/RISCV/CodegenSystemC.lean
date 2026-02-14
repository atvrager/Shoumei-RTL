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

/-- Check if decoder includes F-extension instructions (SystemC) -/
private def hasFSC (defs : List InstructionDef) : Bool :=
  defs.any (fun d => d.extension.any (· == "rv_f"))

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

  let hasF := hasFSC defs
  let optypeWidth := if hasF then 7 else 6

  let fpPorts := if hasF then
    "\n" ++
    genBoolPorts "sc_out" "io_rs3" 5 ++ "\n" ++
    genBoolPorts "sc_out" "io_rm" 3 ++ "\n" ++
    "  sc_out<bool> io_is_fp;\n" ++
    "  sc_out<bool> io_has_fp_rd;\n" ++
    "  sc_out<bool> io_fp_rs1_read;\n" ++
    "  sc_out<bool> io_fp_rs2_read;\n" ++
    "  sc_out<bool> io_fp_rs3_used;\n" ++
    "  sc_out<bool> io_is_fp_load;\n" ++
    "  sc_out<bool> io_is_fp_store;"
  else ""

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
    s!"  // Output: decoded operation type ({optypeWidth} bits)",
    genBoolPorts "sc_out" "io_optype" optypeWidth,
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
    "  sc_out<bool> io_use_imm;" ++ muldivPort ++ fpPorts,
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

  let hasF := hasFSC defs

  -- Gather input bits into uint32_t
  let gatherInstr := "  uint32_t instr = 0;\n" ++
    String.intercalate "\n" ((List.range 32).map fun i =>
      s!"  instr |= (io_instr_{i}.read() ? 1u : 0u) << {i};")

  -- Scatter multi-bit outputs
  let scatterField (name : String) (width : Nat) (varName : String) : String :=
    String.intercalate "\n" ((List.range width).map fun i =>
      s!"  {name}_{i}.write(({varName} >> {i}) & 1);")

  let optypeWidth := if hasF then 7 else 6

  let rs3RmExtract := if hasF then
    "  uint32_t rs3 = (instr >> 27) & 0x1f;\n" ++
    "  uint32_t rm  = (instr >> 12) & 0x7;\n"
  else ""

  let rs3RmScatter := if hasF then
    scatterField "io_rs3" 5 "rs3" ++ "\n" ++
    scatterField "io_rm" 3 "rm" ++ "\n"
  else ""

  -- FLW/FSW immediate mux entries
  let fpImmCases := if hasF then
    "    case 0x07:  // FLW (I-type)\n" ++
    "      imm = imm_i; break;\n" ++
    "    case 0x27:  // FSW (S-type)\n" ++
    "      imm = imm_s; break;\n"
  else ""

  -- FP store in is_store
  let fpStoreCheck := if hasF then " || (opcode == 0x27)" else ""

  -- FSW excluded from has_rd
  let fpHasRdExclude := if hasF then " && (opcode != 0x27)" else ""

  -- FP memory opcodes
  let fpMemoryCheck := if hasF then " || (opcode == 0x07) || (opcode == 0x27)" else ""

  -- FP opcodes excluded from use_imm
  let fpUseImmExclude := if hasF then
    " && (opcode != 0x53) && (opcode != 0x43) && (opcode != 0x47) && (opcode != 0x4b) && (opcode != 0x4f)"
  else ""

  -- FP classification signals
  let fpClassify := if hasF then
    "\n  // FP classification outputs\n" ++
    "  // is_fp: OP-FP (0x53), FMADD (0x43), FMSUB (0x47), FNMADD (0x4b), FNMSUB (0x4f)\n" ++
    "  io_is_fp.write(valid && (\n" ++
    "    (opcode == 0x53) || (opcode == 0x43) || (opcode == 0x47) ||\n" ++
    "    (opcode == 0x4b) || (opcode == 0x4f)));\n" ++
    "\n" ++
    "  // has_fp_rd: FP arith + fused + FLW, excluding compare/classify/FP->int from OP-FP\n" ++
    "  uint32_t funct5 = (instr >> 27) & 0x1f;\n" ++
    "  io_has_fp_rd.write(valid && (\n" ++
    "    (opcode == 0x43) || (opcode == 0x47) ||\n" ++
    "    (opcode == 0x4b) || (opcode == 0x4f) ||\n" ++
    "    (opcode == 0x07) ||  // FLW\n" ++
    "    (opcode == 0x53 && funct5 != 0x14 && funct5 != 0x18 && funct5 != 0x1c)));\n" ++
    "\n" ++
    "  // fp_rs1_read: fused ops + OP-FP excluding int->FP (FCVT.S.W/WU=0x1a, FMV.W.X=0x1e)\n" ++
    "  io_fp_rs1_read.write(valid && (\n" ++
    "    (opcode == 0x43) || (opcode == 0x47) ||\n" ++
    "    (opcode == 0x4b) || (opcode == 0x4f) ||\n" ++
    "    (opcode == 0x53 && funct5 != 0x1a && funct5 != 0x1e)));\n" ++
    "\n" ++
    "  // fp_rs2_read: FSW, fused ops, OP-FP 2-source ops\n" ++
    "  io_fp_rs2_read.write(valid && (\n" ++
    "    (opcode == 0x27) ||  // FSW\n" ++
    "    (opcode == 0x43) || (opcode == 0x47) ||\n" ++
    "    (opcode == 0x4b) || (opcode == 0x4f) ||\n" ++
    "    (opcode == 0x53 && (\n" ++
    "      funct5 == 0x00 || funct5 == 0x01 || funct5 == 0x02 ||\n" ++
    "      funct5 == 0x14 || funct5 == 0x04 || funct5 == 0x05))));\n" ++
    "\n" ++
    "  // fp_rs3_used: R4-type fused ops only\n" ++
    "  io_fp_rs3_used.write(valid && (\n" ++
    "    (opcode == 0x43) || (opcode == 0x47) ||\n" ++
    "    (opcode == 0x4b) || (opcode == 0x4f)));\n" ++
    "\n" ++
    "  // FP load (FLW)\n" ++
    "  io_is_fp_load.write(valid && (opcode == 0x07));\n" ++
    "\n" ++
    "  // FP store (FSW)\n" ++
    "  io_is_fp_store.write(valid && (opcode == 0x27));\n"
  else ""

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
    "  uint32_t rs2 = (instr >> 20) & 0x1f;" ++ (if hasF then "\n" ++ rs3RmExtract else ""),
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
    "    case 0x13: case 0x03: case 0x67: case 0x73:  // I-type (incl. SYSTEM/CSR)",
    "      imm = imm_i; break;",
    "    case 0x23:  // S-type",
    "      imm = imm_s; break;",
    "    case 0x63:  // B-type",
    "      imm = imm_b; break;",
    "    case 0x37: case 0x17:  // U-type",
    "      imm = imm_u; break;",
    "    case 0x6f:  // J-type",
    "      imm = imm_j; break;" ++ (if fpImmCases != "" then "\n" ++ fpImmCases else ""),
    "    default: imm = 0; break;",
    s!"  {rb}",
    "",
    "  // Scatter outputs to individual bool ports",
    scatterField "io_optype" optypeWidth "optype",
    scatterField "io_rd" 5 "rd",
    scatterField "io_rs1" 5 "rs1",
    scatterField "io_rs2" 5 "rs2" ++ (if hasF then "\n" ++ rs3RmScatter else ""),
    "  uint32_t imm_u32 = (uint32_t)imm;",
    scatterField "io_imm" 32 "imm_u32",
    "",
    "  // Control signals",
    "  io_valid.write(valid);",
    "",
    "  // Dispatch classification",
    "  bool is_store  = (opcode == 0x23)" ++ fpStoreCheck ++ ";",
    "  bool is_branch_op = (opcode == 0x63);",
    "  bool is_fence  = (opcode == 0x0f);",
    "  // Note: ECALL/EBREAK/MRET have rd=x0, excluded by rd!=0 check; CSR instructions write rd",
    "  io_has_rd.write(valid && !is_store && !is_branch_op && !is_fence" ++ fpHasRdExclude ++ ");",
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
    "  io_is_memory.write(valid && ((opcode == 0x03) || (opcode == 0x23)" ++ fpMemoryCheck ++ "));",
    "  io_is_branch.write(valid && ((opcode == 0x63) || (opcode == 0x6f) || (opcode == 0x67)));",
    "  io_is_store.write(valid && (opcode == 0x23)" ++ fpStoreCheck ++ ");",
    "  io_use_imm.write(valid && (opcode != 0x33) && (opcode != 0x63)" ++ fpUseImmExclude ++ ");",
    if hasMSC defs then
    "  io_is_muldiv.write(valid && is_mext);"
    else "",
    fpClassify,
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
