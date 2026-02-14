/-
  RISC-V ISA Definitions

  Core data structures for RISC-V instruction definitions.
  These types are populated from riscv-opcodes JSON via OpcodeParser.
-/

import Shoumei.RISCV.OpTypeGenerated

namespace Shoumei.RISCV

/-- Instruction field types (register specifiers and immediates) -/
inductive FieldType where
  | rd       : FieldType  -- Destination register
  | rs1      : FieldType  -- Source register 1
  | rs2      : FieldType  -- Source register 2
  | imm12    : FieldType  -- 12-bit immediate (I-type)
  | imm20    : FieldType  -- 20-bit immediate (U-type)
  | jimm20   : FieldType  -- 20-bit jump immediate (J-type)
  | bimm12hi : FieldType  -- Branch immediate high bits
  | bimm12lo : FieldType  -- Branch immediate low bits
  | imm12hi  : FieldType  -- Store immediate high bits
  | imm12lo  : FieldType  -- Store immediate low bits
  | shamtw   : FieldType  -- Shift amount (5 bits for RV32)
  | fm       : FieldType  -- Fence mode (FENCE instruction)
  | pred     : FieldType  -- Predecessor set (FENCE instruction)
  | succ     : FieldType  -- Successor set (FENCE instruction)
  | rs3      : FieldType  -- Source register 3 (bits 31:27, R4-type FP fused ops)
  | rm       : FieldType  -- Rounding mode (bits 14:12, F extension)
  | csr      : FieldType  -- CSR address (bits 31:20, Zicsr)
  | zimm5    : FieldType  -- Zero-extended 5-bit immediate (bits 19:15, Zicsr)
  deriving Repr, BEq, DecidableEq

instance : ToString FieldType where
  toString := fun
    | .rd => "rd"
    | .rs1 => "rs1"
    | .rs2 => "rs2"
    | .imm12 => "imm12"
    | .imm20 => "imm20"
    | .jimm20 => "jimm20"
    | .bimm12hi => "bimm12hi"
    | .bimm12lo => "bimm12lo"
    | .imm12hi => "imm12hi"
    | .imm12lo => "imm12lo"
    | .shamtw => "shamtw"
    | .fm => "fm"
    | .pred => "pred"
    | .succ => "succ"
    | .rs3 => "rs3"
    | .rm => "rm"
    | .csr => "csr"
    | .zimm5 => "zimm5"

/-- Parse field type from string (as appears in JSON) -/
def FieldType.fromString (s : String) : Option FieldType :=
  match s with
  | "rd"       => some .rd
  | "rs1"      => some .rs1
  | "rs2"      => some .rs2
  | "imm12"    => some .imm12
  | "imm20"    => some .imm20
  | "jimm20"   => some .jimm20
  | "bimm12hi" => some .bimm12hi
  | "bimm12lo" => some .bimm12lo
  | "imm12hi"  => some .imm12hi
  | "imm12lo"  => some .imm12lo
  | "shamtw"   => some .shamtw
  | "fm"       => some .fm
  | "pred"     => some .pred
  | "succ"     => some .succ
  | "rs3"      => some .rs3
  | "rm"       => some .rm
  | "csr"      => some .csr
  | "zimm5"    => some .zimm5
  | _          => none

-- OpType, ToString OpType, OpType.fromString are auto-generated in OpTypeGenerated.lean

/--
  Instruction definition (parsed from riscv-opcodes JSON)

  This structure mirrors the JSON format from instr_dict.json:
  {
    "add": {
      "encoding": "0000000----------000-----0110011",
      "variable_fields": ["rd", "rs1", "rs2"],
      "extension": ["rv_i"],
      "match": "0x33",
      "mask": "0xfe00707f"
    }
  }
-/
structure InstructionDef where
  /-- Instruction name (e.g., "add", "sub", "beq") -/
  name : String
  /-- Instruction operation type -/
  opType : OpType
  /-- 32-bit encoding pattern (0/1 for fixed bits, - for variable) -/
  encoding : String
  /-- List of variable fields (rd, rs1, rs2, immediates, etc.) -/
  variableFields : List FieldType
  /-- Extensions this instruction belongs to (e.g., ["rv_i"]) -/
  extension : List String
  /-- Match value: bits that must match for this instruction -/
  matchBits : UInt32
  /-- Mask: which bits to check (1 = check, 0 = don't care) -/
  maskBits : UInt32
  deriving Repr

/-- Helper: Check if a 32-bit instruction word matches this definition -/
def InstructionDef.matches (self : InstructionDef) (instr : UInt32) : Bool :=
  (instr &&& self.maskBits) == self.matchBits

/-- All RV32I instruction definitions (populated by parser) -/
def rv32i_instructions : List InstructionDef :=
  -- This will be populated by OpcodeParser.lean from JSON
  []

/-! ## F Extension Register File Classification -/

/-- Does this op write to an FP destination register? -/
def OpType.hasFpRd : OpType → Bool
  -- FP arithmetic, fused, sign-inject, min/max all write FP rd
  | .FADD_S | .FSUB_S | .FMUL_S | .FDIV_S | .FSQRT_S
  | .FMADD_S | .FMSUB_S | .FNMADD_S | .FNMSUB_S
  | .FMIN_S | .FMAX_S | .FSGNJ_S | .FSGNJN_S | .FSGNJX_S
  -- int→FP conversions and moves write FP rd
  | .FCVT_S_W | .FCVT_S_WU | .FMV_W_X
  -- FP load writes FP rd
  | .FLW => true
  | _ => false

/-- Does this op read FP source register rs1? -/
def OpType.hasFpRs1 : OpType → Bool
  | .FADD_S | .FSUB_S | .FMUL_S | .FDIV_S | .FSQRT_S
  | .FMADD_S | .FMSUB_S | .FNMADD_S | .FNMSUB_S
  | .FEQ_S | .FLT_S | .FLE_S
  | .FCVT_W_S | .FCVT_WU_S | .FMV_X_W | .FCLASS_S
  | .FMIN_S | .FMAX_S | .FSGNJ_S | .FSGNJN_S | .FSGNJX_S
  | .FSW => true
  | _ => false

/-- Does this op read FP source register rs2? -/
def OpType.hasFpRs2 : OpType → Bool
  | .FADD_S | .FSUB_S | .FMUL_S
  | .FMADD_S | .FMSUB_S | .FNMADD_S | .FNMSUB_S
  | .FEQ_S | .FLT_S | .FLE_S
  | .FMIN_S | .FMAX_S | .FSGNJ_S | .FSGNJN_S | .FSGNJX_S => true
  | _ => false

/-- Does this op read FP source register rs3? (R4-type fused ops only) -/
def OpType.hasFpRs3 : OpType → Bool
  | .FMADD_S | .FMSUB_S | .FNMADD_S | .FNMSUB_S => true
  | _ => false

/-- Does this op read integer rs1? (FLW/FSW use int rs1 for address) -/
def OpType.hasIntRs1 : OpType → Bool
  | .FLW | .FSW => true
  -- FMV_W_X reads int rs1
  | .FMV_W_X => true
  -- FCVT_S_W/FCVT_S_WU read int rs1
  | .FCVT_S_W | .FCVT_S_WU => true
  -- All non-F ops read int rs1 (when they have rs1)
  | op => !op.hasFpRs1

/-- Does this op write to an integer destination register?
    (Compare, classify, FP→int conversion, FMV_X_W) -/
def OpType.hasIntRd : OpType → Bool
  | .FEQ_S | .FLT_S | .FLE_S | .FCLASS_S
  | .FCVT_W_S | .FCVT_WU_S | .FMV_X_W => true
  | op => !op.hasFpRd

end Shoumei.RISCV
