/-
  RISC-V ISA Definitions

  Core data structures for RISC-V instruction definitions.
  These types are populated from riscv-opcodes JSON via OpcodeParser.
-/

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
  | _          => none

/-- Instruction operation types (high-level categories) -/
inductive OpType where
  -- Arithmetic/Logic (R-type and I-type)
  | ADD    : OpType
  | SUB    : OpType
  | AND    : OpType
  | OR     : OpType
  | XOR    : OpType
  | SLT    : OpType  -- Set less than (signed)
  | SLTU   : OpType  -- Set less than unsigned
  | SLL    : OpType  -- Shift left logical
  | SRL    : OpType  -- Shift right logical
  | SRA    : OpType  -- Shift right arithmetic
  -- Immediate variants (have dedicated opcodes in RV32I)
  | ADDI   : OpType
  | ANDI   : OpType
  | ORI    : OpType
  | XORI   : OpType
  | SLTI   : OpType
  | SLTIU  : OpType
  | SLLI   : OpType
  | SRLI   : OpType
  | SRAI   : OpType
  -- Branches
  | BEQ    : OpType  -- Branch if equal
  | BNE    : OpType  -- Branch if not equal
  | BLT    : OpType  -- Branch if less than (signed)
  | BGE    : OpType  -- Branch if greater or equal (signed)
  | BLTU   : OpType  -- Branch if less than (unsigned)
  | BGEU   : OpType  -- Branch if greater or equal (unsigned)
  -- Jumps
  | JAL    : OpType  -- Jump and link
  | JALR   : OpType  -- Jump and link register
  -- Loads
  | LB     : OpType  -- Load byte (sign-extended)
  | LH     : OpType  -- Load halfword (sign-extended)
  | LW     : OpType  -- Load word
  | LBU    : OpType  -- Load byte unsigned
  | LHU    : OpType  -- Load halfword unsigned
  -- Stores
  | SB     : OpType  -- Store byte
  | SH     : OpType  -- Store halfword
  | SW     : OpType  -- Store word
  -- Upper immediates
  | LUI    : OpType  -- Load upper immediate
  | AUIPC  : OpType  -- Add upper immediate to PC
  -- System
  | FENCE  : OpType  -- Fence instruction
  | ECALL  : OpType  -- Environment call
  | EBREAK : OpType  -- Environment break
  -- M extension: Multiply/Divide
  -- F extension: Single-precision floating-point
  | FADD_S   : OpType  -- FP add single
  | FSUB_S   : OpType  -- FP subtract single
  | FMUL_S   : OpType  -- FP multiply single
  | FDIV_S   : OpType  -- FP divide single
  | FSQRT_S  : OpType  -- FP square root single
  | FMADD_S  : OpType  -- FP fused multiply-add single (R4-type)
  | FMSUB_S  : OpType  -- FP fused multiply-sub single (R4-type)
  | FNMADD_S : OpType  -- FP negated fused multiply-add single (R4-type)
  | FNMSUB_S : OpType  -- FP negated fused multiply-sub single (R4-type)
  | FEQ_S    : OpType  -- FP compare equal (result → int rd)
  | FLT_S    : OpType  -- FP compare less than (result → int rd)
  | FLE_S    : OpType  -- FP compare less or equal (result → int rd)
  | FCVT_W_S  : OpType  -- FP → signed int32
  | FCVT_WU_S : OpType  -- FP → unsigned int32
  | FCVT_S_W  : OpType  -- Signed int32 → FP
  | FCVT_S_WU : OpType  -- Unsigned int32 → FP
  | FMV_X_W  : OpType  -- Move FP bits → int register
  | FMV_W_X  : OpType  -- Move int bits → FP register
  | FCLASS_S : OpType  -- FP classify (result → int rd)
  | FMIN_S   : OpType  -- FP minimum single
  | FMAX_S   : OpType  -- FP maximum single
  | FSGNJ_S  : OpType  -- FP sign inject single
  | FSGNJN_S : OpType  -- FP sign inject negated single
  | FSGNJX_S : OpType  -- FP sign inject XOR single
  | FLW      : OpType  -- FP load word (from memory → FP reg)
  | FSW      : OpType  -- FP store word (FP reg → memory)
  -- M extension: Multiply/Divide
  | MUL    : OpType  -- Multiply low: rd = (rs1 * rs2)[31:0]
  | MULH   : OpType  -- Multiply high signed: rd = (signed(rs1) * signed(rs2))[63:32]
  | MULHSU : OpType  -- Multiply high signed-unsigned: rd = (signed(rs1) * unsigned(rs2))[63:32]
  | MULHU  : OpType  -- Multiply high unsigned: rd = (unsigned(rs1) * unsigned(rs2))[63:32]
  | DIV    : OpType  -- Divide signed: rd = signed(rs1) / signed(rs2)
  | DIVU   : OpType  -- Divide unsigned: rd = unsigned(rs1) / unsigned(rs2)
  | REM    : OpType  -- Remainder signed: rd = signed(rs1) % signed(rs2)
  | REMU   : OpType  -- Remainder unsigned: rd = unsigned(rs1) % unsigned(rs2)
  -- Zicsr: CSR instructions (minimal, for F extension FCSR support)
  | CSRRW  : OpType  -- CSR read/write: rd = csr; csr = rs1
  | CSRRS  : OpType  -- CSR read/set: rd = csr; csr |= rs1
  | CSRRC  : OpType  -- CSR read/clear: rd = csr; csr &= ~rs1
  | CSRRWI : OpType  -- CSR read/write immediate: rd = csr; csr = zimm
  | CSRRSI : OpType  -- CSR read/set immediate: rd = csr; csr |= zimm
  | CSRRCI : OpType  -- CSR read/clear immediate: rd = csr; csr &= ~zimm
  deriving Repr, BEq, DecidableEq

instance : ToString OpType where
  toString := fun
    | .ADD => "ADD" | .SUB => "SUB" | .AND => "AND" | .OR => "OR" | .XOR => "XOR"
    | .SLT => "SLT" | .SLTU => "SLTU" | .SLL => "SLL" | .SRL => "SRL" | .SRA => "SRA"
    | .ADDI => "ADDI" | .ANDI => "ANDI" | .ORI => "ORI" | .XORI => "XORI"
    | .SLTI => "SLTI" | .SLTIU => "SLTIU" | .SLLI => "SLLI" | .SRLI => "SRLI" | .SRAI => "SRAI"
    | .BEQ => "BEQ" | .BNE => "BNE" | .BLT => "BLT" | .BGE => "BGE" | .BLTU => "BLTU" | .BGEU => "BGEU"
    | .JAL => "JAL" | .JALR => "JALR"
    | .LB => "LB" | .LH => "LH" | .LW => "LW" | .LBU => "LBU" | .LHU => "LHU"
    | .SB => "SB" | .SH => "SH" | .SW => "SW"
    | .LUI => "LUI" | .AUIPC => "AUIPC"
    | .FENCE => "FENCE" | .ECALL => "ECALL" | .EBREAK => "EBREAK"
    | .FADD_S => "FADD_S" | .FSUB_S => "FSUB_S" | .FMUL_S => "FMUL_S"
    | .FDIV_S => "FDIV_S" | .FSQRT_S => "FSQRT_S"
    | .FMADD_S => "FMADD_S" | .FMSUB_S => "FMSUB_S"
    | .FNMADD_S => "FNMADD_S" | .FNMSUB_S => "FNMSUB_S"
    | .FEQ_S => "FEQ_S" | .FLT_S => "FLT_S" | .FLE_S => "FLE_S"
    | .FCVT_W_S => "FCVT_W_S" | .FCVT_WU_S => "FCVT_WU_S"
    | .FCVT_S_W => "FCVT_S_W" | .FCVT_S_WU => "FCVT_S_WU"
    | .FMV_X_W => "FMV_X_W" | .FMV_W_X => "FMV_W_X" | .FCLASS_S => "FCLASS_S"
    | .FMIN_S => "FMIN_S" | .FMAX_S => "FMAX_S"
    | .FSGNJ_S => "FSGNJ_S" | .FSGNJN_S => "FSGNJN_S" | .FSGNJX_S => "FSGNJX_S"
    | .FLW => "FLW" | .FSW => "FSW"
    | .MUL => "MUL" | .MULH => "MULH" | .MULHSU => "MULHSU" | .MULHU => "MULHU"
    | .DIV => "DIV" | .DIVU => "DIVU" | .REM => "REM" | .REMU => "REMU"
    | .CSRRW => "CSRRW" | .CSRRS => "CSRRS" | .CSRRC => "CSRRC"
    | .CSRRWI => "CSRRWI" | .CSRRSI => "CSRRSI" | .CSRRCI => "CSRRCI"

/-- Parse OpType from instruction name (uppercase) -/
def OpType.fromString (s : String) : Option OpType :=
  match s.toUpper with
  | "ADD"    => some .ADD
  | "SUB"    => some .SUB
  | "AND"    => some .AND
  | "OR"     => some .OR
  | "XOR"    => some .XOR
  | "SLT"    => some .SLT
  | "SLTU"   => some .SLTU
  | "SLL"    => some .SLL
  | "SRL"    => some .SRL
  | "SRA"    => some .SRA
  | "ADDI"   => some .ADDI
  | "ANDI"   => some .ANDI
  | "ORI"    => some .ORI
  | "XORI"   => some .XORI
  | "SLTI"   => some .SLTI
  | "SLTIU"  => some .SLTIU
  | "SLLI"   => some .SLLI
  | "SRLI"   => some .SRLI
  | "SRAI"   => some .SRAI
  | "BEQ"    => some .BEQ
  | "BNE"    => some .BNE
  | "BLT"    => some .BLT
  | "BGE"    => some .BGE
  | "BLTU"   => some .BLTU
  | "BGEU"   => some .BGEU
  | "JAL"    => some .JAL
  | "JALR"   => some .JALR
  | "LB"     => some .LB
  | "LH"     => some .LH
  | "LW"     => some .LW
  | "LBU"    => some .LBU
  | "LHU"    => some .LHU
  | "SB"     => some .SB
  | "SH"     => some .SH
  | "SW"     => some .SW
  | "LUI"    => some .LUI
  | "AUIPC"  => some .AUIPC
  | "FENCE"  => some .FENCE
  | "ECALL"  => some .ECALL
  | "EBREAK" => some .EBREAK
  -- F extension
  | "FADD_S" | "FADD.S"   => some .FADD_S
  | "FSUB_S" | "FSUB.S"   => some .FSUB_S
  | "FMUL_S" | "FMUL.S"   => some .FMUL_S
  | "FDIV_S" | "FDIV.S"   => some .FDIV_S
  | "FSQRT_S" | "FSQRT.S" => some .FSQRT_S
  | "FMADD_S" | "FMADD.S"   => some .FMADD_S
  | "FMSUB_S" | "FMSUB.S"   => some .FMSUB_S
  | "FNMADD_S" | "FNMADD.S" => some .FNMADD_S
  | "FNMSUB_S" | "FNMSUB.S" => some .FNMSUB_S
  | "FEQ_S" | "FEQ.S"     => some .FEQ_S
  | "FLT_S" | "FLT.S"     => some .FLT_S
  | "FLE_S" | "FLE.S"     => some .FLE_S
  | "FCVT_W_S" | "FCVT.W.S"   => some .FCVT_W_S
  | "FCVT_WU_S" | "FCVT.WU.S" => some .FCVT_WU_S
  | "FCVT_S_W" | "FCVT.S.W"   => some .FCVT_S_W
  | "FCVT_S_WU" | "FCVT.S.WU" => some .FCVT_S_WU
  | "FMV_X_W" | "FMV.X.W" => some .FMV_X_W
  | "FMV_W_X" | "FMV.W.X" => some .FMV_W_X
  | "FCLASS_S" | "FCLASS.S" => some .FCLASS_S
  | "FMIN_S" | "FMIN.S"   => some .FMIN_S
  | "FMAX_S" | "FMAX.S"   => some .FMAX_S
  | "FSGNJ_S" | "FSGNJ.S"   => some .FSGNJ_S
  | "FSGNJN_S" | "FSGNJN.S" => some .FSGNJN_S
  | "FSGNJX_S" | "FSGNJX.S" => some .FSGNJX_S
  | "FLW"     => some .FLW
  | "FSW"     => some .FSW
  -- M extension
  | "MUL"    => some .MUL
  | "MULH"   => some .MULH
  | "MULHSU" => some .MULHSU
  | "MULHU"  => some .MULHU
  | "DIV"    => some .DIV
  | "DIVU"   => some .DIVU
  | "REM"    => some .REM
  | "REMU"   => some .REMU
  | "CSRRW"  => some .CSRRW
  | "CSRRS"  => some .CSRRS
  | "CSRRC"  => some .CSRRC
  | "CSRRWI" => some .CSRRWI
  | "CSRRSI" => some .CSRRSI
  | "CSRRCI" => some .CSRRCI
  | _        => none

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
