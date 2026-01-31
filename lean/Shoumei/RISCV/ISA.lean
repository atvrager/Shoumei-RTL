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

end Shoumei.RISCV
