/-
  RISC-V Instruction Dispatch Classification

  Maps each OpType to the execution unit that handles it.
  Used by the pipeline to route instructions to the correct
  Reservation Station after renaming.

  The classification is config-aware: M-extension operations
  route to MulDiv when enabled, or Illegal when disabled.
-/

import Shoumei.RISCV.ISA
import Shoumei.RISCV.Config

namespace Shoumei.RISCV.Execution

open Shoumei.RISCV

/-- Execution unit types for dispatch routing -/
inductive ExecUnit where
  | Integer : ExecUnit   -- ALU operations (ADD, SUB, shifts, etc.)
  | Branch  : ExecUnit   -- Branch and jump operations
  | Memory  : ExecUnit   -- Load and store operations
  | MulDiv  : ExecUnit   -- M-extension multiply/divide
  | FPExec  : ExecUnit   -- F-extension floating-point operations
  | System  : ExecUnit   -- FENCE, ECALL, EBREAK
  | Illegal : ExecUnit   -- Unsupported operation for current config
  deriving Repr, BEq, DecidableEq

instance : ToString ExecUnit where
  toString
    | .Integer => "Integer"
    | .Branch  => "Branch"
    | .Memory  => "Memory"
    | .MulDiv  => "MulDiv"
    | .FPExec  => "FPExec"
    | .System  => "System"
    | .Illegal => "Illegal"

/-- Classify an instruction to its execution unit based on CPU configuration.

    M-extension operations are routed to MulDiv when config.enableM is true,
    otherwise they are classified as Illegal (decoded as illegal instruction).
-/
def classifyToUnit (op : OpType) (config : CPUConfig) : ExecUnit :=
  match op with
  -- Integer ALU (R-type and I-type, 32-bit and 64-bit word ops)
  | .ADD | .SUB | .AND | .OR | .XOR | .SLT | .SLTU | .SLL | .SRL | .SRA
  | .ADDI | .ANDI | .ORI | .XORI | .SLTI | .SLTIU | .SLLI | .SRLI | .SRAI
  | .ADDW | .SUBW | .SLLW | .SRLW | .SRAW
  | .ADDIW | .SLLIW | .SRLIW | .SRAIW
  | .LUI | .AUIPC => .Integer
  -- Branch and jump
  | .BEQ | .BNE | .BLT | .BGE | .BLTU | .BGEU
  | .JAL | .JALR => .Branch
  -- Memory (loads and stores)
  | .LB | .LH | .LW | .LBU | .LHU | .LWU | .LD
  | .SB | .SH | .SW | .SD => .Memory
  -- Memory (FP loads/stores go to Memory unit like integer loads/stores)
  | .FLW | .FSW => if config.enableF then .Memory else .Illegal
  | .FLD | .FSD => if config.enableD then .Memory else .Illegal
  -- A extension: atomics route to the Memory unit (LSU handles LR/SC/AMO)
  | .LR_W | .SC_W
  | .AMOADD_W | .AMOSWAP_W | .AMOXOR_W | .AMOAND_W | .AMOOR_W
  | .AMOMIN_W | .AMOMAX_W | .AMOMINU_W | .AMOMAXU_W
  | .LR_D | .SC_D
  | .AMOADD_D | .AMOSWAP_D | .AMOXOR_D | .AMOAND_D | .AMOOR_D
  | .AMOMIN_D | .AMOMAX_D | .AMOMINU_D | .AMOMAXU_D =>
      if config.enableA then .Memory else .Illegal
  -- F extension (floating-point arithmetic)
  | .FADD_S | .FSUB_S | .FMUL_S | .FDIV_S | .FSQRT_S
  | .FMADD_S | .FMSUB_S | .FNMADD_S | .FNMSUB_S
  | .FMIN_S | .FMAX_S | .FSGNJ_S | .FSGNJN_S | .FSGNJX_S =>
      if config.enableF then .FPExec else .Illegal
  -- F extension (FP compare/classify/convert → integer result)
  | .FEQ_S | .FLT_S | .FLE_S | .FCLASS_S
  | .FCVT_W_S | .FCVT_WU_S | .FMV_X_W
  | .FCVT_L_S | .FCVT_LU_S =>
      if config.enableF then .FPExec else .Illegal
  -- F extension (integer → FP conversions, FP move)
  | .FCVT_S_W | .FCVT_S_WU | .FMV_W_X
  | .FCVT_S_L | .FCVT_S_LU =>
      if config.enableF then .FPExec else .Illegal
  -- D extension (floating-point arithmetic)
  | .FADD_D | .FSUB_D | .FMUL_D | .FDIV_D | .FSQRT_D
  | .FMADD_D | .FMSUB_D | .FNMADD_D | .FNMSUB_D
  | .FMIN_D | .FMAX_D | .FSGNJ_D | .FSGNJN_D | .FSGNJX_D =>
      if config.enableD then .FPExec else .Illegal
  -- D extension (FP compare/classify/convert → integer or SP result)
  | .FEQ_D | .FLT_D | .FLE_D | .FCLASS_D
  | .FCVT_W_D | .FCVT_WU_D | .FCVT_S_D
  | .FCVT_L_D | .FCVT_LU_D | .FMV_X_D =>
      if config.enableD then .FPExec else .Illegal
  -- D extension (integer / SP → DP conversions)
  | .FCVT_D_W | .FCVT_D_WU | .FCVT_D_S
  | .FCVT_D_L | .FCVT_D_LU | .FMV_D_X =>
      if config.enableD then .FPExec else .Illegal
  -- M extension (multiply/divide)
  | .MUL | .MULH | .MULHSU | .MULHU | .MULW
  | .DIV | .DIVU | .REM | .REMU
  | .DIVW | .DIVUW | .REMW | .REMUW =>
      if config.enableM then .MulDiv else .Illegal
  -- Zicsr (CSR instructions routed to Integer unit)
  | .CSRRW | .CSRRS | .CSRRC | .CSRRWI | .CSRRSI | .CSRRCI => .Integer
  -- System
  | .FENCE | .FENCE_I | .ECALL | .EBREAK | .MRET | .WFI => .System

/-- Check if an operation is a multiply (as opposed to divide) -/
def isMulOp (op : OpType) : Bool :=
  match op with
  | .MUL | .MULH | .MULHSU | .MULHU | .MULW => true
  | _ => false

/-- Check if an operation is a divide/remainder -/
def isDivOp (op : OpType) : Bool :=
  match op with
  | .DIV | .DIVU | .REM | .REMU | .DIVW | .DIVUW | .REMW | .REMUW => true
  | _ => false

/-- Encode M-extension operation type to 4-bit opcode.
    Bit 3 = 1 for word operations (*W).
    0000=MUL, 0001=MULH, 0010=MULHSU, 0011=MULHU,
    0100=DIV, 0101=DIVU, 0110=REM, 0111=REMU,
    1000=MULW, 1100=DIVW, 1101=DIVUW, 1110=REMW, 1111=REMUW -/
def opTypeToMulDivOpcode (op : OpType) : Nat :=
  match op with
  | .MUL    => 0
  | .MULH   => 1
  | .MULHSU => 2
  | .MULHU  => 3
  | .DIV    => 4
  | .DIVU   => 5
  | .REM    => 6
  | .REMU   => 7
  | .MULW   => 8
  | .DIVW   => 12
  | .DIVUW  => 13
  | .REMW   => 14
  | .REMUW  => 15
  | _       => 0  -- Invalid (shouldn't reach MulDiv unit)

end Shoumei.RISCV.Execution
