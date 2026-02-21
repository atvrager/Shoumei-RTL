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
  | Vector  : ExecUnit   -- Zve32x vector operations (forwarded to RvvCore)
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
    | .Vector  => "Vector"
    | .System  => "System"
    | .Illegal => "Illegal"

/-- Classify an instruction to its execution unit based on CPU configuration.

    M-extension operations are routed to MulDiv when config.enableM is true,
    otherwise they are classified as Illegal (decoded as illegal instruction).
-/
def classifyToUnit (op : OpType) (config : CPUConfig) : ExecUnit :=
  match op with
  -- Integer ALU (R-type and I-type)
  | .ADD | .SUB | .AND | .OR | .XOR | .SLT | .SLTU | .SLL | .SRL | .SRA
  | .ADDI | .ANDI | .ORI | .XORI | .SLTI | .SLTIU | .SLLI | .SRLI | .SRAI
  | .LUI | .AUIPC => .Integer
  -- Branch and jump
  | .BEQ | .BNE | .BLT | .BGE | .BLTU | .BGEU
  | .JAL | .JALR => .Branch
  -- Memory (loads and stores)
  | .LB | .LH | .LW | .LBU | .LHU
  | .SB | .SH | .SW => .Memory
  -- Memory (FP loads/stores go to Memory unit like integer loads/stores)
  | .FLW | .FSW => if config.enableF then .Memory else .Illegal
  -- F extension (floating-point arithmetic)
  | .FADD_S | .FSUB_S | .FMUL_S | .FDIV_S | .FSQRT_S
  | .FMADD_S | .FMSUB_S | .FNMADD_S | .FNMSUB_S
  | .FMIN_S | .FMAX_S | .FSGNJ_S | .FSGNJN_S | .FSGNJX_S =>
      if config.enableF then .FPExec else .Illegal
  -- F extension (FP compare/classify/convert → integer result)
  | .FEQ_S | .FLT_S | .FLE_S | .FCLASS_S
  | .FCVT_W_S | .FCVT_WU_S | .FMV_X_W =>
      if config.enableF then .FPExec else .Illegal
  -- F extension (integer → FP conversions, FP move)
  | .FCVT_S_W | .FCVT_S_WU | .FMV_W_X =>
      if config.enableF then .FPExec else .Illegal
  -- M extension (multiply/divide)
  | .MUL | .MULH | .MULHSU | .MULHU
  | .DIV | .DIVU | .REM | .REMU =>
      if config.enableM then .MulDiv else .Illegal
  -- Zicsr (CSR instructions routed to Integer unit)
  | .CSRRW | .CSRRS | .CSRRC | .CSRRWI | .CSRRSI | .CSRRCI => .Integer
  -- Zve32x (vector operations forwarded to external RvvCore)
  | .VECTOR_ARITH | .VECTOR_LOAD | .VECTOR_STORE =>
      if config.enableVector then .Vector else .Illegal
  -- System
  | .FENCE | .FENCE_I | .ECALL | .EBREAK => .System

/-- Check if an operation is a multiply (as opposed to divide) -/
def isMulOp (op : OpType) : Bool :=
  match op with
  | .MUL | .MULH | .MULHSU | .MULHU => true
  | _ => false

/-- Check if an operation is a divide/remainder -/
def isDivOp (op : OpType) : Bool :=
  match op with
  | .DIV | .DIVU | .REM | .REMU => true
  | _ => false

/-- Encode M-extension operation type to 3-bit opcode.
    000=MUL, 001=MULH, 010=MULHSU, 011=MULHU,
    100=DIV, 101=DIVU, 110=REM, 111=REMU -/
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
  | _       => 0  -- Invalid (shouldn't reach MulDiv unit)

end Shoumei.RISCV.Execution
