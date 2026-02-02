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
  | System  : ExecUnit   -- FENCE, ECALL, EBREAK
  | Illegal : ExecUnit   -- Unsupported operation for current config
  deriving Repr, BEq, DecidableEq

instance : ToString ExecUnit where
  toString
    | .Integer => "Integer"
    | .Branch  => "Branch"
    | .Memory  => "Memory"
    | .MulDiv  => "MulDiv"
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
  -- M extension (multiply/divide)
  | .MUL | .MULH | .MULHSU | .MULHU
  | .DIV | .DIVU | .REM | .REMU =>
      if config.enableM then .MulDiv else .Illegal
  -- System
  | .FENCE | .ECALL | .EBREAK => .System

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
