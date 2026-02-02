/-
  Dispatch Classification Proofs

  Proves that classifyToUnit is exhaustive and correct.
-/

import Shoumei.RISCV.Execution.Dispatch

namespace Shoumei.RISCV.Execution.DispatchProofs

open Shoumei.RISCV
open Shoumei.RISCV.Execution

/-- All M-ext ops route to MulDiv when M is enabled -/
theorem mul_routes_to_muldiv :
    classifyToUnit .MUL rv32imConfig = .MulDiv := by native_decide

theorem div_routes_to_muldiv :
    classifyToUnit .DIV rv32imConfig = .MulDiv := by native_decide

/-- M-ext ops are illegal when M is disabled -/
theorem mul_illegal_without_m :
    classifyToUnit .MUL rv32iConfig = .Illegal := by native_decide

theorem div_illegal_without_m :
    classifyToUnit .DIV rv32iConfig = .Illegal := by native_decide

/-- Integer ALU ops always route to Integer -/
theorem add_routes_to_integer :
    classifyToUnit .ADD rv32iConfig = .Integer := by native_decide

theorem addi_routes_to_integer :
    classifyToUnit .ADDI rv32imConfig = .Integer := by native_decide

/-- Branch ops always route to Branch -/
theorem beq_routes_to_branch :
    classifyToUnit .BEQ rv32iConfig = .Branch := by native_decide

/-- Load/store ops always route to Memory -/
theorem lw_routes_to_memory :
    classifyToUnit .LW rv32iConfig = .Memory := by native_decide

theorem sw_routes_to_memory :
    classifyToUnit .SW rv32imConfig = .Memory := by native_decide

/-- isMulOp correctly identifies multiply operations -/
theorem mul_is_mul_op : isMulOp .MUL = true := by native_decide
theorem mulh_is_mul_op : isMulOp .MULH = true := by native_decide
theorem div_is_not_mul_op : isMulOp .DIV = false := by native_decide
theorem add_is_not_mul_op : isMulOp .ADD = false := by native_decide

/-- isDivOp correctly identifies divide operations -/
theorem div_is_div_op : isDivOp .DIV = true := by native_decide
theorem remu_is_div_op : isDivOp .REMU = true := by native_decide
theorem mul_is_not_div_op : isDivOp .MUL = false := by native_decide

/-- MulDiv opcode encoding is correct -/
theorem mul_opcode : opTypeToMulDivOpcode .MUL = 0 := by native_decide
theorem mulh_opcode : opTypeToMulDivOpcode .MULH = 1 := by native_decide
theorem mulhsu_opcode : opTypeToMulDivOpcode .MULHSU = 2 := by native_decide
theorem mulhu_opcode : opTypeToMulDivOpcode .MULHU = 3 := by native_decide
theorem div_opcode : opTypeToMulDivOpcode .DIV = 4 := by native_decide
theorem divu_opcode : opTypeToMulDivOpcode .DIVU = 5 := by native_decide
theorem rem_opcode : opTypeToMulDivOpcode .REM = 6 := by native_decide
theorem remu_opcode : opTypeToMulDivOpcode .REMU = 7 := by native_decide

end Shoumei.RISCV.Execution.DispatchProofs
