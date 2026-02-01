//==============================================================================
// RV32I Instruction Decoder
// Generated from riscv-opcodes definitions
//
// This module decodes 32-bit RISC-V instructions and extracts:
// - Operation type (OpType enum)
// - Register operands (rd, rs1, rs2)
// - Immediate values (sign-extended to 32 bits)
//==============================================================================

package shoumei.riscv

import chisel3._
import chisel3.util._

object OpType extends ChiselEnum {
  val XORI   = Value
  val XOR    = Value
  val SW     = Value
  val SUB    = Value
  val SRLI   = Value
  val SRL    = Value
  val SRAI   = Value
  val SRA    = Value
  val SLTU   = Value
  val SLTIU  = Value
  val SLTI   = Value
  val SLT    = Value
  val SLLI   = Value
  val SLL    = Value
  val SH     = Value
  val SB     = Value
  val ORI    = Value
  val OR     = Value
  val LW     = Value
  val LUI    = Value
  val LHU    = Value
  val LH     = Value
  val LBU    = Value
  val LB     = Value
  val JALR   = Value
  val JAL    = Value
  val FENCE  = Value
  val ECALL  = Value
  val EBREAK = Value
  val BNE    = Value
  val BLTU   = Value
  val BLT    = Value
  val BGEU   = Value
  val BGE    = Value
  val BEQ    = Value
  val AUIPC  = Value
  val ANDI   = Value
  val AND    = Value
  val ADDI   = Value
  val ADD    = Value
}

class DecoderIO extends Bundle {
  val instr  = Input(UInt(32.W))  // 32-bit instruction word
  val optype = Output(OpType())   // Decoded operation type
  val rd     = Output(UInt(5.W))  // Destination register
  val rs1    = Output(UInt(5.W))  // Source register 1
  val rs2    = Output(UInt(5.W))  // Source register 2
  val imm    = Output(SInt(32.W)) // Immediate value (sign-extended)
  val valid  = Output(Bool())     // Instruction is valid RV32I
}

class RV32IDecoder extends Module {
  val io = IO(new DecoderIO)

  val instr = io.instr

  // Extract register fields
  io.rd := instr(11, 7)
  io.rs1 := instr(19, 15)
  io.rs2 := instr(24, 20)

  // Extract immediate values for each format

  val immI = Cat(Fill(20, instr(31)), instr(31, 20)).asSInt
  val immS = Cat(Fill(20, instr(31)), instr(31, 25), instr(11, 7)).asSInt

  val immB =
    Cat(Fill(19, instr(31)), instr(31), instr(7), instr(30, 25), instr(11, 8), 0.U(1.W)).asSInt
  val immU = Cat(instr(31, 12), 0.U(12.W)).asSInt

  val immJ =
    Cat(Fill(11, instr(31)), instr(31), instr(19, 12), instr(20), instr(30, 21), 0.U(1.W)).asSInt

  // Default: invalid instruction
  io.optype := OpType.XORI
  io.imm := 0.S
  io.valid := false.B

  // Decode instruction using mask/match patterns
  when(false.B) {
    // Placeholder
  }
    .elsewhen((instr & "h707f".U) === "h4013".U) {
      io.optype := OpType.XORI
      io.valid := true.B
    }
    .elsewhen((instr & "hfe00707f".U) === "h4033".U) {
      io.optype := OpType.XOR
      io.valid := true.B
    }
    .elsewhen((instr & "h707f".U) === "h2023".U) {
      io.optype := OpType.SW
      io.valid := true.B
    }
    .elsewhen((instr & "hfe00707f".U) === "h40000033".U) {
      io.optype := OpType.SUB
      io.valid := true.B
    }
    .elsewhen((instr & "hfe00707f".U) === "h5013".U) {
      io.optype := OpType.SRLI
      io.valid := true.B
    }
    .elsewhen((instr & "hfe00707f".U) === "h5033".U) {
      io.optype := OpType.SRL
      io.valid := true.B
    }
    .elsewhen((instr & "hfe00707f".U) === "h40005013".U) {
      io.optype := OpType.SRAI
      io.valid := true.B
    }
    .elsewhen((instr & "hfe00707f".U) === "h40005033".U) {
      io.optype := OpType.SRA
      io.valid := true.B
    }
    .elsewhen((instr & "hfe00707f".U) === "h3033".U) {
      io.optype := OpType.SLTU
      io.valid := true.B
    }
    .elsewhen((instr & "h707f".U) === "h3013".U) {
      io.optype := OpType.SLTIU
      io.valid := true.B
    }
    .elsewhen((instr & "h707f".U) === "h2013".U) {
      io.optype := OpType.SLTI
      io.valid := true.B
    }
    .elsewhen((instr & "hfe00707f".U) === "h2033".U) {
      io.optype := OpType.SLT
      io.valid := true.B
    }
    .elsewhen((instr & "hfe00707f".U) === "h1013".U) {
      io.optype := OpType.SLLI
      io.valid := true.B
    }
    .elsewhen((instr & "hfe00707f".U) === "h1033".U) {
      io.optype := OpType.SLL
      io.valid := true.B
    }
    .elsewhen((instr & "h707f".U) === "h1023".U) {
      io.optype := OpType.SH
      io.valid := true.B
    }
    .elsewhen((instr & "h707f".U) === "h23".U) {
      io.optype := OpType.SB
      io.valid := true.B
    }
    .elsewhen((instr & "h707f".U) === "h6013".U) {
      io.optype := OpType.ORI
      io.valid := true.B
    }
    .elsewhen((instr & "hfe00707f".U) === "h6033".U) {
      io.optype := OpType.OR
      io.valid := true.B
    }
    .elsewhen((instr & "h707f".U) === "h2003".U) {
      io.optype := OpType.LW
      io.valid := true.B
    }
    .elsewhen((instr & "h7f".U) === "h37".U) {
      io.optype := OpType.LUI
      io.valid := true.B
    }
    .elsewhen((instr & "h707f".U) === "h5003".U) {
      io.optype := OpType.LHU
      io.valid := true.B
    }
    .elsewhen((instr & "h707f".U) === "h1003".U) {
      io.optype := OpType.LH
      io.valid := true.B
    }
    .elsewhen((instr & "h707f".U) === "h4003".U) {
      io.optype := OpType.LBU
      io.valid := true.B
    }
    .elsewhen((instr & "h707f".U) === "h3".U) {
      io.optype := OpType.LB
      io.valid := true.B
    }
    .elsewhen((instr & "h707f".U) === "h67".U) {
      io.optype := OpType.JALR
      io.valid := true.B
    }
    .elsewhen((instr & "h7f".U) === "h6f".U) {
      io.optype := OpType.JAL
      io.valid := true.B
    }
    .elsewhen((instr & "h707f".U) === "hf".U) {
      io.optype := OpType.FENCE
      io.valid := true.B
    }
    .elsewhen((instr & "hffffffff".U) === "h73".U) {
      io.optype := OpType.ECALL
      io.valid := true.B
    }
    .elsewhen((instr & "hffffffff".U) === "h100073".U) {
      io.optype := OpType.EBREAK
      io.valid := true.B
    }
    .elsewhen((instr & "h707f".U) === "h1063".U) {
      io.optype := OpType.BNE
      io.valid := true.B
    }
    .elsewhen((instr & "h707f".U) === "h6063".U) {
      io.optype := OpType.BLTU
      io.valid := true.B
    }
    .elsewhen((instr & "h707f".U) === "h4063".U) {
      io.optype := OpType.BLT
      io.valid := true.B
    }
    .elsewhen((instr & "h707f".U) === "h7063".U) {
      io.optype := OpType.BGEU
      io.valid := true.B
    }
    .elsewhen((instr & "h707f".U) === "h5063".U) {
      io.optype := OpType.BGE
      io.valid := true.B
    }
    .elsewhen((instr & "h707f".U) === "h63".U) {
      io.optype := OpType.BEQ
      io.valid := true.B
    }
    .elsewhen((instr & "h7f".U) === "h17".U) {
      io.optype := OpType.AUIPC
      io.valid := true.B
    }
    .elsewhen((instr & "h707f".U) === "h7013".U) {
      io.optype := OpType.ANDI
      io.valid := true.B
    }
    .elsewhen((instr & "hfe00707f".U) === "h7033".U) {
      io.optype := OpType.AND
      io.valid := true.B
    }
    .elsewhen((instr & "h707f".U) === "h13".U) {
      io.optype := OpType.ADDI
      io.valid := true.B
    }
    .elsewhen((instr & "hfe00707f".U) === "h33".U) {
      io.optype := OpType.ADD
      io.valid := true.B
    }

  // Select appropriate immediate based on instruction format
  switch(instr(6, 0)) {
    is("b0010011".U, "b0000011".U, "b1100111".U)(io.imm := immI) // I-type
    is("b0100011".U)(io.imm := immS)                             // S-type
    is("b1100011".U)(io.imm := immB)                             // B-type
    is("b0110111".U, "b0010111".U)(io.imm := immU)               // U-type
    is("b1101111".U)(io.imm := immJ)                             // J-type
  }
}
