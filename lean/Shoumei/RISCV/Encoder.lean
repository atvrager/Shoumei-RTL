/-
  RISC-V Instruction Encoder

  Inverse of Decoder.lean. Maps OpType + operands → UInt32 instruction word.
  Uses matchBits from InstructionDef as the base encoding, then ORs in variable fields.
-/

import Shoumei.RISCV.ISA
import Shoumei.RISCV.OpcodeParser
import Shoumei.RISCV.Decoder

namespace Shoumei.RISCV

/-- Lookup InstructionDef for a given OpType from the rv32im defs list -/
def opTypeToInstrDef (defs : List InstructionDef) (op : OpType) : Option InstructionDef :=
  defs.find? (fun d => d.opType == op)

/-- Pack rd into bits [11:7] -/
def packRd (reg : Fin 32) : UInt32 :=
  (UInt32.ofNat reg.val) <<< 7

/-- Pack rs1 into bits [19:15] -/
def packRs1 (reg : Fin 32) : UInt32 :=
  (UInt32.ofNat reg.val) <<< 15

/-- Pack rs2 into bits [24:20] -/
def packRs2 (reg : Fin 32) : UInt32 :=
  (UInt32.ofNat reg.val) <<< 20

/-- Pack I-type immediate into bits [31:20] -/
def packImmI (imm : Int) : UInt32 :=
  let bits := (UInt32.ofNat imm.toNat) &&& 0xFFF
  bits <<< 20

/-- Pack S-type immediate: bits [31:25] | [11:7] -/
def packImmS (imm : Int) : UInt32 :=
  let bits := (UInt32.ofNat imm.toNat) &&& 0xFFF
  let imm4_0 := bits &&& 0x1F
  let imm11_5 := (bits >>> 5) &&& 0x7F
  (imm11_5 <<< 25) ||| (imm4_0 <<< 7)

/-- Pack B-type immediate (must be even): scrambled to B-type layout -/
def packImmB (imm : Int) : UInt32 :=
  let bits := (UInt32.ofNat imm.toNat) &&& 0x1FFF
  let imm12   := (bits >>> 12) &&& 1
  let imm11   := (bits >>> 11) &&& 1
  let imm10_5 := (bits >>> 5) &&& 0x3F
  let imm4_1  := (bits >>> 1) &&& 0xF
  (imm12 <<< 31) ||| (imm10_5 <<< 25) ||| (imm4_1 <<< 8) ||| (imm11 <<< 7)

/-- Pack U-type immediate (already shifted left 12 by caller, or upper 20 bits) -/
def packImmU (imm : UInt32) : UInt32 :=
  imm &&& 0xFFFFF000

/-- Pack J-type immediate (must be even): scrambled to J-type layout -/
def packImmJ (imm : Int) : UInt32 :=
  let bits := (UInt32.ofNat imm.toNat) &&& 0x1FFFFF
  let imm20    := (bits >>> 20) &&& 1
  let imm10_1  := (bits >>> 1) &&& 0x3FF
  let imm11    := (bits >>> 11) &&& 1
  let imm19_12 := (bits >>> 12) &&& 0xFF
  (imm20 <<< 31) ||| (imm19_12 <<< 12) ||| (imm11 <<< 20) ||| (imm10_1 <<< 21)

/-- Encode an R-type instruction -/
def encodeR (defs : List InstructionDef) (op : OpType) (rd rs1 rs2 : Fin 32) : Option UInt32 :=
  (opTypeToInstrDef defs op).map fun d =>
    d.matchBits ||| packRd rd ||| packRs1 rs1 ||| packRs2 rs2

/-- Encode an I-type instruction -/
def encodeI (defs : List InstructionDef) (op : OpType) (rd rs1 : Fin 32) (imm : Int) : Option UInt32 :=
  (opTypeToInstrDef defs op).map fun d =>
    d.matchBits ||| packRd rd ||| packRs1 rs1 ||| packImmI imm

/-- Encode an S-type instruction -/
def encodeS (defs : List InstructionDef) (op : OpType) (rs1 rs2 : Fin 32) (imm : Int) : Option UInt32 :=
  (opTypeToInstrDef defs op).map fun d =>
    d.matchBits ||| packRs1 rs1 ||| packRs2 rs2 ||| packImmS imm

/-- Encode a B-type instruction -/
def encodeB (defs : List InstructionDef) (op : OpType) (rs1 rs2 : Fin 32) (offset : Int) : Option UInt32 :=
  (opTypeToInstrDef defs op).map fun d =>
    d.matchBits ||| packRs1 rs1 ||| packRs2 rs2 ||| packImmB offset

/-- Encode a U-type instruction -/
def encodeU (defs : List InstructionDef) (op : OpType) (rd : Fin 32) (imm : UInt32) : Option UInt32 :=
  (opTypeToInstrDef defs op).map fun d =>
    d.matchBits ||| packRd rd ||| packImmU imm

/-- Encode a J-type instruction -/
def encodeJ (defs : List InstructionDef) (op : OpType) (rd : Fin 32) (offset : Int) : Option UInt32 :=
  (opTypeToInstrDef defs op).map fun d =>
    d.matchBits ||| packRd rd ||| packImmJ offset

end Shoumei.RISCV
