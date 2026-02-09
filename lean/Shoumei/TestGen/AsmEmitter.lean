/-
  RISC-V Assembly Emitter

  Generates human-readable .S assembly files from symbolic instruction lists.
  Uses mnemonics (not encoded words) so output is debuggable with objdump.
-/

import Shoumei.RISCV.ISA

namespace Shoumei.TestGen

/-- Register name: x0..x31 -/
def regName (r : Fin 32) : String := s!"x{r.val}"

/-- Symbolic assembly instruction -/
inductive AsmInstr where
  | rtype (mnem : String) (rd rs1 rs2 : Fin 32)
  | itype (mnem : String) (rd rs1 : Fin 32) (imm : Int)
  | load (mnem : String) (rd rs1 : Fin 32) (offset : Int)
  | stype (mnem : String) (rs2 rs1 : Fin 32) (imm : Int)
  | btype (mnem : String) (rs1 rs2 : Fin 32) (label : String)
  | utype (mnem : String) (rd : Fin 32) (imm : UInt32)
  | jtype (mnem : String) (rd : Fin 32) (label : String)
  | label (name : String)
  | pseudo (text : String)
  | comment (text : String)
  | blank

/-- Convert Nat to hex string -/
private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

private def toHex (n : Nat) : String :=
  if n == 0 then "0"
  else
    let rec go (n : Nat) (acc : String) : String :=
      if _h : n == 0 then acc
      else go (n / 16) ((hexDigit (n % 16)).toString ++ acc)
    decreasing_by simp_all; omega
    go n ""

/-- Render a single instruction to assembly text -/
def AsmInstr.toAsm : AsmInstr → String
  | .rtype mnem rd rs1 rs2 => s!"    {mnem} {regName rd}, {regName rs1}, {regName rs2}"
  | .itype mnem rd rs1 imm => s!"    {mnem} {regName rd}, {regName rs1}, {imm}"
  | .load mnem rd rs1 off  => s!"    {mnem} {regName rd}, {off}({regName rs1})"
  | .stype mnem rs2 rs1 imm => s!"    {mnem} {regName rs2}, {imm}({regName rs1})"
  | .btype mnem rs1 rs2 lbl => s!"    {mnem} {regName rs1}, {regName rs2}, {lbl}"
  | .utype mnem rd imm => s!"    {mnem} {regName rd}, 0x{toHex (imm.toNat / 4096)}"
  | .jtype mnem rd lbl => s!"    {mnem} {regName rd}, {lbl}"
  | .label name => s!"{name}:"
  | .pseudo text => s!"    {text}"
  | .comment text => s!"    # {text}"
  | .blank => ""

/-- A complete test program -/
structure TestProgram where
  name : String
  description : String
  instrs : List AsmInstr

/-- Pass epilogue: write 1 to tohost at 0x1000 -/
def passEpilogue : List AsmInstr :=
  [ .blank
  , .comment "PASS: write 1 to tohost"
  , .pseudo "li x1, 0x1000"
  , .pseudo "li x2, 1"
  , .stype "sw" ⟨2, by omega⟩ ⟨1, by omega⟩ 0
  , .label ".Lhalt"
  , .pseudo "j .Lhalt" ]

/-- Fail epilogue: write test_num << 1 | 1 to tohost -/
def failEpilogue (failLabel : String) (testReg : Fin 32) : List AsmInstr :=
  [ .label failLabel
  , .comment "FAIL: write (test_num << 1) | 1 to tohost"
  , .itype "slli" testReg testReg 1
  , .itype "ori" testReg testReg 1
  , .pseudo "li x1, 0x1000"
  , .stype "sw" testReg ⟨1, by omega⟩ 0
  , .label ".Lhalt_fail"
  , .pseudo "j .Lhalt_fail" ]

/-- Render a TestProgram to a complete .S file -/
def TestProgram.toAsm (prog : TestProgram) : String :=
  let header := s!"# Auto-generated test: {prog.name}\n# {prog.description}\n"
  let directives := ".section .text\n.globl main\nmain:\n"
  let body := prog.instrs.map AsmInstr.toAsm |>.foldl (· ++ "\n" ++ ·) ""
  header ++ directives ++ body ++ "\n"

/-- Map OpType to assembly mnemonic -/
def opTypeToMnemonic : Shoumei.RISCV.OpType → String
  | .ADD => "add" | .SUB => "sub" | .AND => "and" | .OR => "or" | .XOR => "xor"
  | .SLT => "slt" | .SLTU => "sltu" | .SLL => "sll" | .SRL => "srl" | .SRA => "sra"
  | .ADDI => "addi" | .ANDI => "andi" | .ORI => "ori" | .XORI => "xori"
  | .SLTI => "slti" | .SLTIU => "sltiu" | .SLLI => "slli" | .SRLI => "srli" | .SRAI => "srai"
  | .BEQ => "beq" | .BNE => "bne" | .BLT => "blt" | .BGE => "bge"
  | .BLTU => "bltu" | .BGEU => "bgeu"
  | .JAL => "jal" | .JALR => "jalr"
  | .LB => "lb" | .LH => "lh" | .LW => "lw" | .LBU => "lbu" | .LHU => "lhu"
  | .SB => "sb" | .SH => "sh" | .SW => "sw"
  | .LUI => "lui" | .AUIPC => "auipc"
  | .FENCE => "fence" | .ECALL => "ecall" | .EBREAK => "ebreak"
  | .MUL => "mul" | .MULH => "mulh" | .MULHSU => "mulhsu" | .MULHU => "mulhu"
  | .DIV => "div" | .DIVU => "divu" | .REM => "rem" | .REMU => "remu"

end Shoumei.TestGen
