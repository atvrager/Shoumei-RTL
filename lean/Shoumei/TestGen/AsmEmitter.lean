/-
  RISC-V Assembly Emitter

  Generates human-readable .S assembly files from symbolic instruction lists.
  Uses mnemonics (not encoded words) so output is debuggable with objdump.
-/

import Shoumei.RISCV.ISA

namespace Shoumei.TestGen

/-- Register name: x0..x31 -/
def regName (r : Fin 32) : String := s!"x{r.val}"

/-- FP register name: f0..f31 -/
def fregName (r : Fin 32) : String := s!"f{r.val}"

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
  -- F extension: FP register names use f0..f31
  | frtype (mnem : String) (fd fs1 fs2 : Fin 32)       -- fadd.s fd, fs1, fs2
  | fr4type (mnem : String) (fd fs1 fs2 fs3 : Fin 32)  -- fmadd.s fd, fs1, fs2, fs3
  | flw (fd rs1 : Fin 32) (offset : Int)                -- flw fd, offset(rs1)
  | fsw (fs2 rs1 : Fin 32) (offset : Int)               -- fsw fs2, offset(rs1)
  | fcvt_to_int (mnem : String) (rd : Fin 32) (fs1 : Fin 32)  -- fcvt.w.s rd, fs1
  | fcvt_from_int (mnem : String) (fd : Fin 32) (rs1 : Fin 32) -- fcvt.s.w fd, rs1
  | fmv_to_int (rd : Fin 32) (fs1 : Fin 32)             -- fmv.x.w rd, fs1
  | fmv_from_int (fd : Fin 32) (rs1 : Fin 32)           -- fmv.w.x fd, rs1
  | fcmp (mnem : String) (rd : Fin 32) (fs1 fs2 : Fin 32) -- feq.s rd, fs1, fs2

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
  | .frtype mnem fd fs1 fs2 => s!"    {mnem} {fregName fd}, {fregName fs1}, {fregName fs2}"
  | .fr4type mnem fd fs1 fs2 fs3 => s!"    {mnem} {fregName fd}, {fregName fs1}, {fregName fs2}, {fregName fs3}"
  | .flw fd rs1 off => s!"    flw {fregName fd}, {off}({regName rs1})"
  | .fsw fs2 rs1 off => s!"    fsw {fregName fs2}, {off}({regName rs1})"
  | .fcvt_to_int mnem rd fs1 => s!"    {mnem} {regName rd}, {fregName fs1}"
  | .fcvt_from_int mnem fd rs1 => s!"    {mnem} {fregName fd}, {regName rs1}"
  | .fmv_to_int rd fs1 => s!"    fmv.x.w {regName rd}, {fregName fs1}"
  | .fmv_from_int fd rs1 => s!"    fmv.w.x {fregName fd}, {regName rs1}"
  | .fcmp mnem rd fs1 fs2 => s!"    {mnem} {regName rd}, {fregName fs1}, {fregName fs2}"

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

/-- Fail epilogue: write 0xDEAD to tohost (distinct from PASS=1) -/
def failEpilogue (failLabel : String) : List AsmInstr :=
  [ .label failLabel
  , .comment "FAIL: write 0xDEAD to tohost"
  , .pseudo "li x30, 0x1000"
  , .pseudo "li x31, 0xDEAD"
  , .stype "sw" ⟨31, by omega⟩ ⟨30, by omega⟩ 0
  , .label ".Lhalt_fail"
  , .pseudo "j .Lhalt_fail" ]

/-- Render a TestProgram to a complete .S file -/
def TestProgram.toAsm (prog : TestProgram) : String :=
  let header := s!"# Auto-generated test: {prog.name}\n# {prog.description}\n"
  let directives := ".section .text\n.globl _start\n_start:\n.globl main\nmain:\n"
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
  | .FENCE => "fence" | .FENCE_I => "fence.i" | .ECALL => "ecall" | .EBREAK => "ebreak"
  | .MUL => "mul" | .MULH => "mulh" | .MULHSU => "mulhsu" | .MULHU => "mulhu"
  | .DIV => "div" | .DIVU => "divu" | .REM => "rem" | .REMU => "remu"
  -- F extension
  | .FADD_S => "fadd.s" | .FSUB_S => "fsub.s" | .FMUL_S => "fmul.s"
  | .FDIV_S => "fdiv.s" | .FSQRT_S => "fsqrt.s"
  | .FMADD_S => "fmadd.s" | .FMSUB_S => "fmsub.s"
  | .FNMADD_S => "fnmadd.s" | .FNMSUB_S => "fnmsub.s"
  | .FEQ_S => "feq.s" | .FLT_S => "flt.s" | .FLE_S => "fle.s"
  | .FCVT_W_S => "fcvt.w.s" | .FCVT_WU_S => "fcvt.wu.s"
  | .FCVT_S_W => "fcvt.s.w" | .FCVT_S_WU => "fcvt.s.wu"
  | .FMV_X_W => "fmv.x.w" | .FMV_W_X => "fmv.w.x" | .FCLASS_S => "fclass.s"
  | .FMIN_S => "fmin.s" | .FMAX_S => "fmax.s"
  | .FSGNJ_S => "fsgnj.s" | .FSGNJN_S => "fsgnjn.s" | .FSGNJX_S => "fsgnjx.s"
  | .FLW => "flw" | .FSW => "fsw"
  -- Zicsr
  | .CSRRW => "csrrw" | .CSRRS => "csrrs" | .CSRRC => "csrrc"
  | .CSRRWI => "csrrwi" | .CSRRSI => "csrrsi" | .CSRRCI => "csrrci"

end Shoumei.TestGen
