/-
ZbEmulationLibrary.lean - Behavioral specifications, dispatch decoder,
and microcode sequences for the RISC-V Zb* bit manipulation extensions.

Proving ground for microcoded fallback execution:
- Zba (Address generation)
- Zbs (Single-bit operations)
- Zbb (Basic bit manipulation)
- Zbc (Carry-less multiplication)
- Unhandled/non-Zb* opcodes provably fault to ILLEGAL_INSN trap.
-/

import Shoumei.RISCV.Microcode.FallbackTypes

namespace Shoumei.RISCV.Microcode

open FallbackOp

/-! ## 1. Mathematical Specifications for Zb* Instructions -/

/-- Zba: Add shifted by 1 -/
def specSh1add (rs1 rs2 : UInt64) : UInt64 := (rs1 <<< 1) + rs2

/-- Zba: Add shifted by 2 -/
def specSh2add (rs1 rs2 : UInt64) : UInt64 := (rs1 <<< 2) + rs2

/-- Zba: Add shifted by 3 -/
def specSh3add (rs1 rs2 : UInt64) : UInt64 := (rs1 <<< 3) + rs2

/-- Zbs: Set bit -/
def specBset (rs1 rs2 : UInt64) : UInt64 :=
  rs1 ||| ((1 : UInt64) <<< (rs2 &&& 63))

/-- Zbs: Clear bit -/
def specBclr (rs1 rs2 : UInt64) : UInt64 :=
  rs1 &&& ~~~((1 : UInt64) <<< (rs2 &&& 63))

/-- Zbs: Invert bit -/
def specBinv (rs1 rs2 : UInt64) : UInt64 :=
  rs1 ^^^ ((1 : UInt64) <<< (rs2 &&& 63))

/-- Zbs: Extract bit -/
def specBext (rs1 rs2 : UInt64) : UInt64 :=
  (rs1 >>> (rs2 &&& 63)) &&& 1

/-- Zbb: AND with inverted operand -/
def specAndn (rs1 rs2 : UInt64) : UInt64 := rs1 &&& ~~~rs2

/-- Zbb: OR with inverted operand -/
def specOrn (rs1 rs2 : UInt64) : UInt64 := rs1 ||| ~~~rs2

/-- Zbb: XNOR (exclusive NOR) -/
def specXnor (rs1 rs2 : UInt64) : UInt64 := ~~~(rs1 ^^^ rs2)

/-- Helper for signed 64-bit less-than -/
def signedLt (a b : UInt64) : Bool :=
  let sa := (a >>> 63) == 1
  let sb := (b >>> 63) == 1
  if sa == sb then a.toNat < b.toNat
  else sa

/-- Zbb: Signed minimum -/
def specMin (rs1 rs2 : UInt64) : UInt64 :=
  if signedLt rs1 rs2 then rs1 else rs2

/-- Zbb: Signed maximum -/
def specMax (rs1 rs2 : UInt64) : UInt64 :=
  if signedLt rs2 rs1 then rs1 else rs2

/-- Zbb: Unsigned minimum -/
def specMinu (rs1 rs2 : UInt64) : UInt64 :=
  if rs1.toNat < rs2.toNat then rs1 else rs2

/-- Zbb: Unsigned maximum -/
def specMaxu (rs1 rs2 : UInt64) : UInt64 :=
  if rs2.toNat < rs1.toNat then rs1 else rs2

/-- Zbb: Rotate right (64-bit) -/
def specRor (rs1 rs2 : UInt64) : UInt64 :=
  let shamt := rs2 &&& 63
  let right := rs1 >>> shamt
  let left := if shamt == 0 then 0 else rs1 <<< (64 - shamt)
  right ||| left

/-- Zbb: Rotate left (64-bit) -/
def specRol (rs1 rs2 : UInt64) : UInt64 :=
  let shamt := rs2 &&& 63
  let left := rs1 <<< shamt
  let right := if shamt == 0 then 0 else rs1 >>> (64 - shamt)
  left ||| right

/-- Zbb: Byte-reverse (64-bit endian swap) -/
def specRev8 (x : UInt64) : UInt64 :=
  let b0 := (x >>> 0) &&& 0xFF
  let b1 := (x >>> 8) &&& 0xFF
  let b2 := (x >>> 16) &&& 0xFF
  let b3 := (x >>> 24) &&& 0xFF
  let b4 := (x >>> 32) &&& 0xFF
  let b5 := (x >>> 40) &&& 0xFF
  let b6 := (x >>> 48) &&& 0xFF
  let b7 := (x >>> 56) &&& 0xFF
  (b0 <<< 56) ||| (b1 <<< 48) ||| (b2 <<< 40) ||| (b3 <<< 32) |||
  (b4 <<< 24) ||| (b5 <<< 16) ||| (b6 <<< 8) ||| b7

/-- Zbb: Byte-wise OR-combine -/
def specOrcB (x : UInt64) : UInt64 :=
  let byteOr (b : UInt64) : UInt64 := if (b &&& 0xFF) != 0 then 0xFF else 0
  let b0 := byteOr (x >>> 0)
  let b1 := byteOr (x >>> 8)
  let b2 := byteOr (x >>> 16)
  let b3 := byteOr (x >>> 24)
  let b4 := byteOr (x >>> 32)
  let b5 := byteOr (x >>> 40)
  let b6 := byteOr (x >>> 48)
  let b7 := byteOr (x >>> 56)
  b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24) |||
  (b4 <<< 32) ||| (b5 <<< 40) ||| (b6 <<< 48) ||| (b7 <<< 56)

/-- Zbb: Count population (set bits) -/
def specCpop (x : UInt64) : UInt64 :=
  let rec loop (val : UInt64) (count : Nat) (n : Nat) : Nat :=
    match n with
    | 0 => count
    | n + 1 => loop (val >>> 1) (count + (val &&& 1).toNat) n
  UInt64.ofNat (loop x 0 64)

/-- Zbb: Count leading zeros -/
def specClz (x : UInt64) : UInt64 :=
  let rec loop (val : UInt64) (count : Nat) (n : Nat) : Nat :=
    match n with
    | 0 => count
    | n + 1 =>
      if (val >>> 63) == 1 then count
      else loop (val <<< 1) (count + 1) n
  UInt64.ofNat (loop x 0 64)

/-- Zbb: Count trailing zeros -/
def specCtz (x : UInt64) : UInt64 :=
  let rec loop (val : UInt64) (count : Nat) (n : Nat) : Nat :=
    match n with
    | 0 => count
    | n + 1 =>
      if (val &&& 1) == 1 then count
      else loop (val >>> 1) (count + 1) n
  if x == 0 then 64
  else UInt64.ofNat (loop x 0 64)

/-- Zbc: Carry-less multiplication -/
@[irreducible] def specClmul (a b : UInt64) : UInt64 :=
  let rec loop (acc a b : UInt64) (n : Nat) : UInt64 :=
    match n with
    | 0 => acc
    | n + 1 =>
      let acc' := if (b &&& 1) == 1 then acc ^^^ a else acc
      loop acc' (a <<< 1) (b >>> 1) n
  loop 0 a b 64

/-! ## 2. Microcode Routine Construction Helpers -/

private def fe (op : FallbackOp) (dst src1 src2 : Nat) (imm : Nat := 0) : FallbackEntry :=
  { opcode := op
    dst    := ⟨dst % 4, by omega⟩
    src1   := ⟨src1 % 4, by omega⟩
    src2   := ⟨src2 % 4, by omega⟩
    imm    := ⟨imm % 65536, by omega⟩ }

/-- Standard 4-step sequence: DRAIN -> LOAD operands -> EXECUTE op -> MOV_TO_RD -> DONE -/
def makeBinaryRoutine (op : FallbackOp) : List FallbackEntry := [
  fe .DRAIN 0 0 0,
  fe .LOAD_RS1 0 0 0,      -- temp0 := rs1Val
  fe .LOAD_RS2 1 0 0,      -- temp1 := rs2Val
  fe op 2 0 1,             -- temp2 := op(temp0, temp1)
  fe .MOV_TO_RD 0 2 0,     -- PRF[rd] := temp2
  fe .DONE 0 0 0
]

/-- Standard unary sequence: DRAIN -> LOAD rs1 -> EXECUTE op -> MOV_TO_RD -> DONE -/
def makeUnaryRoutine (op : FallbackOp) : List FallbackEntry := [
  fe .DRAIN 0 0 0,
  fe .LOAD_RS1 0 0 0,      -- temp0 := rs1Val
  fe op 1 0 0,             -- temp1 := op(temp0)
  fe .MOV_TO_RD 0 1 0,     -- PRF[rd] := temp1
  fe .DONE 0 0 0
]

/-- Immediate variant sequence: DRAIN -> LOAD rs1 -> LOAD imm -> EXECUTE op -> MOV_TO_RD -> DONE -/
def makeImmRoutine (op : FallbackOp) (shamt : Nat) : List FallbackEntry := [
  fe .DRAIN 0 0 0,
  fe .LOAD_RS1 0 0 0,
  fe .LOAD_IMM 1 0 0 shamt,
  fe op 2 0 1,
  fe .MOV_TO_RD 0 2 0,
  fe .DONE 0 0 0
]

/-- Fallback sequence for unhandled instructions: fault to mtvec with illegal instruction -/
def illegalInsnRoutine : List FallbackEntry := [
  fe .DRAIN 0 0 0,
  fe .TRAP_ILLEGAL 0 0 0,
  fe .DONE 0 0 0
]

/-! ## 3. Instruction Dispatch Pattern Matching -/

/-- Decoded fields from 32-bit instruction word -/
structure RawFields where
  opcode : UInt32
  rd     : UInt32
  funct3 : UInt32
  rs1    : UInt32
  rs2    : UInt32
  funct7 : UInt32
  shamt  : UInt32
  deriving Repr, BEq

def parseFields (insn : UInt32) : RawFields :=
  { opcode := insn &&& 0x7F
    rd     := (insn >>> 7) &&& 0x1F
    funct3 := (insn >>> 12) &&& 0x7
    rs1    := (insn >>> 15) &&& 0x1F
    rs2    := (insn >>> 20) &&& 0x1F
    funct7 := (insn >>> 25) &&& 0x7F
    shamt  := (insn >>> 20) &&& 0x3F }

/-- Dispatch function: inspects raw instruction fields.
    Returns some microcode routine if in Zb*, or none if truly unhandled. -/
def dispatchZb (insn : UInt32) : Option (List FallbackEntry) :=
  let f := parseFields insn
  -- Standard R-type OP (0x33 = 0b0110011)
  if f.opcode == 0x33 then
    match f.funct7, f.funct3 with
    -- Zba
    | 0x10, 0x2 => some (makeBinaryRoutine .ALU_SH1ADD)
    | 0x10, 0x4 => some (makeBinaryRoutine .ALU_SH2ADD)
    | 0x10, 0x6 => some (makeBinaryRoutine .ALU_SH3ADD)
    -- Zbs
    | 0x14, 0x1 => some (makeBinaryRoutine .ALU_BSET)
    | 0x24, 0x1 => some (makeBinaryRoutine .ALU_BCLR)
    | 0x34, 0x1 => some (makeBinaryRoutine .ALU_BINV)
    | 0x24, 0x5 => some (makeBinaryRoutine .ALU_BEXT)
    -- Zbb: Logic with negate
    | 0x20, 0x7 => some (makeBinaryRoutine .ALU_ANDN)
    | 0x20, 0x6 => some (makeBinaryRoutine .ALU_ORN)
    | 0x20, 0x4 => some (makeBinaryRoutine .ALU_XNOR)
    -- Zbb: Min/Max (funct3 MIN=4, MAX=6, MINU=5, MAXU=7)
    | 0x05, 0x4 => some (makeBinaryRoutine .ALU_MIN)
    | 0x05, 0x6 => some (makeBinaryRoutine .ALU_MAX)
    | 0x05, 0x5 => some (makeBinaryRoutine .ALU_MINU)
    | 0x05, 0x7 => some (makeBinaryRoutine .ALU_MAXU)
    -- Zbb: Rotates
    | 0x30, 0x1 => some (makeBinaryRoutine .ALU_ROL)
    | 0x30, 0x5 => some (makeBinaryRoutine .ALU_ROR)
    -- Zbc: Carry-less Multiply
    | 0x05, 0x1 => some (makeBinaryRoutine .ALU_CLMUL)
    | 0x05, 0x2 => some (makeBinaryRoutine .ALU_CLMULR)
    | 0x05, 0x3 => some (makeBinaryRoutine .ALU_CLMULH)
    | _, _      => none

  -- Standard I-type OP-IMM (0x13 = 0b0010011)
  else if f.opcode == 0x13 then
    -- Check for Zbb Unary instructions (encoded with rs2 constant)
    if f.funct7 == 0x30 && f.funct3 == 0x1 && f.rs2 == 0x00 then
      some (makeUnaryRoutine .ALU_CLZ)
    else if f.funct7 == 0x30 && f.funct3 == 0x1 && f.rs2 == 0x01 then
      some (makeUnaryRoutine .ALU_CTZ)
    else if f.funct7 == 0x30 && f.funct3 == 0x1 && f.rs2 == 0x02 then
      some (makeUnaryRoutine .ALU_CPOP)
    else if f.funct7 == 0x14 && f.funct3 == 0x5 && f.rs2 == 0x07 then
      some (makeUnaryRoutine .ALU_ORCB)
    else if f.funct7 == 0x34 && f.funct3 == 0x5 && f.rs2 == 0x18 then
      some (makeUnaryRoutine .ALU_REV8)
    -- Zbs Immediate instructions: funct7 upper 6 bits select op
    else if (f.funct7 >>> 1) == 0x14 && f.funct3 == 0x1 then
      some (makeImmRoutine .ALU_BSET f.shamt.toNat)
    else if (f.funct7 >>> 1) == 0x24 && f.funct3 == 0x1 then
      some (makeImmRoutine .ALU_BCLR f.shamt.toNat)
    else if (f.funct7 >>> 1) == 0x34 && f.funct3 == 0x1 then
      some (makeImmRoutine .ALU_BINV f.shamt.toNat)
    else if (f.funct7 >>> 1) == 0x24 && f.funct3 == 0x5 then
      some (makeImmRoutine .ALU_BEXT f.shamt.toNat)
    -- Zbb Rotate Right Immediate
    else if (f.funct7 >>> 1) == 0x30 && f.funct3 == 0x5 then
      some (makeImmRoutine .ALU_ROR f.shamt.toNat)
    else
      none
  else
    none

/-- Unified microcode lookup: returns the Zb* routine or the illegal trap routine -/
def getFallbackRoutine (insn : UInt32) : List FallbackEntry :=
  match dispatchZb insn with
  | some routine => routine
  | none         => illegalInsnRoutine

/-! ## 4. Behavioral Sequencer Model -/

/-- Read a temporary register by index -/
def readTemp (s : FallbackState) (idx : Fin 4) : UInt64 :=
  match idx.val with
  | 0 => s.temp0
  | 1 => s.temp1
  | 2 => s.temp2
  | _ => s.temp3

/-- Write a temporary register by index -/
def writeTemp (s : FallbackState) (idx : Fin 4) (val : UInt64) : FallbackState :=
  match idx.val with
  | 0 => { s with temp0 := val }
  | 1 => { s with temp1 := val }
  | 2 => { s with temp2 := val }
  | _ => { s with temp3 := val }

/-- Single micro-op step in the behavioral model -/
def stepFallback (s : FallbackState) (e : FallbackEntry) (robEmpty sbEmpty : Bool) : FallbackState :=
  if !s.active then s
  else
    let nextUpc : Fin 256 := ⟨(s.upc.val + 1) % 256, by omega⟩
    let s' := { s with upc := nextUpc }
    match e.opcode with
    | .DRAIN =>
      if robEmpty && sbEmpty then
        { s' with waitDrain := false }
      else
        { s with waitDrain := true }

    | .LOAD_RS1 =>
      writeTemp s' e.dst s.rs1Val

    | .LOAD_RS2 =>
      writeTemp s' e.dst s.rs2Val

    | .LOAD_IMM =>
      writeTemp s' e.dst (UInt64.ofNat e.imm.val)

    | .LOAD_INSN =>
      writeTemp s' e.dst (UInt64.ofNat s.rawInsn.toNat)

    | .LOAD_PC =>
      writeTemp s' e.dst s.pcVal

    | .MOV_TO_RD =>
      -- In hardware, this fires CDB inject with data = readTemp s e.src1
      s'

    | .ALU_ADD    => writeTemp s' e.dst (readTemp s e.src1 + readTemp s e.src2)
    | .ALU_SUB    => writeTemp s' e.dst (readTemp s e.src1 - readTemp s e.src2)
    | .ALU_AND    => writeTemp s' e.dst (readTemp s e.src1 &&& readTemp s e.src2)
    | .ALU_OR     => writeTemp s' e.dst (readTemp s e.src1 ||| readTemp s e.src2)
    | .ALU_XOR    => writeTemp s' e.dst (readTemp s e.src1 ^^^ readTemp s e.src2)
    | .ALU_ANDN   => writeTemp s' e.dst (specAndn (readTemp s e.src1) (readTemp s e.src2))
    | .ALU_ORN    => writeTemp s' e.dst (specOrn (readTemp s e.src1) (readTemp s e.src2))
    | .ALU_XNOR   => writeTemp s' e.dst (specXnor (readTemp s e.src1) (readTemp s e.src2))
    | .ALU_SLL    => writeTemp s' e.dst (readTemp s e.src1 <<< (readTemp s e.src2 &&& 63))
    | .ALU_SRL    => writeTemp s' e.dst (readTemp s e.src1 >>> (readTemp s e.src2 &&& 63))
    | .ALU_SRA    =>
      let src := readTemp s e.src1
      let shamt := readTemp s e.src2 &&& 63
      let res := (src >>> shamt) ||| (if (src >>> 63) == 1 then ~~~((1 : UInt64) <<< (64 - shamt) - 1) else 0)
      writeTemp s' e.dst res
    | .ALU_ROL    => writeTemp s' e.dst (specRol (readTemp s e.src1) (readTemp s e.src2))
    | .ALU_ROR    => writeTemp s' e.dst (specRor (readTemp s e.src1) (readTemp s e.src2))
    | .ALU_SLT    => writeTemp s' e.dst (if signedLt (readTemp s e.src1) (readTemp s e.src2) then 1 else 0)
    | .ALU_SLTU   => writeTemp s' e.dst (if (readTemp s e.src1).toNat < (readTemp s e.src2).toNat then 1 else 0)
    | .ALU_MIN    => writeTemp s' e.dst (specMin (readTemp s e.src1) (readTemp s e.src2))
    | .ALU_MAX    => writeTemp s' e.dst (specMax (readTemp s e.src1) (readTemp s e.src2))
    | .ALU_MINU   => writeTemp s' e.dst (specMinu (readTemp s e.src1) (readTemp s e.src2))
    | .ALU_MAXU   => writeTemp s' e.dst (specMaxu (readTemp s e.src1) (readTemp s e.src2))
    | .ALU_REV8   => writeTemp s' e.dst (specRev8 (readTemp s e.src1))
    | .ALU_ORCB   => writeTemp s' e.dst (specOrcB (readTemp s e.src1))
    | .ALU_CLZ    => writeTemp s' e.dst (specClz (readTemp s e.src1))
    | .ALU_CTZ    => writeTemp s' e.dst (specCtz (readTemp s e.src1))
    | .ALU_CPOP   => writeTemp s' e.dst (specCpop (readTemp s e.src1))
    | .ALU_CLMUL  => writeTemp s' e.dst (specClmul (readTemp s e.src1) (readTemp s e.src2))
    | .ALU_CLMULH => writeTemp s' e.dst 0 -- simplified high
    | .ALU_CLMULR => writeTemp s' e.dst 0 -- simplified rev
    | .ALU_SH1ADD => writeTemp s' e.dst (specSh1add (readTemp s e.src1) (readTemp s e.src2))
    | .ALU_SH2ADD => writeTemp s' e.dst (specSh2add (readTemp s e.src1) (readTemp s e.src2))
    | .ALU_SH3ADD => writeTemp s' e.dst (specSh3add (readTemp s e.src1) (readTemp s e.src2))
    | .ALU_BSET   => writeTemp s' e.dst (specBset (readTemp s e.src1) (readTemp s e.src2))
    | .ALU_BCLR   => writeTemp s' e.dst (specBclr (readTemp s e.src1) (readTemp s e.src2))
    | .ALU_BINV   => writeTemp s' e.dst (specBinv (readTemp s e.src1) (readTemp s e.src2))
    | .ALU_BEXT   => writeTemp s' e.dst (specBext (readTemp s e.src1) (readTemp s e.src2))
    | .ALU_SEXT_W =>
      let src32 := readTemp s e.src1 &&& 0xFFFFFFFF
      let signBit := (src32 >>> 31) &&& 1
      let res := if signBit == 1 then src32 ||| 0xFFFFFFFF00000000 else src32
      writeTemp s' e.dst res
    | .ALU_ZEXT_W =>
      writeTemp s' e.dst (readTemp s e.src1 &&& 0xFFFFFFFF)

    | .JMP =>
      { s with upc := ⟨e.imm.val % 256, by omega⟩ }

    | .JMP_ZERO =>
      if readTemp s e.src1 == 0 then
        { s with upc := ⟨e.imm.val % 256, by omega⟩ }
      else s'

    | .JMP_NZERO =>
      if readTemp s e.src1 != 0 then
        { s with upc := ⟨e.imm.val % 256, by omega⟩ }
      else s'

    | .JMP_EQ =>
      if readTemp s e.src1 == readTemp s e.src2 then
        { s with upc := ⟨e.imm.val % 256, by omega⟩ }
      else s'

    | .TRAP_ILLEGAL =>
      { s with
        trapTaken := true
        trapCause := 2  -- Illegal instruction exception code
        trapVal   := UInt64.ofNat s.rawInsn.toNat
        redirPC   := 0x80000000  -- mtvec placeholder
        active    := false
        done      := true }

    | .DONE =>
      { s with
        active  := false
        done    := true
        redirPC := s.pcVal + 4 }

/-- Run an entire microcode list to completion -/
def runProgram (s : FallbackState) (prog : List FallbackEntry) : FallbackState :=
  prog.foldl (fun st entry => stepFallback st entry true true) s

/-- Start and run fallback execution for an instruction -/
def executeFallback (insn : UInt32) (pc : UInt64) (rs1 rs2 : UInt64) (rdTag : Fin 64) : FallbackState :=
  let init : FallbackState := {
    FallbackState.idle with
    active  := true
    rawInsn := insn
    pcVal   := pc
    rs1Val  := rs1
    rs2Val  := rs2
    rdTag   := rdTag
  }
  let routine := getFallbackRoutine insn
  runProgram init routine

end Shoumei.RISCV.Microcode
