/-
ZbEmulationLibrary.lean - Behavioral specifications, the emulated-instruction
table, the microcode control store and the dispatch decoder for the RISC-V Zb*
bit manipulation extensions.

Proving ground for microcoded fallback execution:
- Zba (Address generation)
- Zbs (Single-bit operations)
- Zbb (Basic bit manipulation)
- Zbc (Carry-less multiplication)
- Unhandled/non-Zb* opcodes provably fault to ILLEGAL_INSN trap.

All 43 emulated encodings live in one table (`zbTable`).  The software decoder
(`routineIndex`), the FallbackSequencer's hardware encoder, the benchmark specs
and the equivalence proofs all read that single list, so a decoder and its
routine cannot drift apart.
-/

import Shoumei.RISCV.Microcode.FallbackTypes

namespace Shoumei.RISCV.Microcode

open FallbackOp

/-! ## 1. Micro-ALU primitive specifications

One spec per micro-ALU operation the Zb* routines invoke.  `stepFallback` calls
these, so a routine's result is definitionally its spec and the equivalence
proofs close by `rfl`. -/

/-- 64-bit add -/
def specAdd (a b : UInt64) : UInt64 := a + b

/-- 64-bit subtract -/
def specSub (a b : UInt64) : UInt64 := a - b

/-- Logical shift left by the low 6 bits of `b` -/
def specSll (a b : UInt64) : UInt64 := a <<< (b &&& 63)

/-- Logical shift right by the low 6 bits of `b` -/
def specSrl (a b : UInt64) : UInt64 := a >>> (b &&& 63)

/-- Arithmetic shift right by the low 6 bits of `b`.

    Written so that `s == 0` is the identity: a 6-stage barrel shifter performs
    no stage when the shift amount is zero, so no sign fill may be applied. -/
def specSra (a b : UInt64) : UInt64 :=
  let s := b &&& 63
  let fill := if s == 0 then 0 else ~~~(((1 : UInt64) <<< (64 - s)) - 1)
  (a >>> s) ||| (if (a >>> 63) == 1 then fill else 0)

/-- Low 32 bits of `x`, zero-extended -/
def specZextW (x : UInt64) : UInt64 := x &&& 0xFFFFFFFF

/-- Sign-extend the low 32 bits of `x` -/
def specSextW (x : UInt64) : UInt64 :=
  let w := x &&& 0xFFFFFFFF
  if (w >>> 31) &&& 1 == 1 then w ||| 0xFFFFFFFF00000000 else w

/-- Sign-extend a 32-bit value -/
def specSext32 (v : UInt64) : UInt64 :=
  let w := v &&& 0xFFFFFFFF
  if (w >>> 31) &&& 1 == 1 then w ||| 0xFFFFFFFF00000000 else w

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

/-- Zbb: Rotate left of the low 32 bits, sign-extended (`rolw`) -/
def specRolw (rs1 rs2 : UInt64) : UInt64 :=
  let x := rs1 &&& 0xFFFFFFFF
  let shamt := rs2 &&& 31
  let left := x <<< shamt
  let right := if shamt == 0 then 0 else x >>> (32 - shamt)
  specSext32 (left ||| right)

/-- Zbb: Rotate right of the low 32 bits, sign-extended (`rorw`/`roriw`) -/
def specRorw (rs1 rs2 : UInt64) : UInt64 :=
  let x := rs1 &&& 0xFFFFFFFF
  let shamt := rs2 &&& 31
  let right := x >>> shamt
  let left := if shamt == 0 then 0 else x <<< (32 - shamt)
  specSext32 (right ||| left)

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

/-- Zbb: `clzw` = `clz` of the zero-extended word, biased by 32 so a zero word
    counts 32 leading zeros. -/
def specClzw (rs1 : UInt64) : UInt64 := specSub (specClz (specZextW rs1)) 32

/-- Zbb: `cpopw` = population count of the low word -/
def specCpopw (rs1 : UInt64) : UInt64 := specCpop (specZextW rs1)

/-- Zbb: `ctzw` = trailing zeros of the low word; 32 for a zero word -/
def specCtzw (rs1 : UInt64) : UInt64 :=
  let x := rs1 &&& 0xFFFFFFFF
  if x == 0 then 32 else specCtz x

/-- Zbb: `sext.b` = `(x << 56) >>a 56` -/
def specSextB (rs1 : UInt64) : UInt64 := specSra (specSll rs1 56) 56

/-- Zbb: `sext.h` = `(x << 48) >>a 48` -/
def specSextH (rs1 : UInt64) : UInt64 := specSra (specSll rs1 48) 48

/-- Zbb: `zext.h` = `(x << 48) >> 48` -/
def specZextH (rs1 : UInt64) : UInt64 := specSrl (specSll rs1 48) 48

/-- Zba: `add.uw` = `zext32(rs1) + rs2`, no sign extension of the result -/
def specAddUw (rs1 rs2 : UInt64) : UInt64 := specAdd (specZextW rs1) rs2

/-- Zba: `sh1add.uw` -/
def specSh1addUw (rs1 rs2 : UInt64) : UInt64 := specSh1add (specZextW rs1) rs2

/-- Zba: `sh2add.uw` -/
def specSh2addUw (rs1 rs2 : UInt64) : UInt64 := specSh2add (specZextW rs1) rs2

/-- Zba: `sh3add.uw` -/
def specSh3addUw (rs1 rs2 : UInt64) : UInt64 := specSh3add (specZextW rs1) rs2

/-- Zba: `slli.uw` = 64-bit shift of the zero-extended word -/
def specSlliUw (rs1 shamt : UInt64) : UInt64 := specSll (specZextW rs1) shamt

/-- Zbc: full 128-bit carry-less product as `(low, high)`.

    `m` walks `a` shifted left one bit per iteration; `b` is consumed from the
    bottom.  Bit `i` of `acc` is the XOR of `a_j & b_k` over `j + k = i`. -/
@[irreducible] def specClmul128 (a b : UInt64) : UInt64 × UInt64 :=
  let rec loop (accLo accHi mLo mHi b : UInt64) (n : Nat) : UInt64 × UInt64 :=
    match n with
    | 0 => (accLo, accHi)
    | n + 1 =>
      let hit := (b &&& 1) == 1
      let accLo' := if hit then accLo ^^^ mLo else accLo
      let accHi' := if hit then accHi ^^^ mHi else accHi
      loop accLo' accHi' (mLo <<< 1) ((mHi <<< 1) ||| (mLo >>> 63)) (b >>> 1) n
  loop 0 0 a 0 b 64

/-- Zbc: `clmul` = low 64 bits of the carry-less product -/
@[irreducible] def specClmul (a b : UInt64) : UInt64 := (specClmul128 a b).1

/-- Zbc: `clmulh` = bits 127:64 of the carry-less product -/
@[irreducible] def specClmulh (a b : UInt64) : UInt64 := (specClmul128 a b).2

/-- Zbc: `clmulr` = bits 126:63 of the carry-less product -/
@[irreducible] def specClmulr (a b : UInt64) : UInt64 :=
  let p := specClmul128 a b
  (p.1 >>> 63) ||| (p.2 <<< 1)

/-! ## 2. The emulated-instruction table -/

/-- Operand shape of an emulated encoding: which fields it carries. -/
inductive ZbShape where
  /-- `rd, rs1, rs2` -/
  | binary
  /-- `rd, rs1, shamt` (immediate forms) -/
  | shift
  /-- `rd, rs1` -/
  | unary
  deriving Repr, BEq, DecidableEq

/-- Control-store entries per routine.  Every Zb* routine is 5..8 micro-ops. -/
abbrev routineStride : Nat := 8

/-- Number of emulated Zb* encodings. -/
abbrev routineCount : Nat := 43

/-- Control-store routine slots: the 43 instructions plus the illegal-instruction
    routine one slot past them. -/
abbrev routineSlots : Nat := 44

/-- Control-store size.  A power of two so the micro-PC is exactly 9 bits;
    slots past `routineSlots` read as `.DONE`. -/
abbrev zbRomSize : Nat := 512

/-- Match mask for the two-register forms: funct7 | rs2 | rs1 | funct3 | opcode.
    Bits 24:20 are free, which also makes this the mask of `roriw`, whose
    shift amount is 5 bits wide. -/
def zbMaskFunct7 : UInt32 := 0xFE00707F

/-- Match mask for the 6-bit-shift-amount forms: funct6 | rs1 | funct3 | opcode.
    Bits 25:20 carry the shift amount and are free. -/
def zbMaskFunct6 : UInt32 := 0xFC00707F

/-- Match mask for the unary forms: bits 31:20 are a fixed funct12. -/
def zbMaskFunct12 : UInt32 := 0xFFF0707F

/-- One emulated Zb* encoding: mnemonic, operand shape, sample encoding, match
    mask, and the micro-ops that emulate it. -/
structure ZbRoutine where
  name   : String
  shape  : ZbShape
  sample : UInt32
  mask   : UInt32
  body   : List FallbackEntry
  deriving Repr

private def fe (op : FallbackOp) (dst src1 src2 : Nat) (imm : Nat := 0) : FallbackEntry :=
  { opcode := op
    dst    := ⟨dst % 4, by omega⟩
    src1   := ⟨src1 % 4, by omega⟩
    src2   := ⟨src2 % 4, by omega⟩
    imm    := ⟨imm % 65536, by omega⟩ }

private def drainE : FallbackEntry := fe .DRAIN 0 0 0
private def doneE  : FallbackEntry := fe .DONE 0 0 0

/-- `DRAIN; LOAD_RS1 t0; LOAD_RS2 t1; <op> t2,t0,t1; MOV_TO_RD t2; DONE` -/
private def bodyBinary (op : FallbackOp) : List FallbackEntry :=
  [drainE, fe .LOAD_RS1 0 0 0, fe .LOAD_RS2 1 0 0, fe op 2 0 1, fe .MOV_TO_RD 0 2 0, doneE]

/-- `DRAIN; LOAD_RS1 t0; LOAD_SHAMT t1; <op> t2,t0,t1; MOV_TO_RD t2; DONE` -/
private def bodyShift (op : FallbackOp) : List FallbackEntry :=
  [drainE, fe .LOAD_RS1 0 0 0, fe .LOAD_SHAMT 1 0 0, fe op 2 0 1, fe .MOV_TO_RD 0 2 0, doneE]

/-- `DRAIN; LOAD_RS1 t0; <op> t1,t0; MOV_TO_RD t1; DONE` -/
private def bodyUnary (op : FallbackOp) : List FallbackEntry :=
  [drainE, fe .LOAD_RS1 0 0 0, fe op 1 0 0, fe .MOV_TO_RD 0 1 0, doneE]

/-- `DRAIN; LOAD_RS1 t0; LOAD_IMM t1,<sh>; SLL t2,t0,t1; SRA/SRL t0,t2,t1;
    MOV_TO_RD t0; DONE` - selecting `sext.b`, `sext.h` or `zext.h`. -/
private def bodyShiftIn (op : FallbackOp) (sh : Nat) : List FallbackEntry :=
  [drainE, fe .LOAD_RS1 0 0 0, fe .LOAD_IMM 1 0 0 sh,
   fe .ALU_SLL 2 0 1, fe op 0 2 1, fe .MOV_TO_RD 0 0 0, doneE]

/-- `DRAIN; LOAD_RS1 t0; LOAD_RS2 t1; ZEXT_W t0,t0; <op> t2,t0,t1;
    MOV_TO_RD t2; DONE` - the `.uw` shifted-add family. -/
private def bodyUw (op : FallbackOp) : List FallbackEntry :=
  [drainE, fe .LOAD_RS1 0 0 0, fe .LOAD_RS2 1 0 0, fe .ALU_ZEXT_W 0 0 0,
   fe op 2 0 1, fe .MOV_TO_RD 0 2 0, doneE]

/-- `DRAIN; LOAD_RS1 t0; ZEXT_W t1,t0; CLZ t1,t1; LOAD_IMM t0,32; SUB t1,t1,t0;
    MOV_TO_RD t1; DONE` - `clzw` as `clz(zext32(x)) - 32`. -/
private def bodyClzw : List FallbackEntry :=
  [drainE, fe .LOAD_RS1 0 0 0, fe .ALU_ZEXT_W 1 0 0, fe .ALU_CLZ 1 1 0,
   fe .LOAD_IMM 0 0 0 32, fe .ALU_SUB 1 1 0, fe .MOV_TO_RD 0 1 0, doneE]

/-- `DRAIN; LOAD_RS1 t0; ZEXT_W t1,t0; CPOP t1,t1; MOV_TO_RD t1; DONE` -/
private def bodyCpopw : List FallbackEntry :=
  [drainE, fe .LOAD_RS1 0 0 0, fe .ALU_ZEXT_W 1 0 0, fe .ALU_CPOP 1 1 0,
   fe .MOV_TO_RD 0 1 0, doneE]

/-- `DRAIN; LOAD_RS1 t0; CTZW t1,t0; MOV_TO_RD t1; DONE` -/
private def bodyCtzw : List FallbackEntry :=
  [drainE, fe .LOAD_RS1 0 0 0, fe .ALU_CTZW 1 0 0, fe .MOV_TO_RD 0 1 0, doneE]

/-- `DRAIN; LOAD_RS1 t0; LOAD_SHAMT t1; ZEXT_W t0,t0; SLL t2,t0,t1;
    MOV_TO_RD t2; DONE` - `slli.uw`. -/
private def bodySlliUw : List FallbackEntry :=
  [drainE, fe .LOAD_RS1 0 0 0, fe .LOAD_SHAMT 1 0 0, fe .ALU_ZEXT_W 0 0 0,
   fe .ALU_SLL 2 0 1, fe .MOV_TO_RD 0 2 0, doneE]

/-- Fallback sequence for unhandled instructions: fault to mtvec with illegal
    instruction.  Control-store slot `routineCount`. -/
def illegalInsnRoutine : List FallbackEntry :=
  [drainE, fe .TRAP_ILLEGAL 0 0 0, doneE]

/-- The 43 emulated Zb* encodings, in routine order.

    Sample encodings are canonical single instructions (`rd = x1`, `rs1 = x2`,
    `rs2 = x3`, shift amount 0).  They are the encodings the equivalence proofs
    name, the generator's Zb* alphabet uses, and the benchmark specs emit. -/
def zbTable : List ZbRoutine := [
  -- Zba shifted adds
  ⟨"sh1add",    .binary, 0x203120B3, zbMaskFunct7, bodyBinary .ALU_SH1ADD⟩,
  ⟨"sh2add",    .binary, 0x203140B3, zbMaskFunct7, bodyBinary .ALU_SH2ADD⟩,
  ⟨"sh3add",    .binary, 0x203160B3, zbMaskFunct7, bodyBinary .ALU_SH3ADD⟩,
  -- Zbs register forms
  ⟨"bset",      .binary, 0x283110B3, zbMaskFunct7, bodyBinary .ALU_BSET⟩,
  ⟨"bclr",      .binary, 0x483110B3, zbMaskFunct7, bodyBinary .ALU_BCLR⟩,
  ⟨"bext",      .binary, 0x483150B3, zbMaskFunct7, bodyBinary .ALU_BEXT⟩,
  ⟨"binv",      .binary, 0x683110B3, zbMaskFunct7, bodyBinary .ALU_BINV⟩,
  -- Zbb logic with negate
  ⟨"andn",      .binary, 0x403170B3, zbMaskFunct7, bodyBinary .ALU_ANDN⟩,
  ⟨"orn",       .binary, 0x403160B3, zbMaskFunct7, bodyBinary .ALU_ORN⟩,
  ⟨"xnor",      .binary, 0x403140B3, zbMaskFunct7, bodyBinary .ALU_XNOR⟩,
  -- Zbb min/max
  ⟨"min",       .binary, 0x0A3140B3, zbMaskFunct7, bodyBinary .ALU_MIN⟩,
  ⟨"minu",      .binary, 0x0A3150B3, zbMaskFunct7, bodyBinary .ALU_MINU⟩,
  ⟨"max",       .binary, 0x0A3160B3, zbMaskFunct7, bodyBinary .ALU_MAX⟩,
  ⟨"maxu",      .binary, 0x0A3170B3, zbMaskFunct7, bodyBinary .ALU_MAXU⟩,
  -- Zbb rotates
  ⟨"rol",       .binary, 0x603110B3, zbMaskFunct7, bodyBinary .ALU_ROL⟩,
  ⟨"ror",       .binary, 0x603150B3, zbMaskFunct7, bodyBinary .ALU_ROR⟩,
  -- Zbc carry-less multiply
  ⟨"clmul",     .binary, 0x0A3110B3, zbMaskFunct7, bodyBinary .ALU_CLMUL⟩,
  ⟨"clmulh",    .binary, 0x0A3130B3, zbMaskFunct7, bodyBinary .ALU_CLMULH⟩,
  ⟨"clmulr",    .binary, 0x0A3120B3, zbMaskFunct7, bodyBinary .ALU_CLMULR⟩,
  -- Zbs immediate forms
  ⟨"bseti",     .shift,  0x28011093, zbMaskFunct6,  bodyShift .ALU_BSET⟩,
  ⟨"bclri",     .shift,  0x48011093, zbMaskFunct6,  bodyShift .ALU_BCLR⟩,
  ⟨"binvi",     .shift,  0x68011093, zbMaskFunct6,  bodyShift .ALU_BINV⟩,
  ⟨"bexti",     .shift,  0x48015093, zbMaskFunct6,  bodyShift .ALU_BEXT⟩,
  ⟨"rori",      .shift,  0x60015093, zbMaskFunct6,  bodyShift .ALU_ROR⟩,
  -- Zbb unary forms
  ⟨"clz",       .unary,  0x60011093, zbMaskFunct12, bodyUnary .ALU_CLZ⟩,
  ⟨"ctz",       .unary,  0x60111093, zbMaskFunct12, bodyUnary .ALU_CTZ⟩,
  ⟨"cpop",      .unary,  0x60211093, zbMaskFunct12, bodyUnary .ALU_CPOP⟩,
  ⟨"orc_b",     .unary,  0x28715093, zbMaskFunct12, bodyUnary .ALU_ORCB⟩,
  ⟨"rev8",      .unary,  0x6B815093, zbMaskFunct12, bodyUnary .ALU_REV8⟩,
  ⟨"sext_b",    .unary,  0x60411093, zbMaskFunct12, bodyShiftIn .ALU_SRA 56⟩,
  ⟨"sext_h",    .unary,  0x60511093, zbMaskFunct12, bodyShiftIn .ALU_SRA 48⟩,
  ⟨"zext_h",    .unary,  0x080140BB, zbMaskFunct12, bodyShiftIn .ALU_SRL 48⟩,
  -- RV64 word forms
  ⟨"clzw",      .unary,  0x6001109B, zbMaskFunct12, bodyClzw⟩,
  ⟨"ctzw",      .unary,  0x6011109B, zbMaskFunct12, bodyCtzw⟩,
  ⟨"cpopw",     .unary,  0x6021109B, zbMaskFunct12, bodyCpopw⟩,
  ⟨"rolw",      .binary, 0x603110BB, zbMaskFunct7,  bodyBinary .ALU_ROLW⟩,
  ⟨"rorw",      .binary, 0x603150BB, zbMaskFunct7,  bodyBinary .ALU_RORW⟩,
  ⟨"roriw",     .shift,  0x6001509B, zbMaskFunct7,  bodyShift .ALU_RORW⟩,
  -- Zba word forms
  ⟨"add_uw",    .binary, 0x083100BB, zbMaskFunct7,  bodyUw .ALU_ADD⟩,
  ⟨"sh1add_uw", .binary, 0x203120BB, zbMaskFunct7,  bodyUw .ALU_SH1ADD⟩,
  ⟨"sh2add_uw", .binary, 0x203140BB, zbMaskFunct7,  bodyUw .ALU_SH2ADD⟩,
  ⟨"sh3add_uw", .binary, 0x203160BB, zbMaskFunct7,  bodyUw .ALU_SH3ADD⟩,
  ⟨"slli_uw",   .shift,  0x0801109B, zbMaskFunct6,  bodySlliUw⟩
]

theorem zbTable_length : zbTable.length = routineCount := by native_decide

/-- Table entry for routine `r`. -/
def zbEntry (r : Fin routineCount) : ZbRoutine :=
  zbTable.get ⟨r.val, by rw [zbTable_length]; exact r.isLt⟩

/-- Mnemonic of routine `r`. -/
def zbRoutineName (r : Fin routineCount) : String := (zbEntry r).name

/-- Operand shape of routine `r`. -/
def zbRoutineShape (r : Fin routineCount) : ZbShape := (zbEntry r).shape

/-- Canonical sample encoding of routine `r`. -/
def zbRoutineSample (r : Fin routineCount) : UInt32 := (zbEntry r).sample

/-! ## 3. Control store -/

/-- Routine bodies by control-store slot: the 43 Zb* routines (slots 0..42)
    followed by the illegal-instruction routine (slot 43). -/
private def zbBodies : List (List FallbackEntry) :=
  zbTable.map (·.body) ++ [illegalInsnRoutine]

/-- Micro-ops of control-store slot `r`; empty past the last slot. -/
def zbRoutineBody (r : Nat) : List FallbackEntry := (zbBodies[r]?).getD []

/-- Number of micro-ops in control-store slot `r`. -/
def routineLength (r : Nat) : Nat := (zbRoutineBody r).length

/-- Control-store entry at micro-PC `i`.  `zbRomSize` is a power of two, so the
    micro-PC is 9 bits and the store is realized as a plain mux tree. -/
def zbRom (i : Nat) : FallbackEntry :=
  (zbRoutineBody (i / routineStride))[i % routineStride]?.getD doneE

/-! ## 4. Instruction dispatch -/

/-- Bit `b` of a 32-bit word, as a `Nat`.

    Written with `Nat` division rather than `&&&`/`testBit` so that the kernel
    can reduce a concrete decode: `routineIndex` has to collapse definitionally
    for the equivalence proofs to close by `rfl`, and `Nat.land` does not
    unfold at the transparency `rfl` uses. -/
def bitAt (x : UInt32) (b : Nat) : Nat := (x.toNat >>> b) % 2

/-- Does `insn` match entry `e`?  Every bit `e.mask` fixes must equal `e.sample`;
    the operand fields `e.mask` leaves free are ignored. -/
def zbHit (e : ZbRoutine) (insn : UInt32) : Bool :=
  (List.range 32).all fun b => bitAt e.mask b == 0 || bitAt insn b == bitAt e.sample b

/-- Routine index of a Zb* instruction word, or `none` when the encoding is not
    one of the 43 emulated ones.

    Every entry's `mask` fixes the bits that select it and leaves the operand
    fields free, so a single scan of `zbTable` is both the decoder and the
    definition of what "emulated" means. -/
def routineIndex (insn : UInt32) : Option (Fin routineCount) :=
  (List.finRange routineCount).find? fun r => zbHit (zbEntry r) insn

/-- Control-store slot an instruction executes: its routine index, or the
    illegal-instruction slot when the encoding is not emulated. -/
def routineSlot (insn : UInt32) : Nat :=
  match routineIndex insn with
  | some r => r.val
  | none => routineCount

/-- Micro-PC base of an instruction's routine. -/
def routineBase (insn : UInt32) : Nat := routineSlot insn * routineStride

/-- The micro-ops an instruction executes. -/
def routineOps (insn : UInt32) : List FallbackEntry :=
  match routineIndex insn with
  | some r => (zbEntry r).body
  | none => illegalInsnRoutine

/-- The 6-bit shift amount an immediate-form instruction carries at bits 25:20. -/
def insnShamt (insn : UInt32) : UInt64 := UInt64.ofNat ((insn.toNat >>> 20) % 64)

/-! ## 5. Behavioral Sequencer Model -/

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
    let nextUpc : Fin 512 := ⟨(s.upc.val + 1) % 512, by omega⟩
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

    | .LOAD_SHAMT =>
      writeTemp s' e.dst (insnShamt s.rawInsn)

    | .LOAD_INSN =>
      writeTemp s' e.dst (UInt64.ofNat s.rawInsn.toNat)

    | .LOAD_PC =>
      writeTemp s' e.dst s.pcVal

    | .MOV_TO_RD =>
      -- In hardware, this fires CDB inject with data = readTemp s e.src1
      s'

    | .ALU_ADD    => writeTemp s' e.dst (specAdd (readTemp s e.src1) (readTemp s e.src2))
    | .ALU_SUB    => writeTemp s' e.dst (specSub (readTemp s e.src1) (readTemp s e.src2))
    | .ALU_AND    => writeTemp s' e.dst (readTemp s e.src1 &&& readTemp s e.src2)
    | .ALU_OR     => writeTemp s' e.dst (readTemp s e.src1 ||| readTemp s e.src2)
    | .ALU_XOR    => writeTemp s' e.dst (readTemp s e.src1 ^^^ readTemp s e.src2)
    | .ALU_ANDN   => writeTemp s' e.dst (specAndn (readTemp s e.src1) (readTemp s e.src2))
    | .ALU_ORN    => writeTemp s' e.dst (specOrn (readTemp s e.src1) (readTemp s e.src2))
    | .ALU_XNOR   => writeTemp s' e.dst (specXnor (readTemp s e.src1) (readTemp s e.src2))
    | .ALU_SLL    => writeTemp s' e.dst (specSll (readTemp s e.src1) (readTemp s e.src2))
    | .ALU_SRL    => writeTemp s' e.dst (specSrl (readTemp s e.src1) (readTemp s e.src2))
    | .ALU_SRA    => writeTemp s' e.dst (specSra (readTemp s e.src1) (readTemp s e.src2))
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
    | .ALU_CLMULH => writeTemp s' e.dst (specClmulh (readTemp s e.src1) (readTemp s e.src2))
    | .ALU_CLMULR => writeTemp s' e.dst (specClmulr (readTemp s e.src1) (readTemp s e.src2))
    | .ALU_SH1ADD => writeTemp s' e.dst (specSh1add (readTemp s e.src1) (readTemp s e.src2))
    | .ALU_SH2ADD => writeTemp s' e.dst (specSh2add (readTemp s e.src1) (readTemp s e.src2))
    | .ALU_SH3ADD => writeTemp s' e.dst (specSh3add (readTemp s e.src1) (readTemp s e.src2))
    | .ALU_BSET   => writeTemp s' e.dst (specBset (readTemp s e.src1) (readTemp s e.src2))
    | .ALU_BCLR   => writeTemp s' e.dst (specBclr (readTemp s e.src1) (readTemp s e.src2))
    | .ALU_BINV   => writeTemp s' e.dst (specBinv (readTemp s e.src1) (readTemp s e.src2))
    | .ALU_BEXT   => writeTemp s' e.dst (specBext (readTemp s e.src1) (readTemp s e.src2))
    | .ALU_SEXT_W => writeTemp s' e.dst (specSextW (readTemp s e.src1))
    | .ALU_ZEXT_W => writeTemp s' e.dst (specZextW (readTemp s e.src1))
    | .ALU_ROLW   => writeTemp s' e.dst (specRolw (readTemp s e.src1) (readTemp s e.src2))
    | .ALU_RORW   => writeTemp s' e.dst (specRorw (readTemp s e.src1) (readTemp s e.src2))
    | .ALU_CTZW   => writeTemp s' e.dst (specCtzw (readTemp s e.src1))

    | .JMP =>
      { s with upc := ⟨e.imm.val % 512, by omega⟩ }

    | .JMP_ZERO =>
      if readTemp s e.src1 == 0 then
        { s with upc := ⟨e.imm.val % 512, by omega⟩ }
      else s'

    | .JMP_NZERO =>
      if readTemp s e.src1 != 0 then
        { s with upc := ⟨e.imm.val % 512, by omega⟩ }
      else s'

    | .JMP_EQ =>
      if readTemp s e.src1 == readTemp s e.src2 then
        { s with upc := ⟨e.imm.val % 512, by omega⟩ }
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
  runProgram init (routineOps insn)

end Shoumei.RISCV.Microcode
