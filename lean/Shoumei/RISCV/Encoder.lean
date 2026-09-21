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

/-- Mask `imm` to `w` bits, two's complement: -1 at w=12 gives 0xFFF.

    Lean's `%` on `Int` is Euclidean, so `imm % 2^w` is already non-negative and
    `toNat` is exact.  This is what makes negative immediates encode: the
    previous `UInt32.ofNat imm.toNat` turned every negative `imm` into 0. -/
def maskTwos (imm : Int) (w : Nat) : UInt32 :=
  UInt32.ofNat ((imm % (2 : Int) ^ w).toNat)

/-- Pack I-type immediate into bits [31:20] -/
def packImmI (imm : Int) : UInt32 :=
  maskTwos imm 12 <<< 20

/-- Pack S-type immediate: bits [31:25] | [11:7] -/
def packImmS (imm : Int) : UInt32 :=
  let bits := maskTwos imm 12
  let imm4_0 := bits &&& 0x1F
  let imm11_5 := (bits >>> 5) &&& 0x7F
  (imm11_5 <<< 25) ||| (imm4_0 <<< 7)

/-- Pack B-type immediate (must be even): scrambled to B-type layout -/
def packImmB (imm : Int) : UInt32 :=
  let bits := maskTwos imm 13
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
  let bits := maskTwos imm 21
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

/-! ## Field-driven encoding

One path covering every field signature in the instruction dictionary.  The six
`encodeR/I/S/B/U/J` helpers above cannot express R4-type, CSR, AMO or FENCE and
have no production callers; this one is what the random generator uses. -/

/-- Bit range of a variable field, inclusive.

    The scrambled S/B/J immediates return `(0, 0)`: they are not a contiguous
    slice and go through `packImmS`/`packImmB`/`packImmJ` instead. -/
def FieldType.bitRange : FieldType → Nat × Nat
  | .rd       => (11, 7)
  | .rs1      => (19, 15)
  | .rs2      => (24, 20)
  | .rs3      => (31, 27)
  | .rm       => (14, 12)
  | .csr      => (31, 20)
  | .zimm5    => (19, 15)
  | .shamtw   => (24, 20)
  | .shamtd   => (25, 20)
  | .fm       => (31, 28)
  | .pred     => (27, 24)
  | .succ     => (23, 20)
  | .aq       => (26, 26)
  | .rl       => (25, 25)
  | .imm12    => (31, 20)
  | .imm20    => (31, 12)
  | .imm12hi  => (0, 0)
  | .imm12lo  => (0, 0)
  | .bimm12hi => (0, 0)
  | .bimm12lo => (0, 0)
  | .jimm20   => (0, 0)

/-- The field a caller supplies the value for.  The split S and B immediates
    carry one value between them, so both halves read the same key: `.imm12`
    for stores and `.bimm12hi` for branches. -/
def FieldType.valueKey : FieldType → FieldType
  | .imm12hi | .imm12lo => .imm12
  | .bimm12hi | .bimm12lo => .bimm12hi
  | f => f

/-- `matchBits` OR every variable field of `d`, taking operands from `v`.

    `v` is queried with `FieldType.valueKey f`; `none` aborts the encoding.
    Register fields are masked to their width, so an out-of-range operand is
    truncated rather than corrupting its neighbours. -/
def encodeWithFields (d : InstructionDef) (v : FieldType → Option Int) : Option UInt32 := do
  let mut w := d.matchBits
  for f in d.variableFields do
    match f with
    | .imm12hi | .imm12lo => w := w ||| packImmS (← v .imm12)
    | .bimm12hi | .bimm12lo => w := w ||| packImmB (← v .bimm12hi)
    | .jimm20 => w := w ||| packImmJ (← v .jimm20)
    | f =>
      let r := f.bitRange
      w := w ||| (maskTwos (← v f) (r.1 - r.2 + 1) <<< UInt32.ofNat r.2)
  return w

end Shoumei.RISCV
