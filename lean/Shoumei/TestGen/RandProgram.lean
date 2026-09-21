/-
  TestGen/RandProgram.lean - Random straight-line payloads.

  A program is a prologue, `payloadWords` instructions and the pass epilogue.
  Every operand domain is chosen so the payload cannot leave the body:

    * loads and stores address `x31 + aligned offset` inside a fixed scratch
      buffer, so no access is misaligned and none reaches a peripheral;
    * branches compare a register with itself, so the outcome follows from the
      opcode alone (`beq`/`bge`/`bgeu` taken, the rest not) and the branch is a
      +4 fall-through either way;
    * `jal` is pinned to +4 and `jalr` is emitted as an `auipc`/`jalr` pair that
      targets the word after itself;
    * `ecall`, `ebreak`, `mret` and `wfi` are not in the alphabet at all.

  `checkWord` re-derives that invariant from each emitted encoding, so a
  generator bug stops the run instead of producing a program that wanders off.
-/

import Shoumei.TestGen.AsmEmitter
import Shoumei.TestGen.Rng
import Shoumei.TestGen.RandAlphabet
import Shoumei.RISCV.Encoder
import Shoumei.RISCV.Decoder

namespace Shoumei.TestGen

open Shoumei.RISCV

-- ════════════════════════════════════════════════════════════════════════════
-- Fixed operands
-- ════════════════════════════════════════════════════════════════════════════

/-- Scratch base register: set up by the prologue, never written by the payload. -/
def dataBaseReg : Fin 32 := ⟨31, by omega⟩

/-- Scratch base address.  Free RAM: `.tohost` is 0x1000, `_stack_top` 0x40000. -/
def dataBaseVal : UInt32 := 0x2000

/-- Scratch extent.  Keeps every offset inside a signed 12-bit field. -/
def scratchBytes : Nat := 2048

/-- Fall-through offset used wherever a transfer must not move the PC. -/
def branchFallThrough : Int := 4

/-- `auipc`/`jalr` pair offset: the word after the pair. -/
def jalrPairOffset : Int := 8

/-- Instructions per generated program. -/
def payloadWords : Nat := 64

/-- Programs per batch.  Program `i`'s dealt cover is every `batchSize`-th
    alphabet member, so the batch as a whole covers the alphabet. -/
def batchSize : Nat := 32

/-- CSR addresses the hardware decodes. -/
def csrWhitelist : List Nat :=
  [0x001, 0x002, 0x003, 0x300, 0x301, 0x304, 0x305, 0x340, 0x341, 0x342,
   0x343, 0x344, 0xB00, 0xB02, 0xB80, 0xB82, 0xC00, 0xC02, 0xC80, 0xC82, 0xF14]

/-- CSRs that may be written: the ones the generator is willing to perturb. -/
def csrWritable : List Nat := [0x340, 0x001, 0x002, 0x003]

/-- Branch opcodes. -/
def branchOpcodes : List OpType := [.BEQ, .BNE, .BLT, .BGE, .BLTU, .BGEU]

/-- Branches that are taken when both operands are equal. -/
def equalTakenOpcodes : List OpType := [.BEQ, .BGE, .BGEU]

/-- Atomics: `rs1` is the address and the AMO immediate field is reserved, so
    the generator must pin `rs1` to the scratch base like a plain access. -/
def atomicOpcodes : List OpType :=
  [.LR_W, .SC_W, .AMOADD_W, .AMOSWAP_W, .AMOXOR_W, .AMOAND_W, .AMOOR_W,
   .AMOMIN_W, .AMOMAX_W, .AMOMINU_W, .AMOMAXU_W,
   .LR_D, .SC_D, .AMOADD_D, .AMOSWAP_D, .AMOXOR_D, .AMOAND_D, .AMOOR_D,
   .AMOMIN_D, .AMOMAX_D, .AMOMINU_D, .AMOMAXU_D]

/-- Access size of a memory instruction, 0 when it does not touch memory. -/
def accessBytes : OpType → Nat
  | .LB | .LBU | .SB => 1
  | .LH | .LHU | .SH => 2
  | .LW | .LWU | .SW | .FLW | .FSW => 4
  | .LD | .SD | .FLD | .FSD => 8
  | _ => 0

-- ════════════════════════════════════════════════════════════════════════════
-- Register classes
-- ════════════════════════════════════════════════════════════════════════════

/-- Truncate a drawn register number into `Fin 32`. -/
def fin32 (v : Nat) : Fin 32 := ⟨v % 32, Nat.mod_lt v (by omega)⟩

/-- Integer destination: `x0..x30`.  `x31` holds the scratch base. -/
def pickIntRd : RandM (Fin 32) := do
  return fin32 (← RandM.pickNat 31)

/-- Any integer register.  `x0` is a legal read; `x31` is the scratch base. -/
def pickIntRs : RandM (Fin 32) := do
  return fin32 (← RandM.pickNat 32)

/-- Any FP register. -/
def pickFpReg : RandM (Fin 32) := do
  return fin32 (← RandM.pickNat 32)

/-- Base register of an `auipc`/`jalr` pair: neither `x0` (whose target would be
    8) nor `x31` (the scratch base). -/
def pickPairBase : RandM (Fin 32) := do
  return fin32 (← RandM.pick 1 30)

-- ════════════════════════════════════════════════════════════════════════════
-- Operand domains
-- ════════════════════════════════════════════════════════════════════════════

/-- One value per variable field of `d`, keyed by `FieldType.valueKey`. -/
def genFields (d : InstructionDef) : RandM (List (FieldType × Int)) := do
  let memBytes := accessBytes d.opType
  let isBranch := branchOpcodes.contains d.opType
  let taken := equalTakenOpcodes.contains d.opType
  let isCsr := d.variableFields.contains .csr
  -- A branch compares one register with itself, so its outcome is fixed by the
  -- opcode and the payload stays straight-line.
  let breg ← pickIntRs
  let aq ← RandM.pickBit
  let rl ← RandM.pickBit
  let pred ← RandM.pick 0 15
  let succ ← RandM.pick 0 15
  let csr ←
    if !isCsr then pure 0
    else if [.CSRRW, .CSRRWI].contains d.opType then RandM.pickFrom csrWritable
    else RandM.pickFrom csrWhitelist
  let mut acc : List (FieldType × Int) := []
  for f in (d.variableFields.map FieldType.valueKey).eraseDups do
    let v ←
      match f with
      | .rd =>
        if d.opType.hasFpRd then do
          let r ← pickFpReg
          pure (r.val : Int)
        else do
          let r ← pickIntRd
          pure (r.val : Int)
      | .rs1 =>
        if isBranch then pure (breg.val : Int)
        else if memBytes > 0 || atomicOpcodes.contains d.opType then
          pure (dataBaseReg.val : Int)
        else if d.opType.hasFpRs1 then do
          let r ← pickFpReg
          pure (r.val : Int)
        else do
          let r ← pickIntRs
          pure (r.val : Int)
      | .rs2 =>
        if isBranch then pure (breg.val : Int)
        else if memBytes > 0 then pure (dataBaseReg.val : Int)
        else if d.opType.hasFpRs2 then do
          let r ← pickFpReg
          pure (r.val : Int)
        else do
          let r ← pickIntRs
          pure (r.val : Int)
      | .rs3 => do
        let r ← pickFpReg
        pure (r.val : Int)
      | .rm => do
        let v ← RandM.pick 0 4
        pure (v : Int)
      | .csr => pure (csr : Int)
      | .zimm5 =>
        if [.CSRRSI, .CSRRCI].contains d.opType then pure 0
        else do
          let v ← RandM.pick 0 31
          pure (v : Int)
      | .shamtw => do
        let v ← RandM.pick 0 31
        pure (v : Int)
      | .shamtd => do
        let v ← RandM.pick 0 63
        pure (v : Int)
      | .imm12 =>
        if memBytes > 0 then do
          -- size-aligned offset inside the scratch buffer
          let k ← RandM.pickNat (scratchBytes / memBytes)
          pure ((k * memBytes : Nat) : Int)
        else if d.opType == .JALR then pure jalrPairOffset
        else do
          let v ← RandM.pick 0 4095
          pure ((v : Int) - 2048)
      | .imm20 => do
        let v ← RandM.pick 0 0xFFFFF
        pure (v : Int)
      | .jimm20 => pure branchFallThrough
      | .bimm12hi =>
        if taken then pure branchFallThrough
        else do
          let v ← RandM.pick 0 4095
          pure ((v : Int) * 2 - 4096)
      | .fm => pure 0
      | .pred => pure (pred : Int)
      | .succ => pure (succ : Int)
      | .aq => pure (aq : Int)
      | .rl => pure (rl : Int)
      -- the split S/B immediates carry one value, keyed by `valueKey`
      | .imm12hi | .imm12lo | .bimm12lo => pure 0
    acc := acc ++ [(f, v)]
  return acc

/-- Lookup for `encodeWithFields`. -/
def fieldLookup (fields : List (FieldType × Int)) : FieldType → Option Int :=
  fun f => (fields.find? (fun p => p.1 == f)).map (·.2)

-- ════════════════════════════════════════════════════════════════════════════
-- Instruction generation
-- ════════════════════════════════════════════════════════════════════════════

/-- One emitted word: the alphabet entry it came from, its encoding and the
    comment beside it. -/
abbrev Emitted := InstrClass × UInt32 × String

/-- Encode one alphabet entry: the word(s) plus the comment beside them. -/
def genInstr (defs : List InstructionDef) (cls : InstrClass) : RandM (List Emitted) :=
  match cls with
  | .zbRoutine r =>
    pure [(cls, Microcode.zbRoutineSample r,
           s!"{Microcode.zbRoutineName r} (Zb* routine {r.val})")]
  | .decoded d => do
    let fields ← genFields d
    if d.opType == .JALR then
      -- `auipc xT, 0` leaves the PC in xT, so `jalr xD, 8(xT)` targets the word
      -- after the pair and the pair falls through.
      let xt ← pickPairBase
      let xd ← pickIntRd
      let auDef := defs.find? (fun x => x.opType == .AUIPC)
      match auDef, encodeU defs .AUIPC xt 0, encodeI defs .JALR xd xt 8 with
      | some ad, some au, some jr =>
        pure [(.decoded ad, au, s!"auipc x{xt.val}, 0"),
              (cls, jr, s!"jalr x{xd.val}, 8(x{xt.val})")]
      | _, _, _ => pure []
    else
      match encodeWithFields d (fieldLookup fields) with
      | some w => pure [(cls, w, d.name)]
      | none => pure []

-- ════════════════════════════════════════════════════════════════════════════
-- Self-check
-- ════════════════════════════════════════════════════════════════════════════

/-- Check one emitted word against the straight-line invariant.

    `prev` is the word before it, needed to confirm the `auipc`/`jalr` pair
    targets the word after itself. -/
def checkWord (defs : List InstructionDef) (cls : InstrClass) (w : UInt32)
    (prev : Option UInt32) : Except String Unit :=
  match cls with
  | .zbRoutine r =>
    match Microcode.routineIndex w with
    | some r' =>
      if r' == r then .ok ()
      else .error s!"Zb* word 0x{hex8 w} dispatches to routine {r'.val}, expected {r.val}"
    | none => .error s!"Zb* word 0x{hex8 w} does not dispatch"
  | .decoded d =>
    match decodeInstruction defs w 0 with
    | none => .error s!"word 0x{hex8 w} does not decode"
    | some di =>
      if di.opType != d.opType then
        .error s!"word decodes to {di.opType}, expected {d.opType}"
      else if branchOpcodes.contains d.opType then
        -- equal operands: taken for BEQ/BGE/BGEU (offset +4 = fall-through),
        -- not taken for the rest (offset is then irrelevant)
        if di.rs1 != di.rs2 then .error s!"{d.name}: branch operands differ"
        else if takenEquals d.opType then
          if di.imm == some branchFallThrough then .ok ()
          else .error s!"{d.name}: taken branch offset {di.imm} is not +4"
        else .ok ()
      else if d.opType == .JAL then
        if di.imm == some branchFallThrough then .ok ()
        else .error s!"jal offset {di.imm} is not +4"
      else if d.opType == .JALR then
        match prev, di.imm, di.rs1 with
        | some p, some off, some rs1 =>
          match decodeInstruction defs p 0 with
          | some pd =>
            if pd.opType == .AUIPC && pd.rd == some rs1 && off == jalrPairOffset then .ok ()
            else .error s!"jalr is not paired with an auipc to the same register"
          | none => .error "jalr pair: previous word does not decode"
        | _, _, _ => .error "jalr is missing its immediate or base register"
      else .ok ()
where
  takenEquals (op : OpType) : Bool := equalTakenOpcodes.contains op

-- ════════════════════════════════════════════════════════════════════════════
-- Program assembly
-- ════════════════════════════════════════════════════════════════════════════

/-- `x31 = scratch base`, then every FP register cleared.

    The FP clear matters for the oracle: Spike NaN-boxes `f64` reads, so an
    unwritten FP register reads as qNaN there and as +0.0 in the RTL.  A payload
    that reads one would diverge for reasons that have nothing to do with the
    instruction under test. -/
def randProgramPrologue (defs : List InstructionDef) : List AsmInstr :=
  [ .comment "x31 = scratch base; never written by the payload"
  , .utype "lui" dataBaseReg dataBaseVal ]
  ++ (List.range 32).filterMap fun i =>
      (encodeR defs .FMV_D_X (fin32 i) ⟨0, by omega⟩ ⟨0, by omega⟩).map
        (fun w => .word w s!"fmv.d.x f{i}, x0")

/-- One program body: the dealt cover first (so the batch covers the alphabet),
    then uniform draws up to `length` instructions. -/
def buildProgram (defs : List InstructionDef) (alphabet dealt : List InstrClass)
    (length : Nat) : RandM (List Emitted) := do
  let cover ← RandM.shuffle dealt
  let mut body : List Emitted := []
  for cls in cover do
    body := body ++ (← genInstr defs cls)
  let extra := if length > cover.length then length - cover.length else 0
  for _ in List.range extra do
    let cls ← RandM.pickFrom alphabet
    body := body ++ (← genInstr defs cls)
  return body

/-- The dealt cover of program `i` in a batch of `batchSize`. -/
def dealtCover (alphabet : List InstrClass) (i : Nat) : List InstrClass :=
  (alphabet.enum.filter (fun p => p.1 % batchSize == i)).map (·.2)

/-- A complete `.S` file for a random program. -/
def randProgramAsm (defs : List InstructionDef) (name : String) (seed length count : Nat)
    (dictPath : String) (body : List Emitted) : String :=
  let lines :=
    [ s!"# Auto-generated random test: {name}"
    , s!"# seed={seed}"
    , s!"# length={length} count={count} dict={dictPath}"
    , ".section .text"
    , ".globl _start"
    , "_start:"
    , ".globl main"
    , "main:" ]
    ++ (randProgramPrologue defs ++ body.map (fun e => AsmInstr.word e.2.1 e.2.2)
        ++ passEpilogue).map AsmInstr.toAsm
  String.intercalate "\n" lines ++ "\n"

/-- Seeds promoted from a run that found a defect: regenerated alongside the
    entropy batch so a failing program can be replayed byte for byte. -/
def replaySeeds : List Nat := []

end Shoumei.TestGen
