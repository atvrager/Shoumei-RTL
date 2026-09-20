/-
  BenchmarkSpecs.lean - software-driven instruction benchmark suite

  The benchmark set is derived from the decoder's instruction table (the
  riscv-opcodes instr_dict.json the CPU decoder is built from), never handwritten.
  For every instruction one self-contained .S program is emitted that measures
  cycles-per-instruction over a region bracketed by mcycle/minstret reads:

      CPI = delta(mcycle) / delta(minstret)   (scaled by 1000, "cpi_milli")

  Two region shapes exist:
    - throughput: BENCH_NTHR independent copies per loop iteration, destinations
      rotating through a 16-register window so no copy depends on its neighbour;
    - latency:    BENCH_NLAT dependent copies forming a true dependency chain
      (dest register feeds the next copy's source/address). Only emitted when
      the instruction format permits a same-class rd -> rs1 chain (see
      `latencyEligible`).

  Mintret is validated against the exact expected retired count per region, so a
  minstret accounting bug fails the benchmark (tohost = 0xDEAD) instead of
  silently skewing every CPI number.

  Loop sizing lives in the BENCH_* constants below; tune here only.
-/

import Shoumei.RISCV.ISA
import Shoumei.RISCV.OpcodeParser
import Shoumei.RISCV.Decoder
import Shoumei.RISCV.Encoder
import Shoumei.RISCV.Config
import Lean.Data.Json
import Lean.Elab.Command

namespace Shoumei.RISCV

open Lean
open Lean.Elab.Command

-- ════════════════════════════════════════════════════════════════════════════
-- Loop sizing / register allocation (single source of truth; tune here only)
-- ════════════════════════════════════════════════════════════════════════════

def BENCH_NTHR : Nat := 64      -- throughput copies per loop iteration
def BENCH_NLAT : Nat := 8       -- latency chain copies per loop iteration
def BENCH_ITERS : Nat := 256    -- loop iterations per measured region
def BENCH_CHAIN_X : Nat := 5    -- integer chain register: x5
def BENCH_CHAIN_F : Nat := 6    -- FP chain register: f6
def BENCH_CONST_X : Nat := 12   -- integer constant register: x12 (preloaded 8)
def BENCH_CONST_F : Nat := 7    -- FP constant register: f7 (preloaded 1.0)
def BENCH_CONST_F2 : Nat := 8   -- FP constant register: f8 (preloaded 2.0)
def BENCH_BASE : Nat := 28      -- x28 = scratch buffer base
def BENCH_COUNT : Nat := 29     -- x29 = loop counter
def BENCH_SCRATCH : Nat := 8192 -- scratch buffer bytes (data + rodata section)
def BENCH_SLOTS : Nat := 16     -- distinct 8-byte slot offsets ((copy%16)*8 < 2048)
def BENCH_CSR : Nat := 0x340    -- mscratch: writable, no side effects
def BENCH_MMIO : Nat := 0x1004  -- putchar MMIO address (matches cpuTestbenchConfig)
def BENCH_TOHOST : Nat := 0x1000

/-- Control/trap/privileged instructions never benchmarked.
    fence.i is excluded because the serialized drain does not increment
    minstret, so a minstret-derived CPI is meaningless for it.  (Its
    slot-0 predecessor drop is fixed -- see
    testbench/tests/serialize_pair_test.S and
    testbench/fence_i_regression/README.md.) -/
def BENCH_SKIP : List String := ["ecall", "ebreak", "mret", "wfi", "sret", "uret", "sfence.vma", "fence_i"]

-- ════════════════════════════════════════════════════════════════════════════
-- Spec model
-- ════════════════════════════════════════════════════════════════════════════

inductive BenchKind where
  | throughputOnly
  | latencyAndThroughput
deriving Repr, BEq, DecidableEq, Inhabited

def BenchKind.toString : BenchKind → String
  | .throughputOnly => "throughput"
  | .latencyAndThroughput => "latency"

structure BenchmarkSpec where
  name : String
  opType : Option OpType := none
  kind : BenchKind
  sample : UInt32
  needsFpMarch : Bool := false
  needsAmoMarch : Bool := false
  needsZbMarch : Bool := false
deriving Repr

/--
  Can this instruction be measured as a dependency chain?

  Requires rd and rs1 in the variable fields with the destination in the same
  register class as the source (FP iff the op writes/reads FP, else INT).
  Chains: rd -> rs1 of the next copy, e.g. `add x5, x5, x12`, `ld x5, 0(x5)`,
  `amoadd.w x5, x12, 0(x5)`, `csrrw x5, mscratch, x5`, `fadd.s f6, f6, f7`.
-/
def latencyEligible (d : InstructionDef) : Bool :=
  let hasRd := d.variableFields.contains .rd
  let hasRs1 := d.variableFields.contains .rs1
  let sameClass := d.opType.hasFpRd == d.opType.hasFpRs1
  -- Control flow, atomic ops (rs1 is address), CSRs, and fences never chain; always throughput-only.
  let noChain : List String := ["jal", "jalr", "beq", "bne", "blt", "bge", "bltu", "bgeu", "sc_d", "sc_w", "fence", "fence_i"]
  let isAmoOrLr := d.name.startsWith "amo" || d.name.startsWith "lr"
  hasRd && hasRs1 && sameClass && !noChain.contains d.name && !isAmoOrLr

/-- Instructions whose extension list contains no `rv_system`, deduped by
    (maskBits, matchBits) keeping the first occurrence (matches the CPU
    decoder table minus system instructions). -/
def since (defs : List InstructionDef) : List InstructionDef :=
  defs.filter (fun d => !d.extension.contains "rv_system") |>.foldl (fun acc d =>
    if acc.any (fun e => e.maskBits == d.maskBits && e.matchBits == d.matchBits) then
      acc
    else
      acc ++ [d]) []

/-- FP-group def (sorted after the integer block, exactly like the decoder's
    `sortIMFirst`). -/
def isFpDef (d : InstructionDef) : Bool :=
  d.extension.any (fun e => e == "rv_f" || e == "rv_d" || e == "rv64_f" || e == "rv64_d")

/-- Integer block first (in-place order), then the FP block; the same grouping
    the RV64GDecoder enum uses. -/
def sortIMFirstLike (defs : List InstructionDef) : List InstructionDef :=
  defs.filter (fun d => !isFpDef d) ++ defs.filter isFpDef

/-- Pack a register number into bits [27:23] (rs3 field of R4-type ops). -/
def packRs3 (reg : Fin 32) : UInt32 :=
  (UInt32.ofNat reg.val) <<< 27

/--
  Build a representative 32-bit encoding for the instruction: match bits with
  every variable field packed to a fixed, non-zero value. The opType of the
  decoded sample must equal the definition's opType (validated in `emitAll`).
-/
def sampleEncoding (d : InstructionDef) : UInt32 :=
  let f := d.variableFields
  let s0 := d.matchBits
  let withRd := if f.contains .rd then s0 ||| packRd ⟨10, by omega⟩ else s0
  let withRs1 := if f.contains .rs1 then withRd ||| packRs1 ⟨11, by omega⟩ else withRd
  let withRs2 := if f.contains .rs2 then withRs1 ||| packRs2 ⟨12, by omega⟩ else withRs1
  let withRs3 := if f.contains .rs3 then withRs2 ||| packRs3 ⟨13, by omega⟩ else withRs2
  -- imm12 / loads / fence.i / fm field sits in bits 31:20
  let withImm :=
    if f.contains .imm12 then withRs3 ||| packImmI 1
    else if f.contains .imm12hi || f.contains .imm12lo then withRs3 ||| packImmS 8
    else if f.contains .bimm12hi || f.contains .bimm12lo then withRs3 ||| packImmB 8
    else if f.contains .jimm20 then withRs3 ||| packImmJ 0
    else if f.contains .imm20 then withRs3 ||| (0x00012000 : UInt32)
    else withRs3
  let withShift :=
    if f.contains .shamtw || f.contains .shamtd then withImm ||| ((2 : UInt32) <<< 20) else withImm
  let withFence :=
    (if f.contains .succ then withShift ||| ((0xF : UInt32) <<< 20) else withShift) |||
    (if f.contains .pred then ((0xF : UInt32) <<< 24) else 0)
  let withCsr :=
    if f.contains .csr then withFence ||| (UInt32.ofNat BENCH_CSR <<< 20) else withFence
  let withZimm :=
    if f.contains .zimm5 then withCsr ||| ((5 : UInt32) <<< 15) else withCsr
  -- .rm → 0, .fm → 0, .aq/.rl → 0 (hints only)
  withZimm

/-- Classify a decoder definition into a benchmark spec (none for skipped
    control/trap instructions). -/
def classify (d : InstructionDef) : Option BenchmarkSpec :=
  if BENCH_SKIP.contains d.name then
    none
  else
    let kind := if latencyEligible d then .latencyAndThroughput else .throughputOnly
    some {
      name := d.name
      opType := some d.opType
      kind := kind
      sample := sampleEncoding d
      needsFpMarch := d.opType.isFpGroup
      needsAmoMarch := d.extension.any (fun e => e == "rv_a" || e == "rv64_a")
      needsZbMarch := false
    }

/-- Dummy InstructionDef for microcode fallback Zb* instructions (3-register integer ALU). -/
def zbInstructionDef (name : String) (sample : UInt32) : InstructionDef := {
  name := name
  opType := .ADD
  encoding := ""
  variableFields := [.rd, .rs1, .rs2]
  extension := ["rv_zba"]
  matchBits := sample
  maskBits := 0xfe00707f
}

/-- Benchmark specs for the 17 un-decoded Zb* bitmanip fallback instructions. -/
def zbSpecs : List BenchmarkSpec := [
  { name := "sh1add", opType := none, kind := .throughputOnly, sample := 0x20002033, needsZbMarch := true },
  { name := "sh2add", opType := none, kind := .throughputOnly, sample := 0x20004033, needsZbMarch := true },
  { name := "sh3add", opType := none, kind := .throughputOnly, sample := 0x20006033, needsZbMarch := true },
  { name := "bset",   opType := none, kind := .throughputOnly, sample := 0x28001033, needsZbMarch := true },
  { name := "bclr",   opType := none, kind := .throughputOnly, sample := 0x48001033, needsZbMarch := true },
  { name := "binv",   opType := none, kind := .throughputOnly, sample := 0x68001033, needsZbMarch := true },
  { name := "bext",   opType := none, kind := .throughputOnly, sample := 0x48005033, needsZbMarch := true },
  { name := "andn",   opType := none, kind := .throughputOnly, sample := 0x40007033, needsZbMarch := true },
  { name := "orn",    opType := none, kind := .throughputOnly, sample := 0x40006033, needsZbMarch := true },
  { name := "xnor",   opType := none, kind := .throughputOnly, sample := 0x40004033, needsZbMarch := true },
  { name := "min",    opType := none, kind := .throughputOnly, sample := 0x0a004033, needsZbMarch := true },
  { name := "max",    opType := none, kind := .throughputOnly, sample := 0x0a006033, needsZbMarch := true },
  { name := "minu",   opType := none, kind := .throughputOnly, sample := 0x0a005033, needsZbMarch := true },
  { name := "maxu",   opType := none, kind := .throughputOnly, sample := 0x0a007033, needsZbMarch := true },
  { name := "rol",    opType := none, kind := .throughputOnly, sample := 0x60001033, needsZbMarch := true },
  { name := "ror",    opType := none, kind := .throughputOnly, sample := 0x60005033, needsZbMarch := true },
  { name := "clmul",  opType := none, kind := .throughputOnly, sample := 0x0a001033, needsZbMarch := true }
]

/-- All benchmark specs for a config: `since` → sortIMFirst → classify ++ zbSpecs. -/
def computeSpecs (defs : List InstructionDef) : List BenchmarkSpec :=
  (sortIMFirstLike (since defs)).filterMap classify ++ zbSpecs

-- ════════════════════════════════════════════════════════════════════════════
-- Assembly emission
-- ════════════════════════════════════════════════════════════════════════════

def rn (n : Nat) : String := s!"x{n}"
def frn (n : Nat) : String := s!"f{n}"

/-- GAS mnemonic: instr_dict names use underscores (`fadd_d`), gas wants
    dots (`fadd.d`). -/
def mnemonicOf (name : String) : String :=
  name.replace "_" "."

/-- Per-loop-iteration instruction count of the throughput region. -/
def thrPerIter (spec : BenchmarkSpec) : Nat :=
  if spec.name.startsWith "csr" then 2
  else if spec.name == "jal" then 66
  -- `la` is auipc+addi (linker relaxation disabled: -Wl,--no-relax), so a
  -- jalr copy costs 3 instructions: 64*3 + addi + j.
  else if spec.name == "jalr" then 194
  else if spec.name ∈ ["beq", "bne", "blt", "bge", "bltu", "bgeu"] then 66
  else BENCH_NTHR + 2

/-- Per-loop-iteration instruction count of the latency (chain) region.
    Branches get a taken-branch throughput loop here instead of a chain. -/
def latPerIter (spec : BenchmarkSpec) : Nat :=
  if spec.name.startsWith "csr" then 2
  else if spec.name ∈ ["beq", "bne", "blt", "bge", "bltu", "bgeu"] then 3
  else BENCH_NLAT + 2

/-- Scratch memory slots: distinct 8-byte offsets in the scratch buffer. -/
def slotOff (k : Nat) : Nat := (k % BENCH_SLOTS) * 8

def isLoad (d : InstructionDef) : Bool :=
  d.name ∈ ["lb", "lbu", "lh", "lhu", "lw", "lwu", "ld"]

def isFpLoad (d : InstructionDef) : Bool :=
  d.name ∈ ["flw", "fld"]

/-- Instructions whose latency chain walks memory through x5 (loads, LR, AMO):
    keep the address alive by self-initialising `sd x5, 0(x5)`. -/
def isMemChain (d : InstructionDef) : Bool :=
  isLoad d || d.name.startsWith "lr" || d.name.startsWith "amo"

def isBranch (d : InstructionDef) : Bool :=
  d.name ∈ ["beq", "bne", "blt", "bge", "bltu", "bgeu"]

def isDiv (d : InstructionDef) : Bool :=
  d.opType == .FDIV_S || d.opType == .FDIV_D

/-- Divide chains use f8 (2.0) as the second operand so the value converges;
    everything else keeps f7 (1.0). -/
def fpConst2 (d : InstructionDef) : String :=
  if isDiv d then frn BENCH_CONST_F2 else frn BENCH_CONST_F

/-- Throughput destination window (integer): 16 registers that never collide
    with the reserved set (x5 chain, x12 const, x24..x31 IO/timing). -/
def INT_THR_REGS : List Nat :=
  [6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

/-- Throughput destination window (FP): 16 registers that never collide with
    the reserved set (f6 chain, f7/f8 constants). -/
def FP_THR_REGS : List Nat :=
  [0, 1, 2, 3, 4, 5, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]

/-- The destination register of throughput copy k (rotating window). -/
def thrDestR (k : Nat) : String := rn (List.getD INT_THR_REGS (k % BENCH_SLOTS) 6)
def thrDestF (k : Nat) : String := frn (List.getD FP_THR_REGS (k % BENCH_SLOTS) 0)

/-- One throughput copy line for instruction `d` (copy index k). -/
def thrCopy (d : InstructionDef) (k : Nat) : String :=
  let m := mnemonicOf d.name
  let f := d.variableFields
  if f.contains .rs3 then
    -- R4 fp fused ops: fd, fs1, fs2, fs3
    s!"  {m} {thrDestF k}, {frn BENCH_CONST_F}, {frn BENCH_CONST_F}, {frn BENCH_CONST_F2}"
  else if f.contains .rs2 && f.contains .aq then
    -- AMO / SC: rd, rs2, (rs1). The AMO immediate field is reserved (must be
    -- 0; gas rejects nonzero), so all copies share the scratch base.
    s!"  {m} {thrDestR k}, {rn BENCH_CONST_X}, 0({rn BENCH_BASE})"
  else if f.contains .rs2 && f.contains .rm then
    -- FP r2 ops (without rs3): fd, fs1, fs2
    s!"  {m} {thrDestF k}, {frn BENCH_CONST_F}, {fpConst2 d}"
  else if f.contains .imm12hi || f.contains .imm12lo then
    -- stores (sb/sh/sw/sd/fsd/fsw): rs2, imm(rs1); FSW/FSD carry the value
    -- in an FP register (hasFpRs2 excludes them; hasFpRs1 covers both)
    if d.opType.hasFpRs1 then
      s!"  {m} {frn BENCH_CONST_F}, {slotOff k}({rn BENCH_BASE})"
    else
      s!"  {m} {rn BENCH_CONST_X}, {slotOff k}({rn BENCH_BASE})"
  else if f.contains .rs2 then
    -- integer R-type / feq/flt/fle/fmin/fmax/fsgnj (rd, rs1, rs2);
    -- feq/flt/fle write an int rd but read FP sources
    if d.opType.hasFpRd then
      s!"  {m} {thrDestF k}, {frn BENCH_CONST_F}, {fpConst2 d}"
    else if d.opType.hasFpRs1 then
      s!"  {m} {thrDestR k}, {frn BENCH_CONST_F}, {frn BENCH_CONST_F}"
    else
      s!"  {m} {thrDestR k}, {rn BENCH_CONST_X}, {rn BENCH_CONST_X}"
  else if f.contains .csr && f.contains .zimm5 then
    -- CSRRWI / CSRRSI / CSRRCI
    s!"  {m} {thrDestR k}, mscratch, 5"
  else if f.contains .csr then
    -- CSRRW / CSRRS / CSRRC
    s!"  {m} {thrDestR k}, mscratch, {rn BENCH_CONST_X}"
  else if isLoad d then
    -- integer loads
    s!"  {m} {thrDestR k}, {slotOff k}({rn BENCH_BASE})"
  else if isFpLoad d then
    s!"  {m} {thrDestF k}, {slotOff k}({rn BENCH_BASE})"
  else if d.name.startsWith "lr" then
    s!"  {m} {thrDestR k}, ({rn BENCH_BASE})"
  else if d.name == "fence" then
    "  fence iorw, iorw"
  else if f.contains .imm12 then
    -- ALU immediate (addi/andi/...): rs1 = const, imm = 1
    s!"  {m} {thrDestR k}, {rn BENCH_CONST_X}, 1"
  else if f.contains .shamtw || f.contains .shamtd then
    -- shifts
    s!"  {m} {thrDestR k}, {rn BENCH_CONST_X}, 2"
  else if f.contains .imm20 then
    -- LUI / AUIPC
    s!"  {m} {thrDestR k}, 0x12"
  else if f.contains .rm then
    -- FP unary / converts (fsqrt, fcvt*): fd, fs1.
    -- Source class follows the op: int→fp converts read x12, everything
    -- else reads the f7 constant.
    if d.opType.hasFpRd then
      if d.opType.hasFpRs1 then
        s!"  {m} {thrDestF k}, {frn BENCH_CONST_F}"
      else
        s!"  {m} {thrDestF k}, {rn BENCH_CONST_X}"
    else
      s!"  {m} {thrDestR k}, {frn BENCH_CONST_F}"
  else if f.contains .rs1 then
    -- fclass / fmv (rd, rs1 only, no rm): dest class decides the operand
    if d.opType.hasFpRd then
      s!"  {m} {thrDestF k}, {rn BENCH_CONST_X}"
    else
      s!"  {m} {thrDestR k}, {frn BENCH_CONST_F}"
  else
    "  " ++ m

/-- One latency chain copy line for instruction `d` (index unused: chains are
    identical copies). -/
def latCopy (d : InstructionDef) (_k : Nat) : String :=
  let m := mnemonicOf d.name
  if d.opType.hasFpRd then
    -- FP chains: f6 feeds the next copy's fs1 (R2/R4/sqrt/convert)
    if d.variableFields.contains .rs3 then
      s!"  {m} {frn BENCH_CHAIN_F}, {frn BENCH_CHAIN_F}, {frn BENCH_CONST_F}, {frn BENCH_CONST_F2}"
    else if d.variableFields.contains .rs2 then
      s!"  {m} {frn BENCH_CHAIN_F}, {frn BENCH_CHAIN_F}, {fpConst2 d}"
    else
      s!"  {m} {frn BENCH_CHAIN_F}, {frn BENCH_CHAIN_F}"
  else
    -- Integer chains: x5 feeds the next copy's rs1/address.
    if isLoad d then
      s!"  {m} {rn BENCH_CHAIN_X}, 0({rn BENCH_CHAIN_X})"
    else if d.name.startsWith "lr" then
      s!"  {m} {rn BENCH_CHAIN_X}, ({rn BENCH_CHAIN_X})"
    else if d.name.startsWith "amo" then
      s!"  {m} {rn BENCH_CHAIN_X}, {rn BENCH_CONST_X}, 0({rn BENCH_CHAIN_X})"
    else if d.variableFields.contains .csr then
      s!"  {m} {rn BENCH_CHAIN_X}, mscratch, {rn BENCH_CHAIN_X}"
    else if d.variableFields.contains .shamtw || d.variableFields.contains .shamtd then
      s!"  {m} {rn BENCH_CHAIN_X}, {rn BENCH_CHAIN_X}, 2"
    else if d.variableFields.contains .imm12 then
      s!"  {m} {rn BENCH_CHAIN_X}, {rn BENCH_CHAIN_X}, 1"
    else
      s!"  {m} {rn BENCH_CHAIN_X}, {rn BENCH_CHAIN_X}, {rn BENCH_CONST_X}"

/-- Throughput region body: the `copies` per-iteration instructions. -/
def thrBody (d : InstructionDef) : List String :=
  if d.name == "jal" then
    (List.range BENCH_NTHR).flatMap fun k =>
      [s!"  jal x1, .Lskip_{k}", s!".Lskip_{k}:"]
  else if d.name == "jalr" then
    (List.range BENCH_NTHR).flatMap fun k =>
      [s!"  la x13, .Ljalr_{k + 1}", s!"  jalr x1, 0(x13)", s!".Ljalr_{k + 1}:"]
  else if isBranch d then
    let notTakenBranch := match d.name with
      | "beq"  => "  beq x8, x9, .Lfail"
      | "bne"  => "  bne x8, x8, .Lfail"
      | "blt"  => "  blt x9, x8, .Lfail"
      | "bge"  => "  bge x8, x9, .Lfail"
      | "bltu" => "  bltu x9, x8, .Lfail"
      | "bgeu" => "  bgeu x8, x9, .Lfail"
      | _ => s!"  {mnemonicOf d.name} x8, x9, .Lfail"
    (List.range BENCH_NTHR).map fun _ => notTakenBranch
  else
    (List.range BENCH_NTHR).map (thrCopy d)

/-- Latency region body: the `copies` per-iteration chain instructions.
    Branches measure a taken-branch loop instead. -/
def latBody (d : InstructionDef) : List String :=
  if isBranch d then
    let takenBranch := match d.name with
      | "beq"  => "  beq x8, x8, .Ltake"
      | "bne"  => "  bne x8, x9, .Ltake"
      | "blt"  => "  blt x8, x9, .Ltake"
      | "bge"  => "  bge x9, x8, .Ltake"
      | "bltu" => "  bltu x8, x9, .Ltake"
      | "bgeu" => "  bgeu x9, x8, .Ltake"
      | _ => s!"  {mnemonicOf d.name} x8, x8, .Ltake"
    [takenBranch, ".Ltake:"]
  else
    (List.range BENCH_NLAT).map (latCopy d)

/-- Loop tail for a region: counter decrement + branch back. -/
def loopTail (_d : InstructionDef) (lat : Bool) : List String :=
  let top := if lat then ".Ltop_lat" else ".Ltop_thr"
  ["  addi x29, x29, -1", s!"  bne x29, x0, {top}"]
/-- One measured region (throughput or chain), bracketed by csrr reads. -/
def regionAsm (d : InstructionDef) (lat : Bool) : String :=
  let top := if lat then ".Ltop_lat" else ".Ltop_thr"
  let body := if lat then latBody d else thrBody d
  let tail := loopTail d lat
  let l1 := String.intercalate "\n" body
  let l2 := String.intercalate "\n" tail
  "  csrr x26, mcycle\n" ++
  "  csrr x27, minstret\n" ++
  s!"{top}:\n" ++
  (if l1.isEmpty then "" else l1 ++ "\n") ++
  l2 ++ "\n" ++
  "  csrr x24, mcycle\n" ++
  "  csrr x25, minstret"

/-- Compute cpi_milli for the region just measured (x24=Δcycle, x25=Δretired,
    checked against the exact retired count) and stash it in x6 (throughput) or
    x7 (latency). -/
def regionCheck (spec : BenchmarkSpec) (lat : Bool) : String :=
  let perIter := if lat then latPerIter spec else thrPerIter spec
  let expected := BENCH_ITERS * perIter
  let dst := if lat then "x7" else "x6"
  "  # validate minstret delta == expected, then compute cpi_milli\n" ++
  "  sub x24, x24, x26\n" ++
  "  sub x25, x25, x27\n" ++
  s!"  li x30, {expected}\n" ++
  "  bne x25, x30, .Lfail\n" ++
  "  li x30, 1000\n" ++
  "  mul x24, x24, x30\n" ++
  "  divu x24, x24, x25\n" ++
  s!"  mv {dst}, x24\n"

/-- Shared putstr / putdec routines (MMIO 0x1004, preserve x5..x31). -/
def ioRoutines : String :=
  "putstr:\n" ++
  "  li x31, 0x1004\n" ++
  "1:\n" ++
  "  lbu x11, 0(x10)\n" ++
  "  beqz x11, 2f\n" ++
  "  sb x11, 0(x31)\n" ++
  "  addi x10, x10, 1\n" ++
  "  j 1b\n" ++
  "2:\n" ++
  "  jalr x0, 0(x1)\n\n" ++
  "putdec:\n" ++
  "  addi sp, sp, -216\n" ++
  "  sd x5, 0(sp)\n" ++
  "  sd x6, 8(sp)\n" ++
  "  sd x7, 16(sp)\n" ++
  "  sd x8, 24(sp)\n" ++
  "  sd x9, 32(sp)\n" ++
  "  sd x10, 40(sp)\n" ++
  "  sd x11, 48(sp)\n" ++
  "  sd x12, 56(sp)\n" ++
  "  sd x13, 64(sp)\n" ++
  "  sd x14, 72(sp)\n" ++
  "  sd x15, 80(sp)\n" ++
  "  sd x16, 88(sp)\n" ++
  "  sd x17, 96(sp)\n" ++
  "  sd x18, 104(sp)\n" ++
  "  sd x19, 112(sp)\n" ++
  "  sd x20, 120(sp)\n" ++
  "  sd x21, 128(sp)\n" ++
  "  sd x22, 136(sp)\n" ++
  "  sd x23, 144(sp)\n" ++
  "  sd x24, 152(sp)\n" ++
  "  sd x25, 160(sp)\n" ++
  "  sd x26, 168(sp)\n" ++
  "  sd x27, 176(sp)\n" ++
  "  sd x28, 184(sp)\n" ++
  "  sd x29, 192(sp)\n" ++
  "  sd x30, 200(sp)\n" ++
  "  sd x31, 208(sp)\n" ++
  "  li x31, 0x1004\n" ++
  "  li x17, 0\n" ++
  "1:\n" ++
  "  li x15, 10\n" ++
  "  divu x16, x14, x15\n" ++
  "  remu x15, x14, x15\n" ++
  "  addi x15, x15, 48\n" ++
  "  addi sp, sp, -8\n" ++
  "  sd x15, 0(sp)\n" ++
  "  addi x17, x17, 1\n" ++
  "  mv x14, x16\n" ++
  "  bne x14, x0, 1b\n" ++
  "2:\n" ++
  "  ld x15, 0(sp)\n" ++
  "  addi sp, sp, 8\n" ++
  "  sb x15, 0(x31)\n" ++
  "  addi x17, x17, -1\n" ++
  "  bnez x17, 2b\n" ++
  "  addi sp, sp, 216\n" ++
  "  ld x5, -216(sp)\n" ++
  "  ld x6, -208(sp)\n" ++
  "  ld x7, -200(sp)\n" ++
  "  ld x8, -192(sp)\n" ++
  "  ld x9, -184(sp)\n" ++
  "  ld x10, -176(sp)\n" ++
  "  ld x11, -168(sp)\n" ++
  "  ld x12, -160(sp)\n" ++
  "  ld x13, -152(sp)\n" ++
  "  ld x14, -144(sp)\n" ++
  "  ld x15, -136(sp)\n" ++
  "  ld x16, -128(sp)\n" ++
  "  ld x17, -120(sp)\n" ++
  "  ld x18, -112(sp)\n" ++
  "  ld x19, -104(sp)\n" ++
  "  ld x20, -96(sp)\n" ++
  "  ld x21, -88(sp)\n" ++
  "  ld x22, -80(sp)\n" ++
  "  ld x23, -72(sp)\n" ++
  "  ld x24, -64(sp)\n" ++
  "  ld x25, -56(sp)\n" ++
  "  ld x26, -48(sp)\n" ++
  "  ld x27, -40(sp)\n" ++
  "  ld x28, -32(sp)\n" ++
  "  ld x29, -24(sp)\n" ++
  "  ld x30, -16(sp)\n" ++
  "  ld x31, -8(sp)\n" ++
  "  jalr x0, 0(x1)\n"

/-- Print `BENCH <name> <thr_milli> <lat_milli>` through the MMIO putchar.
    `hasLatRegion` selects the x7 latency value; branches measure a taken loop
    there even though their kind stays throughput-only. -/
def printLine (hasLatRegion : Bool) : String :=
  "  li x31, 0x1004\n" ++
  "  la x10, .Lstr_bench\n" ++
  "  call putstr\n" ++
  "  la x10, .Lstr_name\n" ++
  "  call putstr\n" ++
  "  la x10, .Lstr_sp\n" ++
  "  call putstr\n" ++
  "  mv x14, x6\n" ++
  "  call putdec\n" ++
  "  la x10, .Lstr_sp\n" ++
  "  call putstr\n" ++
  (if hasLatRegion then
    "  mv x14, x7\n" ++
    "  call putdec\n"
   else
    "  la x10, .Lstr_dash\n" ++
    "  call putstr\n") ++
  "  la x10, .Lstr_nl\n" ++
  "  call putstr\n"

/-- Preamble: stack, scratch base, constants, chain-register setup. -/
def preamble (d : InstructionDef) : String :=
  let isDbl := d.extension.any (fun e => e == "rv_d" || e == "rv64_d")
  let fpLoad := if isDbl then "fld" else "flw"
  let fpInit :=
    s!"  la x30, .Lc1\n" ++
    s!"  {fpLoad} f{BENCH_CONST_F}, 0(x30)\n" ++
    s!"  la x30, .Lc2\n" ++
    s!"  {fpLoad} f{BENCH_CONST_F2}, 0(x30)\n"
  let chainInit :=
    if isMemChain d then
      "  la x5, bench_scratch\n" ++
      "  sd x5, 0(x5)\n"
    else if latencyEligible d && !d.opType.hasFpRd then
      "  li x5, 8\n"
    else if isBranch d then
      "  li x8, 8\n" ++
      "  li x9, 9\n"
    else
      ""
  -- FP latency chains re-arm the chain register with 1.0 before the region
  let fpReinit :=
    if latencyEligible d && d.opType.hasFpRd then
      let fldW := if isDbl then "d" else "s"
      -- fsgnj is always available and copies f7 -> f6 without side effects
      s!"  fsgnj.{fldW} f{BENCH_CHAIN_F}, f{BENCH_CONST_F}, f{BENCH_CONST_F}\n"
    else
      ""
  "  la sp, _stack_top\n" ++
  "  la x28, bench_scratch\n" ++
  "  li x12, 8\n" ++
  "  li x29, 256\n" ++
  (if d.opType.isFpGroup then fpInit else "") ++
  chainInit ++
  fpReinit

/-- Branch latency region re-arms the taken-loop registers. -/
def latPreamble (d : InstructionDef) : String :=
  let fpReinit :=
    if latencyEligible d && d.opType.hasFpRd then
      let isDbl := d.extension.any (fun e => e == "rv_d" || e == "rv64_d")
      let fldW := if isDbl then "d" else "s"
      s!"  fsgnj.{fldW} f{BENCH_CHAIN_F}, f{BENCH_CONST_F}, f{BENCH_CONST_F}\n"
    else
      ""
  let branchInit :=
    if isBranch d then "  li x8, 8\n  li x9, 9\n" else ""
  "  li x29, 256\n" ++ branchInit ++ fpReinit

/-- Data: scratch buffer + rodata constants + strings. -/
def dataSection (spec : BenchmarkSpec) (d : InstructionDef) : String :=
  let isDbl := d.extension.any (fun e => e == "rv_d" || e == "rv64_d")
  let c1 := if isDbl then ".dword 0x3FF0000000000000" else ".word 0x3F800000"
  let c2 := if isDbl then ".dword 0x4000000000000000" else ".word 0x40000000"
  ".section .data\n" ++
  ".balign 8\n" ++
  "bench_scratch:\n" ++
  s!"  .space {BENCH_SCRATCH}\n\n" ++
  ".section .rodata\n" ++
  ".Lc1:\n" ++
  s!"  {c1}\n" ++
  ".Lc2:\n" ++
  s!"  {c2}\n" ++
  ".Lstr_bench:\n" ++
  "  .string \"BENCH \"\n" ++
  ".Lstr_name:\n" ++
  s!"  .string \"{spec.name}\"\n" ++
  ".Lstr_sp:\n" ++
  "  .string \" \"\n" ++
  ".Lstr_dash:\n" ++
  "  .string \"-\"\n" ++
  ".Lstr_nl:\n" ++
  "  .string \"\\n\"\n"

/-- One self-contained benchmark program (`.S`). -/
def programAsm (spec : BenchmarkSpec) (rawDefs : List InstructionDef) : String :=
  let defOpt := match rawDefs.find? (fun d => d.name == spec.name) with
    | some d => some d
    | none => if spec.needsZbMarch then some (zbInstructionDef spec.name spec.sample) else none
  match defOpt with
  | none => "!ERROR: unknown instruction " ++ spec.name
  | some d =>
    let lat := spec.kind == .latencyAndThroughput || isBranch d
    let latPre := if lat then latPreamble d else ""
    "# Auto-generated benchmark program. DO NOT EDIT. Regenerate with: lake exe gen_benchmarks\n" ++
    s!"# {spec.name} ({if lat then "throughput + chain" else "throughput"})\n" ++
    ".section .text\n" ++
    ".globl _start\n" ++
    "_start:\n" ++
    preamble d ++
    "\n" ++
    "# --- throughput region ---\n" ++
    regionAsm d false ++ "\n\n" ++
    regionCheck spec false ++
    "\n" ++
    (if lat then
      "# --- latency region ---\n" ++
      latPre ++
      regionAsm d true ++ "\n\n" ++
      regionCheck spec true ++ "\n"
     else "") ++
    "# --- epilogue: print and halt ---\n" ++
    printLine lat ++
    "  # pass\n" ++
    "  li x30, 0x1000\n" ++
    "  li x31, 1\n" ++
    "  sw x31, 0(x30)\n" ++
    ".Lhalt:\n" ++
    "  j .Lhalt\n" ++
    ".Lfail:\n" ++
    "  li x30, 0x1000\n" ++
    "  li x31, 0xDEAD\n" ++
    "  sw x31, 0(x30)\n" ++
    "  j .Lhalt\n" ++
    ".Lend:\n" ++
    "  j .Lhalt\n\n" ++
    ioRoutines ++
    "\n  # Skid buffer: prevent speculative prefetch of non-code rodata past ret\n" ++
    "  nop\n  nop\n  nop\n  nop\n  nop\n  nop\n  nop\n  nop\n\n" ++
    dataSection spec d

-- ════════════════════════════════════════════════════════════════════════════
-- I/O: emit programs, JSON manifest, validation
-- ════════════════════════════════════════════════════════════════════════════

def benchAsmDir : String := "testbench/tests/generated/bench"
def benchOutDir : String := "output/bench"

/-- File prefix / march group for a spec: fp_ (F/D) or amo_ (A), else none. -/
def marchPrefix (spec : BenchmarkSpec) : String :=
  if spec.needsFpMarch then "fp_"
  else if spec.needsAmoMarch then "amo_"
  else if spec.needsZbMarch then "zb_"
  else ""

/-- Emit all benchmark programs + bench-programs.json; hard-fails on any
    sample that does not decode back to its own opType. -/
def emitAll (config : CPUConfig := defaultCPUConfig) : IO Unit := do
  let opcodesPath := Shoumei.RISCV.instrDictPath
  unless (← opcodesPath.pathExists) do
    IO.println "  instr_dict.json not found, running 'make opcodes'..."
    let result ← IO.Process.run { cmd := "make", args := #["opcodes"] }
    unless result.isEmpty do
      IO.println result
  let rawDefs ← loadInstrDictFromFile opcodesPath
  let defs ← loadInstrDefsForConfig config
  let specs := computeSpecs defs

  -- Validate every sample encoding: a wrong sample is a wrong benchmark.
  for spec in specs do
    match spec.opType with
    | some expectedOt =>
      match (decodeInstruction rawDefs spec.sample 0).map (·.opType) with
      | some ot =>
          if ot != expectedOt then
            throw (IO.userError
              s!"bench sample for {spec.name} decodes to {ot}, expected {expectedOt}")
      | none =>
          throw (IO.userError s!"bench sample for {spec.name} does not decode")
    | none => pure ()
  IO.FS.createDirAll benchAsmDir
  IO.FS.createDirAll benchOutDir

  let mut count := 0
  for spec in specs do
    let asm := programAsm spec rawDefs
    let path := s!"{benchAsmDir}/{marchPrefix spec}{spec.name}.S"
    IO.FS.writeFile path asm
    count := count + 1

  -- JSON manifest {name, kind, sample, march}
  let entries := specs.map fun spec =>
    "  { \"name\": \"" ++ spec.name ++
    "\", \"kind\": \"" ++ spec.kind.toString ++
    "\", \"sample\": " ++ toString spec.sample.toNat.repr ++
    ", \"march\": \"" ++ marchPrefix spec ++ "\" }"
  let json := "[\n" ++ String.intercalate ",\n" entries ++ "\n]\n"
  IO.FS.writeFile s!"{benchOutDir}/bench-programs.json" json

  IO.println s!"Generated {count} benchmark programs ({specs.length} specs)"
  for spec in specs do
    IO.println s!"  {marchPrefix spec}{spec.name} kind={spec.kind.toString} sample={spec.sample}"

/-- Metaprogram entry point: body typechecks at file load; the command runs
    `emitAll` when invoked (fallback path if liftIO is unavailable). -/
elab "benchmark_programs!" : command => do
  let _ ← liftIO (emitAll)
  logInfo "benchmark programs generated"

end Shoumei.RISCV
