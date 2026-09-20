/-
  RISC-V CPU Configuration

  Feature-flag system for configurable ISA extensions.
  Controls which instructions are decoded and which execution units are synthesized.
  This is a build-time parameter -- no runtime mux overhead in hardware.
-/
import Shoumei.DSL
import Shoumei.RISCV.OpTypeGenerated

namespace Shoumei.RISCV

/-- Instruction classes the microcode ROM knows how to handle.
    Add entries here as new ROM sequences are written. -/
inductive MicrocodeSequence where
  | csr       -- CSRRW/S/C and immediate variants (ROM sequences 0–2)
  | fenceI    -- FENCE.I (ROM sequence 3)
  | trapEntry -- ECALL trap entry (ROM sequence 4)
  | mret      -- MRET return from trap (ROM sequence 5)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- All sequences the ROM currently implements. -/
def knownMicrocodeSequences : List MicrocodeSequence := [.csr, .fenceI, .trapEntry, .mret]

/-- Cache hierarchy geometry.

    Sizes are chosen per PDK from one rule (`docs/lsu-architecture.md` §13):
    the SRAM budget is the silicon left after the core, and every level is a
    multiple of the 4 KiB page granularity that TileLink/AXI address decoding
    uses.  With `lineWords` words per line, a level's per-way array is
    `sets × lineWords × 4` bytes; keeping that at 4 KiB puts every index bit
    inside the page offset (`indexBits + offsetBits = 12`), so no lookup
    reaches outside one page and all levels share one index/tag geometry.

    `default` is the historical geometry (L1I 256 B, L1D 256 B, L2 512 B, 32 B
    lines) and the builders keep it byte-identical, so proofs, compositional
    certificates and the cosimulation baseline stay valid.

    `dataPort` selects the physical memory contract the data arrays are written
    against (see `Shoumei.SRAMPortKind`); `r1w1` is the historical one. -/
structure CacheGeom where
  /-- L1 Instruction cache: sets per way (direct-mapped when `l1iWays = 1`) -/
  l1iSets : Nat := 8
  /-- L1 Instruction cache: ways -/
  l1iWays : Nat := 1
  /-- L1 Data cache: sets per way -/
  l1dSets : Nat := 4
  /-- L1 Data cache: ways -/
  l1dWays : Nat := 2
  /-- L2 unified cache: sets per way -/
  l2Sets : Nat := 8
  /-- L2 unified cache: ways -/
  l2Ways : Nat := 2
  /-- Words per line (8 words = 32 B) -/
  lineWords : Nat := 8
  /-- Physical contract for the data arrays -/
  dataPort : SRAMPortKind := .r1w1
  deriving Repr, BEq, DecidableEq

namespace CacheGeom

/-- The historical geometry: 32 B lines, L1I 256 B, L1D 256 B, L2 512 B. -/
def default : CacheGeom := {}

/-- Production-MCU geometry for a several-KB hierarchy: L1I 8 KiB 2-way,
    L1D 16 KiB 4-way, L2 32 KiB 8-way, 64 B lines.  Every level is 64 sets per
    way, so index+offset = 12 bits - exactly one 4 KiB page - and all three
    share one index/tag geometry.  Data arrays use the single-port byte-mask
    contract so a process's 1RW macros bind directly. -/
def mcu64 : CacheGeom :=
  { l1iSets := 64, l1iWays := 2
    l1dSets := 64, l1dWays := 4
    l2Sets := 64, l2Ways := 8
    lineWords := 16
    dataPort := .rw1ByteMask }

/-- Bytes per line. -/
def lineBytes (g : CacheGeom) : Nat := g.lineWords * 4

/-- Capacity of one level in bytes. -/
def levelBytes (g : CacheGeom) (sets ways : Nat) : Nat := sets * ways * g.lineBytes

/-- Total capacity in bytes. -/
def totalBytes (g : CacheGeom) : Nat :=
  g.levelBytes g.l1iSets g.l1iWays + g.levelBytes g.l1dSets g.l1dWays +
    g.levelBytes g.l2Sets g.l2Ways

/-- True for the geometry the builders keep byte-identical. -/
def isDefault (g : CacheGeom) : Bool := g == default

/-- Short capacity label for module names: 8192 -> "8K", 1048576 -> "1M";
    a value with no exact unit falls back to bytes. -/
def sizeLabel (bytes : Nat) : String :=
  if bytes % (1024 * 1024) == 0 then s!"{bytes / (1024 * 1024)}M"
  else if bytes % 1024 == 0 then s!"{bytes / 1024}K"
  else s!"{bytes}B"

/-- Module-name suffix: empty for the default geometry (emitted module names,
    proofs and certificates unchanged), else the capacity, so two configured
    hierarchies can coexist in one build. -/
def nameSuffix (g : CacheGeom) : String :=
  if g.isDefault then ""
  else
    let l1i := g.levelBytes g.l1iSets g.l1iWays
    let l1d := g.levelBytes g.l1dSets g.l1dWays
    let l2 := g.levelBytes g.l2Sets g.l2Ways
    s!"_L1I{sizeLabel l1i}_L1D{sizeLabel l1d}_L2{sizeLabel l2}"

end CacheGeom

/-- CPU configuration flags. Controls which extensions are synthesized.
    Each Bool flag gates the inclusion of circuits at code generation time
    and the inclusion of instruction definitions at decode time. -/
structure CPUConfig where
  -- ═══ ISA Extensions ═══
  /-- RV32I base ISA (always true) -/
  enableI : Bool := true
  /-- M extension: integer multiply/divide (MUL, MULH, MULHSU, MULHU, DIV, DIVU, REM, REMU) -/
  enableM : Bool := false
  /-- A extension: atomics (LR.W, SC.W, AMO*.W) -/
  enableA : Bool := false
  /-- F extension: single-precision floating-point (IEEE 754) -/
  enableF : Bool := false
  /-- D extension: double-precision floating-point (IEEE 754) -/
  enableD : Bool := false
  /-- C extension: compressed instructions (future) -/
  enableC : Bool := false
  /-- Zicsr extension: CSR instructions (CSRRW/S/C, CSRRWI/SI/CI, mcycle, minstret, mscratch) -/
  enableZicsr : Bool := false
  /-- Zifencei extension: instruction-fetch fence (FENCE.I) -/
  enableZifencei : Bool := false
  /-- Register width (32 for RV32, 64 for RV64) -/
  xlen : Nat := 64
  /-- Number of instructions fetched, decoded, renamed, and dispatched per cycle -/
  dispatchWidth : Nat := 2
  /-- ROB commit width (number of instructions retired per cycle) -/
  commitWidth : Nat := 2
  /-- Number of harts (hardware threads / cores) - FUTURE -/
  numHarts : Nat := 1
  /-- Entry point address for program execution (typically 0x80000000 for bare-metal RISC-V) -/
  entryPoint : UInt32 := 0x80000000
  /-- Pipeline stages on store buffer forwarding path before CDB FIFO enqueue.
      0 = combinational (default), 1 = registered (for timing closure).
      The CDB FIFO decouples timing, so both settings are correct. -/
  sbFwdPipelineStages : Nat := 0
  /-- Microcode sequences to enable. Empty = all-hardwired (default).
      Only sequences listed in knownMicrocodeSequences are valid. -/
  enabledMicrocode : List MicrocodeSequence := []

  -- ═══ Microarchitecture ═══
  /-- Number of physical registers (default 64, giving 6-bit tags) -/
  numPhysRegs : Nat := 64
  /-- Number of Reorder Buffer entries -/
  robEntries : Nat := 16
  /-- Number of store buffer entries -/
  storeBufferEntries : Nat := 8
  /-- Number of reservation station entries (integer, memory, MulDiv, FP) -/
  rsEntries : Nat := 4

  -- ═══ Cache Hierarchy ═══
  /-- Enable L1I/L1D/L2 cache hierarchy (wraps CPU in CachedCPU) -/
  enableCache : Bool := false
  /-- Cache hierarchy geometry (sizes, associativity, line size) -/
  cacheGeom : CacheGeom := CacheGeom.default

  -- ═══ Simulation ═══
  /-- Memory size in words for testbench -/
  memSizeWords : Nat := 65536
  /-- Simulation timeout in clock cycles -/
  timeoutCycles : Nat := 100000
  deriving Repr, BEq, DecidableEq

/-! ## Derived Helpers -/

/-- Ceiling log2 of a power of two (0 for n ≤ 1); the cache builders derive
    index/tag widths from geometry with it. -/
def log2Ceil (n : Nat) : Nat :=
  if n <= 1 then 0
  else Nat.log2 n + (if 2^(Nat.log2 n) < n then 1 else 0)

/-- Physical register tag width in bits (e.g., 6 for 64 registers) -/
def CPUConfig.physTagWidth (c : CPUConfig) : Nat := log2Ceil c.numPhysRegs

/-- ROB index width in bits (e.g., 4 for 16 entries) -/
def CPUConfig.robIdxWidth (c : CPUConfig) : Nat := log2Ceil c.robEntries

/-- Store buffer index width in bits (e.g., 3 for 8 entries) -/
def CPUConfig.sbIdxWidth (c : CPUConfig) : Nat := log2Ceil c.storeBufferEntries

/-- Cache line offset bits (e.g. 5 for 8 words × 4 bytes = 32 bytes) -/
def CPUConfig.cacheOffsetBits (c : CPUConfig) : Nat := log2Ceil c.cacheGeom.lineBytes

/-- L1I tag bits (address width - index bits - offset bits) -/
def CPUConfig.l1iTagBits (c : CPUConfig) : Nat :=
  c.xlen - log2Ceil c.cacheGeom.l1iSets - c.cacheOffsetBits

/-- L1D tag bits -/
def CPUConfig.l1dTagBits (c : CPUConfig) : Nat :=
  c.xlen - log2Ceil c.cacheGeom.l1dSets - c.cacheOffsetBits

/-- L2 tag bits -/
def CPUConfig.l2TagBits (c : CPUConfig) : Nat :=
  c.xlen - log2Ceil c.cacheGeom.l2Sets - c.cacheOffsetBits

/-- Cache size string for module naming (e.g., "L1I256B_L1D256B_L2512B" for the
    default geometry, "L1I8K_L1D16K_L232K" for the MCU preset) -/
def CPUConfig.cacheString (c : CPUConfig) : String :=
  let g := c.cacheGeom
  let l1iBytes := g.levelBytes g.l1iSets g.l1iWays
  let l1dBytes := g.levelBytes g.l1dSets g.l1dWays
  let l2Bytes := g.levelBytes g.l2Sets g.l2Ways
  s!"L1I{CacheGeom.sizeLabel l1iBytes}_L1D{CacheGeom.sizeLabel l1dBytes}_L2{CacheGeom.sizeLabel l2Bytes}"

/-- Floating-point register width in bits (FLEN): 64 if D enabled or RV64, else 32.
    FLEN is a computed projection of the configuration, not a stored field. -/
def CPUConfig.flen (c : CPUConfig) : Nat :=
  if c.enableD || c.xlen == 64 then 64 else 32

/-- Map config flags to riscv-opcodes extension strings.
    This bridges CPUConfig and the JSON-based instruction definitions
    from third_party/riscv-opcodes/instr_dict.json. -/
def CPUConfig.enabledExtensions (config : CPUConfig) : List String :=
  (if config.enableI then (if config.xlen == 64 then ["rv_i", "rv64_i"] else ["rv_i", "rv32_i"]) else []) ++
  (if config.enableM then (if config.xlen == 64 then ["rv_m", "rv64_m"] else ["rv_m"]) else []) ++
  (if config.enableA then (if config.xlen == 64 then ["rv_a", "rv64_a"] else ["rv_a"]) else []) ++
  (if config.enableF then (if config.xlen == 64 then ["rv_f", "rv64_f"] else ["rv_f"]) else []) ++
  (if config.enableD then (if config.xlen == 64 then ["rv_d", "rv64_d"] else ["rv_d"]) else []) ++
  (if config.enableC then ["rv_c"] else []) ++
  (if config.enableZicsr then ["rv_zicsr"] else []) ++
  (if config.enableZifencei then ["rv_zifencei"] else []) ++
  (if config.enabledMicrocode.contains .mret then ["rv_system"] else [])

/-- Check if M extension operations should be accepted by the decoder -/
def CPUConfig.supportsMulDiv (config : CPUConfig) : Bool :=
  config.enableM

/-- Whether any microcode sequences are enabled -/
def CPUConfig.useMicrocode (c : CPUConfig) : Bool := !c.enabledMicrocode.isEmpty

/-- Whether the CSR microcode sequence is enabled -/
def CPUConfig.microcodesCSR (c : CPUConfig) : Bool := c.enabledMicrocode.contains .csr

/-- Whether the FENCE.I microcode sequence is enabled -/
def CPUConfig.microcodesFenceI (c : CPUConfig) : Bool := c.enabledMicrocode.contains .fenceI

/-- Whether the trap entry microcode sequence is enabled -/
def CPUConfig.microcodesTraps (c : CPUConfig) : Bool := c.enabledMicrocode.contains .trapEntry

/-- Whether the MRET microcode sequence is enabled -/
def CPUConfig.microcodesMRET (c : CPUConfig) : Bool := c.enabledMicrocode.contains .mret

/-- THE default config. Edit this single definition to change what gets built.
    RV64IMAFD + Zicsr + Zifencei + Cache, N=2 superscalar dispatch + retire. -/
def defaultCPUConfig : CPUConfig := {
  xlen := 64
  enableM := true
  enableA := true
  enableF := true
  enableD := true
  enableZicsr := true
  enableZifencei := true
  enableCache := true
  enabledMicrocode := [.trapEntry, .mret]
  dispatchWidth := 2
  commitWidth := 2
}

/-- The MCU-class part: the default RV64IMAFD_Zicsr_Zifencei CPU with the
    `CacheGeom.mcu64` hierarchy (L1I 8 KiB 2-way, L1D 16 KiB 4-way, L2 32 KiB
    8-way, 64-byte lines, single-port byte-mask data arrays). -/
def mcu64CPUConfig : CPUConfig := { defaultCPUConfig with cacheGeom := CacheGeom.mcu64 }

/-- Default RV32I configuration (no extensions) -/
def rv32iConfig : CPUConfig := { xlen := 32 }

/-- RV32IM configuration (M extension enabled) -/
def rv32imConfig : CPUConfig := { xlen := 32, enableM := true, enableZicsr := true, enableZifencei := true }

/-- RV32IF configuration (F extension enabled, no M) -/
def rv32ifConfig : CPUConfig := { xlen := 32, enableF := true, enableZicsr := true, enableZifencei := true }

/-- RV32IMF configuration (M + F + Zicsr + Zifencei) -/
def rv32imfConfig : CPUConfig := { xlen := 32, enableM := true, enableF := true, enableZicsr := true, enableZifencei := true }

/-- RV32IMA configuration (M + A + Zicsr + Zifencei) -/
def rv32imaConfig : CPUConfig := { xlen := 32, enableM := true, enableA := true, enableZicsr := true, enableZifencei := true }

/-- RV32G configuration (RV32IMAFD + Zicsr + Zifencei) -/
def rv32gConfig : CPUConfig := { xlen := 32, enableM := true, enableA := true, enableF := true, enableD := true, enableZicsr := true, enableZifencei := true }

/-- RV64G configuration (RV64IMAFD + Zicsr + Zifencei) -/
def rv64gConfig : CPUConfig := { xlen := 64, enableM := true, enableA := true, enableF := true, enableD := true, enableZicsr := true, enableZifencei := true }

/-- RV32IMF with microcoded trap entry sequencer -/
def rv32imfMicrocodedConfig : CPUConfig := { xlen := 32, enableM := true, enableF := true, enableZicsr := true, enableZifencei := true, enabledMicrocode := [.trapEntry] }


/-
RVVI-TRACE Interface Parameters

The RVVI (RISC-V Verification Interface) is the standard trace port for RISC-V
processor verification. RVVI-TRACE parameters are derived from the Lean CPU
model at code generation time, ensuring consistency between the behavioral model
and the structural circuit.

See docs/cosimulation.md for details on lock-step cosimulation with Spike.
-/

/-- RVVI-TRACE interface parameters derived from CPU config -/
structure RVVIConfig where
  /-- Register width (XLEN) -/
  xlen : Nat
  /-- Instruction width (ILEN): 16 if C extension enabled, else 32 -/
  ilen : Nat
  /-- Number of instructions retired per cycle (NRET) -/
  nret : Nat
  /-- Number of harts (NHART) -/
  nhart : Nat
deriving Repr, BEq

/-- Derive RVVI-TRACE parameters from CPU configuration -/
def CPUConfig.rvviConfig (cfg : CPUConfig) : RVVIConfig :=
  { xlen  := cfg.xlen
    ilen  := if cfg.enableC then 16 else 32
    nret  := cfg.commitWidth
    nhart := cfg.numHarts }

/-- Human-readable ISA string (e.g., "RV32I", "RV32IM", "RV32IMC") -/
def CPUConfig.isaString (cfg : CPUConfig) : String :=
  let base := s!"RV{cfg.xlen}I"
  let mExt := if cfg.enableM then "M" else ""
  let aExt := if cfg.enableA then "A" else ""
  let fExt := if cfg.enableF then "F" else ""
  let dExt := if cfg.enableD then "D" else ""
  let cExt := if cfg.enableC then "C" else ""
  let zicsr := if cfg.enableZicsr then "_Zicsr" else ""
  let zifencei := if cfg.enableZifencei then "_Zifencei" else ""
  let ucode := if cfg.useMicrocode then "_Microcoded" else ""
  base ++ mExt ++ aExt ++ fExt ++ dExt ++ cExt ++ zicsr ++ zifencei ++ ucode

/-- Full CPU module name including ISA string and optional cache suffix -/
def CPUConfig.fullName (c : CPUConfig) : String :=
  let base := s!"CPU_{c.isaString}"
  if c.enableCache then s!"{base}_{c.cacheString}" else base

/-- Spike ISA string for cosimulation (e.g., "rv32imf_zicsr_zifencei") -/
def CPUConfig.spikeIsa (c : CPUConfig) : String :=
  let base := s!"rv{c.xlen}i"
  let m := if c.enableM then "m" else ""
  let a := if c.enableA then "a" else ""
  let f := if c.enableF then "f" else ""
  let d := if c.enableD then "d" else ""
  let c_ := if c.enableC then "c" else ""
  let zicsr := if c.enableZicsr then "_zicsr" else ""
  let zifencei := if c.enableZifencei then "_zifencei" else ""
  let zb := if c.microcodesTraps then "_zba_zbb_zbc_zbs" else ""
  base ++ m ++ a ++ f ++ d ++ c_ ++ zicsr ++ zifencei ++ zb

/-- Compute the decoder instruction name list for a given config.
    Derived from `OpType.all` and `OpType.extensionGroup` -- no handwritten tables.
    Order matches the generated SV decoder enum: reverse alphabetical within
    each group (integer first, then FP appended). -/
def CPUConfig.decoderInstrNames (config : CPUConfig) : List String :=
  let enabled := config.enabledExtensions
  let applicable : List OpType := OpType.all.filter fun op =>
    op.extensionGroup.any fun ext => enabled.contains ext
  let intOps : List OpType := applicable.filter fun op => !op.isFpGroup
  let fpOps : List OpType := applicable.filter fun op => op.isFpGroup
  let revAlpha (a b : String) : Bool := a.toLower > b.toLower
  let sortedInt := (intOps.map (toString ·)).toArray.qsort revAlpha |>.toList
  let sortedFp := (fpOps.map (toString ·)).toArray.qsort revAlpha |>.toList
  sortedInt ++ sortedFp

/-- Look up the decoder index of an OpType for a given config.
    Replaces the old `OpcodeEncodings` struct -- indices are derived, not stored. -/
def CPUConfig.opcodeIndex (cfg : CPUConfig) (op : OpType) : Nat :=
  let names := cfg.decoderInstrNames
  match names.findIdx? (· == toString op) with
  | some idx => idx
  | none => 0

/-- Opcode width in bits for reservation stations and execution pipeline.
    8 bits for RV64G (> 128 instructions), 7 bits for RV32G/RV32IMF, 6 bits for base RV32I. -/
def CPUConfig.opcodeWidth (c : CPUConfig) : Nat :=
  if c.xlen == 64 || c.decoderInstrNames.length > 128 then 8
  else if c.decoderInstrNames.length > 64 then 7
  else 6

end Shoumei.RISCV

