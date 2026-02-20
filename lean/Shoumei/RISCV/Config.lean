/-
  RISC-V CPU Configuration

  Feature-flag system for configurable ISA extensions.
  Controls which instructions are decoded and which execution units are synthesized.
  This is a build-time parameter -- no runtime mux overhead in hardware.
-/
import Shoumei.RISCV.OpTypeGenerated

namespace Shoumei.RISCV

/-- CSR execution mode: hardwired FSM or ROM-driven microcode sequencer -/
inductive CSRMode where
  | hardwired    -- current serialize FSM (mkSerializeDetect)
  | microcoded   -- ROM-driven microcode sequencer
  deriving Repr, BEq, DecidableEq, Inhabited

/-- CPU configuration flags. Controls which extensions are synthesized.
    Each Bool flag gates the inclusion of circuits at code generation time
    and the inclusion of instruction definitions at decode time. -/
structure CPUConfig where
  -- ═══ ISA Extensions ═══
  /-- RV32I base ISA (always true) -/
  enableI : Bool := true
  /-- M extension: integer multiply/divide (MUL, MULH, MULHSU, MULHU, DIV, DIVU, REM, REMU) -/
  enableM : Bool := false
  /-- F extension: single-precision floating-point (IEEE 754) -/
  enableF : Bool := false
  /-- C extension: compressed instructions (future) -/
  enableC : Bool := false
  /-- Zicsr extension: CSR instructions (CSRRW/S/C, CSRRWI/SI/CI, mcycle, minstret, mscratch) -/
  enableZicsr : Bool := false
  /-- Zifencei extension: instruction-fetch fence (FENCE.I) -/
  enableZifencei : Bool := false
  /-- Register width (32 for RV32, 64 for RV64) -/
  xlen : Nat := 32
  /-- ROB commit width (number of instructions retired per cycle) -/
  commitWidth : Nat := 1
  /-- Number of harts (hardware threads / cores) - FUTURE -/
  numHarts : Nat := 1
  /-- Entry point address for program execution (typically 0x80000000 for bare-metal RISC-V) -/
  entryPoint : UInt32 := 0x80000000
  /-- Pipeline stages on store buffer forwarding path before CDB FIFO enqueue.
      0 = combinational (default), 1 = registered (for timing closure).
      The CDB FIFO decouples timing, so both settings are correct. -/
  sbFwdPipelineStages : Nat := 0
  /-- CSR execution mode: hardwired serialize FSM or ROM-driven microcode sequencer -/
  csrMode : CSRMode := .hardwired

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
  /-- L1 Instruction cache: number of sets -/
  l1iSets : Nat := 8
  /-- L1 Data cache: number of sets -/
  l1dSets : Nat := 4
  /-- L1 Data cache: number of ways (associativity) -/
  l1dWays : Nat := 2
  /-- L2 Unified cache: number of sets -/
  l2Sets : Nat := 8
  /-- L2 Unified cache: number of ways (associativity) -/
  l2Ways : Nat := 2
  /-- Words per cache line (8 words = 32 bytes) -/
  cacheLineWords : Nat := 8

  -- ═══ Simulation ═══
  /-- Memory size in words for testbench -/
  memSizeWords : Nat := 16384
  /-- Simulation timeout in clock cycles -/
  timeoutCycles : Nat := 100000
  deriving Repr, BEq, DecidableEq

/-! ## Derived Helpers -/

/-- Helper: compute log2 of a power of 2 (or ceiling for non-powers) -/
private def log2Ceil (n : Nat) : Nat :=
  if n <= 1 then 0
  else Nat.log2 n + (if 2^(Nat.log2 n) < n then 1 else 0)

/-- Physical register tag width in bits (e.g., 6 for 64 registers) -/
def CPUConfig.physTagWidth (c : CPUConfig) : Nat := log2Ceil c.numPhysRegs

/-- ROB index width in bits (e.g., 4 for 16 entries) -/
def CPUConfig.robIdxWidth (c : CPUConfig) : Nat := log2Ceil c.robEntries

/-- Store buffer index width in bits (e.g., 3 for 8 entries) -/
def CPUConfig.sbIdxWidth (c : CPUConfig) : Nat := log2Ceil c.storeBufferEntries

/-- Cache line offset bits (e.g., 5 for 8 words × 4 bytes = 32 bytes) -/
def CPUConfig.cacheOffsetBits (c : CPUConfig) : Nat := log2Ceil (c.cacheLineWords * 4)

/-- L1I tag bits (address width - index bits - offset bits) -/
def CPUConfig.l1iTagBits (c : CPUConfig) : Nat := 32 - log2Ceil c.l1iSets - c.cacheOffsetBits

/-- L1D tag bits -/
def CPUConfig.l1dTagBits (c : CPUConfig) : Nat := 32 - log2Ceil c.l1dSets - c.cacheOffsetBits

/-- L2 tag bits -/
def CPUConfig.l2TagBits (c : CPUConfig) : Nat := 32 - log2Ceil c.l2Sets - c.cacheOffsetBits

/-- Cache size string for module naming (e.g., "L1I256B_L1D256B_L2512B") -/
def CPUConfig.cacheString (c : CPUConfig) : String :=
  let lineBytes := c.cacheLineWords * 4
  let l1iBytes := c.l1iSets * lineBytes
  let l1dBytes := c.l1dSets * c.l1dWays * lineBytes
  let l2Bytes := c.l2Sets * c.l2Ways * lineBytes
  s!"L1I{l1iBytes}B_L1D{l1dBytes}B_L2{l2Bytes}B"

/-- Map config flags to riscv-opcodes extension strings.
    This bridges CPUConfig and the JSON-based instruction definitions
    from third_party/riscv-opcodes/instr_dict.json. -/
def CPUConfig.enabledExtensions (config : CPUConfig) : List String :=
  (if config.enableI then ["rv_i", "rv32_i"] else []) ++
  (if config.enableM then ["rv_m"] else []) ++
  (if config.enableF then ["rv_f"] else []) ++
  (if config.enableC then ["rv_c"] else []) ++
  (if config.enableZicsr then ["rv_zicsr"] else []) ++
  (if config.enableZifencei then ["rv_zifencei"] else [])

/-- Check if M extension operations should be accepted by the decoder -/
def CPUConfig.supportsMulDiv (config : CPUConfig) : Bool :=
  config.enableM

/-- THE default config. Edit this single definition to change what gets built.
    RV32IMF + Zicsr + Zifencei + Cache, with standard microarch parameters. -/
def defaultCPUConfig : CPUConfig := {
  enableM := true
  enableF := true
  enableZicsr := true
  enableZifencei := true
  enableCache := true
}

/-- Default RV32I configuration (no extensions) -/
def rv32iConfig : CPUConfig := {}

/-- RV32IM configuration (M extension enabled) -/
def rv32imConfig : CPUConfig := { enableM := true, enableZicsr := true, enableZifencei := true }

/-- RV32IF configuration (F extension enabled, no M) -/
def rv32ifConfig : CPUConfig := { enableF := true, enableZicsr := true, enableZifencei := true }

/-- RV32IMF configuration (M + F + Zicsr + Zifencei) -/
def rv32imfConfig : CPUConfig := { enableM := true, enableF := true, enableZicsr := true, enableZifencei := true }

/-- RV32IMF with microcoded CSR sequencer -/
def rv32imfMicrocodedConfig : CPUConfig := { enableM := true, enableF := true, enableZicsr := true, enableZifencei := true, csrMode := .microcoded }


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
  let fExt := if cfg.enableF then "F" else ""
  let cExt := if cfg.enableC then "C" else ""
  let zicsr := if cfg.enableZicsr then "_Zicsr" else ""
  let zifencei := if cfg.enableZifencei then "_Zifencei" else ""
  let ucode := match cfg.csrMode with | .hardwired => "" | .microcoded => "_Microcoded"
  base ++ mExt ++ fExt ++ cExt ++ zicsr ++ zifencei ++ ucode

/-- Full CPU module name including ISA string and optional cache suffix -/
def CPUConfig.fullName (c : CPUConfig) : String :=
  let base := s!"CPU_{c.isaString}"
  if c.enableCache then s!"{base}_{c.cacheString}" else base

/-- Spike ISA string for cosimulation (e.g., "rv32imf_zicsr_zifencei") -/
def CPUConfig.spikeIsa (c : CPUConfig) : String :=
  let base := s!"rv{c.xlen}i"
  let m := if c.enableM then "m" else ""
  let f := if c.enableF then "f" else ""
  let c_ := if c.enableC then "c" else ""
  let zicsr := if c.enableZicsr then "_zicsr" else ""
  let zifencei := if c.enableZifencei then "_zifencei" else ""
  base ++ m ++ f ++ c_ ++ zicsr ++ zifencei

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

end Shoumei.RISCV
