/-
  RISC-V CPU Configuration

  Feature-flag system for configurable ISA extensions.
  Controls which instructions are decoded and which execution units are synthesized.
  This is a build-time parameter -- no runtime mux overhead in hardware.
-/
import Shoumei.RISCV.OpTypeGenerated

namespace Shoumei.RISCV

/-- CPU configuration flags. Controls which extensions are synthesized.
    Each Bool flag gates the inclusion of circuits at code generation time
    and the inclusion of instruction definitions at decode time. -/
structure CPUConfig where
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
  /-- Number of MulDiv Reservation Station entries -/
  mulDivRSEntries : Nat := 4
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
  deriving Repr, BEq, DecidableEq

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

/-- Default RV32I configuration (no extensions) -/
def rv32iConfig : CPUConfig := {}

/-- RV32IM configuration (M extension enabled) -/
def rv32imConfig : CPUConfig := { enableM := true, enableZicsr := true, enableZifencei := true }

/-- RV32IF configuration (F extension enabled, no M) -/
def rv32ifConfig : CPUConfig := { enableF := true, enableZicsr := true, enableZifencei := true }

/-- RV32IMF configuration (M + F + Zicsr + Zifencei) -/
def rv32imfConfig : CPUConfig := { enableM := true, enableF := true, enableZicsr := true, enableZifencei := true }


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
  base ++ mExt ++ fExt ++ cExt ++ zicsr ++ zifencei

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
