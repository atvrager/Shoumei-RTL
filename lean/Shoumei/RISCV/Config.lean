/-
  RISC-V CPU Configuration

  Feature-flag system for configurable ISA extensions.
  Controls which instructions are decoded and which execution units are synthesized.
  This is a build-time parameter -- no runtime mux overhead in hardware.
-/

namespace Shoumei.RISCV

/-- CPU configuration flags. Controls which extensions are synthesized.
    Each Bool flag gates the inclusion of circuits at code generation time
    and the inclusion of instruction definitions at decode time. -/
structure CPUConfig where
  /-- RV32I base ISA (always true) -/
  enableI : Bool := true
  /-- M extension: integer multiply/divide (MUL, MULH, MULHSU, MULHU, DIV, DIVU, REM, REMU) -/
  enableM : Bool := false
  /-- C extension: compressed instructions (future) -/
  enableC : Bool := false
  /-- Zicsr extension: CSR instructions (future) -/
  enableZicsr : Bool := false
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
  /-- Pipeline stages on store buffer forwarding path before CDB merge.
      0 = combinational (current behavior), 1 = registered (for timing closure).
      When 1, SB forwarding result is registered and merged after the CDB DFF,
      bypassing the main CDB arbiter to avoid double-delay. -/
  sbFwdPipelineStages : Nat := 1
  deriving Repr, BEq, DecidableEq

/-- Map config flags to riscv-opcodes extension strings.
    This bridges CPUConfig and the JSON-based instruction definitions
    from third_party/riscv-opcodes/instr_dict.json. -/
def CPUConfig.enabledExtensions (config : CPUConfig) : List String :=
  (if config.enableI then ["rv_i", "rv32_i"] else []) ++
  (if config.enableM then ["rv_m"] else []) ++
  (if config.enableC then ["rv_c"] else []) ++
  (if config.enableZicsr then ["rv_zicsr"] else [])

/-- Check if M extension operations should be accepted by the decoder -/
def CPUConfig.supportsMulDiv (config : CPUConfig) : Bool :=
  config.enableM

/-- Default RV32I configuration (no extensions) -/
def rv32iConfig : CPUConfig := {}

/-- RV32IM configuration (M extension enabled) -/
def rv32imConfig : CPUConfig := { enableM := true }



/-
RVVI-TRACE Interface Parameters

The RVVI (RISC-V Verification Interface) is the standard trace port for RISC-V
processor verification. RVVI-TRACE parameters are derived from the Lean CPU
model at code generation time, ensuring consistency between the behavioral model
and the structural circuit.

See docs/cosimulation.md for details on lock-step cosimulation with Spike and SystemC.
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
  let cExt := if cfg.enableC then "C" else ""
  base ++ mExt ++ cExt

/-- Opcode encodings that differ between RV32I and RV32IM decoders.
    The decoder assigns sequential numbers to instructions; M-extension
    instructions shift the encodings of base instructions. -/
structure OpcodeEncodings where
  lui : Nat
  auipc : Nat
  jal : Nat
  jalr : Nat
  beq : Nat
  bne : Nat
  blt : Nat
  bge : Nat
  bltu : Nat
  bgeu : Nat
  lw : Nat
  lh : Nat
  lhu : Nat
  lb : Nat
  lbu : Nat

/-- RV32I decoder opcode encodings -/
def opcodeEncodings_RV32I : OpcodeEncodings :=
  { lui := 19, auipc := 35, jal := 25, jalr := 24,
    beq := 34, bne := 29, blt := 31, bge := 33, bltu := 30, bgeu := 32,
    lw := 18, lh := 21, lhu := 20, lb := 23, lbu := 22 }

/-- RV32IM decoder opcode encodings -/
def opcodeEncodings_RV32IM : OpcodeEncodings :=
  { lui := 25, auipc := 43, jal := 31, jalr := 30,
    beq := 42, bne := 37, blt := 39, bge := 41, bltu := 38, bgeu := 40,
    lw := 24, lh := 27, lhu := 26, lb := 29, lbu := 28 }

/-- Get opcode encodings for a CPU config -/
def CPUConfig.opcodeEncodings (cfg : CPUConfig) : OpcodeEncodings :=
  if cfg.enableM then opcodeEncodings_RV32IM else opcodeEncodings_RV32I

end Shoumei.RISCV
