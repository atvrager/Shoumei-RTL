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

end Shoumei.RISCV
