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
    Order matches the generated SV decoder enum: reverse alphabetical within
    each extension group (I+M first in reverse-alpha, then F appended in
    reverse-alpha). Built by collecting instruction names and sorting. -/
def CPUConfig.decoderInstrNames (config : CPUConfig) : List String :=
  let rv32i := ["ADD", "ADDI", "AND", "ANDI", "AUIPC", "BEQ", "BGE", "BGEU",
                "BLT", "BLTU", "BNE", "EBREAK", "ECALL", "FENCE", "JAL",
                "JALR", "LB", "LBU", "LH", "LHU", "LUI", "LW", "OR", "ORI",
                "SB", "SH", "SLL", "SLLI", "SLT", "SLTI", "SLTIU", "SLTU",
                "SRA", "SRAI", "SRL", "SRLI", "SUB", "SW", "XOR", "XORI"]
  let rv_m := ["DIV", "DIVU", "MUL", "MULH", "MULHSU", "MULHU", "REM", "REMU"]
  let rv_zifencei := ["FENCE_I"]
  let rv_zicsr := ["CSRRC", "CSRRCI", "CSRRS", "CSRRSI", "CSRRW", "CSRRWI"]
  let rv_f := ["FADD_S", "FCLASS_S", "FCVT_S_W", "FCVT_S_WU", "FCVT_W_S",
               "FCVT_WU_S", "FDIV_S", "FEQ_S", "FLE_S", "FLT_S", "FLW",
               "FMADD_S", "FMAX_S", "FMIN_S", "FMSUB_S", "FMUL_S", "FMV_W_X",
               "FMV_X_W", "FNMADD_S", "FNMSUB_S", "FSGNJ_S", "FSGNJN_S",
               "FSGNJX_S", "FSQRT_S", "FSUB_S", "FSW"]
  -- Collect applicable instruction names
  let intInstrs := rv32i
    ++ (if config.enableM then rv_m else [])
    ++ (if config.enableZifencei then rv_zifencei else [])
    ++ (if config.enableZicsr then rv_zicsr else [])
  -- Sort in reverse order using lowercase comparison (matches decoder's JSON key
  -- order reversed by foldl prepend; lowercase ensures _ sorts correctly vs letters)
  let revAlpha (a b : String) : Bool := a.toLower > b.toLower
  let sortedInt := intInstrs.toArray.qsort revAlpha |>.toList
  -- F extension instructions are appended after I+M group, also reverse-sorted
  if config.enableF then
    let sortedF := rv_f.toArray.qsort revAlpha |>.toList
    sortedInt ++ sortedF
  else sortedInt

/-- Find index of a name in the decoder instruction list -/
private def findIdx (names : List String) (target : String) : Nat :=
  match names.findIdx? (· == target) with
  | some idx => idx
  | none => 0  -- fallback (shouldn't happen for valid configs)

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
  sw : Nat
  sh : Nat
  sb : Nat
  -- F extension (only valid when enableF)
  flw : Nat := 0
  fsw : Nat := 0
  -- Zifencei extension
  fenceI : Nat := 0
  -- Zicsr extension
  csrrw : Nat := 0
  csrrs : Nat := 0
  csrrc : Nat := 0
  csrrwi : Nat := 0
  csrrsi : Nat := 0
  csrrci : Nat := 0

/-- Build OpcodeEncodings from the decoder instruction name list (auto-resolved). -/
def CPUConfig.opcodeEncodings (cfg : CPUConfig) : OpcodeEncodings :=
  let names := cfg.decoderInstrNames
  let f := findIdx names
  { lui := f "LUI", auipc := f "AUIPC", jal := f "JAL", jalr := f "JALR",
    beq := f "BEQ", bne := f "BNE", blt := f "BLT", bge := f "BGE",
    bltu := f "BLTU", bgeu := f "BGEU",
    lw := f "LW", lh := f "LH", lhu := f "LHU", lb := f "LB", lbu := f "LBU",
    sw := f "SW", sh := f "SH", sb := f "SB",
    flw := if cfg.enableF then f "FLW" else 0,
    fsw := if cfg.enableF then f "FSW" else 0,
    fenceI := if cfg.enableZifencei then f "FENCE_I" else 0,
    csrrw := if cfg.enableZicsr then f "CSRRW" else 0,
    csrrs := if cfg.enableZicsr then f "CSRRS" else 0,
    csrrc := if cfg.enableZicsr then f "CSRRC" else 0,
    csrrwi := if cfg.enableZicsr then f "CSRRWI" else 0,
    csrrsi := if cfg.enableZicsr then f "CSRRSI" else 0,
    csrrci := if cfg.enableZicsr then f "CSRRCI" else 0 }

end Shoumei.RISCV
