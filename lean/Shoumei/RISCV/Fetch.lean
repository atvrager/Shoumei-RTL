/-
Fetch Stage - Behavioral Model

The fetch stage retrieves instructions from instruction memory and manages
the program counter (PC). It handles three control flow scenarios:
1. Branch misprediction redirect (highest priority)
2. Pipeline stall (freeze PC)
3. Fetch-stage branch prediction (BTFN + JAL always-taken)
4. Sequential execution (PC += 4)

Phase 9 scope: Added BTFN branch prediction in fetch stage.
-/

import Shoumei.RISCV.Config
import Shoumei.DSL
import Shoumei.Circuits.Sequential.Register
import Shoumei.Circuits.Combinational.KoggeStoneAdder

namespace Shoumei.RISCV

/-- Fetch stage state -/
structure FetchState where
  /-- Current program counter -/
  pc : UInt32
  /-- Fetched instruction (None if no valid instruction) -/
  fetchedInstr : Option UInt32
  /-- Fetch stalled (waiting for pipeline backpressure to clear) -/
  stalled : Bool
deriving Repr, BEq

/-- Initialize fetch state at entry point -/
def FetchState.init (entryPoint : UInt32 := 0x80000000) : FetchState :=
  { pc := entryPoint
    fetchedInstr := none
    stalled := false }

/-
Instruction Memory Model

Simple functional model for testing. Address → instruction word.
Out-of-bounds accesses return 0 (ILLEGAL instruction).
-/

/-- Instruction memory abstraction: address → instruction word -/
def SimpleIMem : Type := UInt32 → UInt32

/-- Load program into instruction memory starting at base address -/
def loadProgram (instrs : List UInt32) (baseAddr : UInt32 := 0x80000000) : SimpleIMem :=
  fun addr =>
    let idx := (addr.toNat - baseAddr.toNat) / 4
    instrs.getD idx 0  -- Return 0 (ILLEGAL) if out of bounds

/-
Fetch Step Function

Executes one cycle of the fetch stage. Control flow priorities:
1. Branch redirect (highest) - Update PC to misprediction recovery target
2. Stall - Freeze PC until pipeline clears
3. Sequential - PC := PC + 4 (normal operation)
-/

/-- Execute one fetch cycle.

    Parameters:
    - state: Current fetch state
    - imem: Instruction memory function
    - stall: Pipeline stall signal (from control logic)
    - branchRedirect: Branch misprediction recovery target (highest priority)

    Returns: Updated fetch state
-/
def fetchStep
    (state : FetchState)
    (imem : SimpleIMem)
    (stall : Bool)
    (branchRedirect : Option UInt32)
    : FetchState :=
  match branchRedirect with
  | some target =>
      -- Priority 1: Branch misprediction recovery
      -- Redirect PC to correct target, fetch instruction, clear stall
      { state with
        pc := target
        fetchedInstr := some (imem target)
        stalled := false }
  | none =>
      if stall then
        -- Priority 2: Stall - freeze PC, mark as stalled
        { state with stalled := true }
      else
        -- Priority 3: Normal - sequential increment
        let instr := imem state.pc
        { state with
          pc := state.pc + 4
          fetchedInstr := some instr
          stalled := false }

/-
Helper functions for testing
-/

/-- Check if fetch is currently stalled -/
def FetchState.isStalled (state : FetchState) : Bool :=
  state.stalled

/-- Get current PC -/
def FetchState.getPC (state : FetchState) : UInt32 :=
  state.pc

/-- Get fetched instruction (if valid) -/
def FetchState.getInstruction (state : FetchState) : Option UInt32 :=
  state.fetchedInstr

/-
Structural Circuit Implementation
-/

open Shoumei
open Shoumei.Circuits.Sequential
open Shoumei.Circuits.Combinational

/-- Helper: Create indexed wires -/
private def makeIndexedWires (name : String) (n : Nat) : List Wire :=
  (List.range n).map (fun i => Wire.mk s!"{name}_{i}")

/--
Build Fetch Stage structural circuit with BTFN branch prediction.

Architecture:
- PC storage: Register32 instance (32-bit register with clock/reset)
- PC increment: KoggeStoneAdder32 instance (PC + 4)
- Branch prediction: Decode B-type/JAL from instruction word, BTFN policy
  - predict_taken = (is_branch AND imm_sign) OR is_jal
  - KoggeStoneAdder32 for PC + imm → predict_target
- Next PC mux: Three-level mux tree for priority logic
  - Level 0: predict_taken ? predict_target : pc_plus_4 (prediction)
  - Level 1: stall ? current_pc : level0_out (stall hold)
  - Level 2: branch_valid ? branch_target : level1_out (redirect override)
- Stalled tracking: 1-bit DFF with control logic

Inputs:
- clock, reset: Control signals
- stall: Pipeline stall signal
- branch_valid: Branch redirect valid
- branch_target[31:0]: Branch redirect target
- instr[31:0]: Fetched instruction word (from IMEM response)
- const_0, const_1: Constant values for adder

Outputs:
- pc[31:0]: Current program counter
- stalled: Fetch stalled status
- predicted_taken: Branch prediction taken flag
-/
def mkFetchStage : Circuit :=
  -- Input wires
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let stall := Wire.mk "stall"
  let branch_valid := Wire.mk "branch_valid"
  let branch_target := makeIndexedWires "branch_target" 32
  let instr := makeIndexedWires "instr" 32
  let const_0 := Wire.mk "const_0"
  let const_1 := Wire.mk "const_1"

  -- Internal wires: PC register
  let pc_reg := makeIndexedWires "pc_reg" 32
  let next_pc := makeIndexedWires "next_pc" 32

  -- Internal wires: Constant 4 generation
  let const_4 := makeIndexedWires "const_4" 32
  let const_4_gates := (List.range 32).map (fun i =>
    if i == 2 then
      Gate.mkBUF const_1 (const_4[i]!)
    else
      Gate.mkBUF const_0 (const_4[i]!)
  )

  -- Internal wires: PC + 4
  let pc_plus_4 := makeIndexedWires "pc_plus_4" 32

  -- === BRANCH PREDICTION (BTFN + JAL always-taken) ===

  -- Decode opcode from instr[6:0]
  -- B-type: opcode = 1100011 (bits 6:0 = 1,1,0,0,0,1,1)
  -- JAL:    opcode = 1101111 (bits 6:0 = 1,1,0,1,1,1,1)
  let is_branch := Wire.mk "is_branch"
  let is_jal_fetch := Wire.mk "is_jal_fetch"

  -- B-type match: instr[6:0] = 1100011
  -- bit0=1, bit1=1, bit2=0, bit3=0, bit4=0, bit5=1, bit6=1
  let not_bit2 := Wire.mk "not_bit2"
  let not_bit3 := Wire.mk "not_bit3"
  let not_bit4 := Wire.mk "not_bit4"
  let btype_tmp1 := Wire.mk "btype_tmp1"
  let btype_tmp2 := Wire.mk "btype_tmp2"
  let btype_tmp3 := Wire.mk "btype_tmp3"
  let btype_tmp4 := Wire.mk "btype_tmp4"
  let btype_tmp5 := Wire.mk "btype_tmp5"

  let btype_gates := [
    Gate.mkNOT instr[2]! not_bit2,
    Gate.mkNOT instr[3]! not_bit3,
    Gate.mkNOT instr[4]! not_bit4,
    Gate.mkAND instr[0]! instr[1]! btype_tmp1,
    Gate.mkAND not_bit2 not_bit3 btype_tmp2,
    Gate.mkAND not_bit4 instr[5]! btype_tmp3,
    Gate.mkAND btype_tmp1 btype_tmp2 btype_tmp4,
    Gate.mkAND btype_tmp3 instr[6]! btype_tmp5,
    Gate.mkAND btype_tmp4 btype_tmp5 is_branch
  ]

  -- JAL match: instr[6:0] = 1101111
  -- bit0=1, bit1=1, bit2=1, bit3=1, bit4=0, bit5=1, bit6=1
  let jal_tmp1 := Wire.mk "jal_tmp1"
  let jal_tmp2 := Wire.mk "jal_tmp2"
  let jal_tmp3 := Wire.mk "jal_tmp3"
  let jal_tmp4 := Wire.mk "jal_tmp4"

  let jal_gates := [
    Gate.mkAND instr[0]! instr[1]! jal_tmp1,
    Gate.mkAND instr[2]! instr[3]! jal_tmp2,
    Gate.mkAND not_bit4 instr[5]! jal_tmp3,
    Gate.mkAND jal_tmp1 jal_tmp2 jal_tmp4,
    Gate.mkAND jal_tmp3 instr[6]! (Wire.mk "jal_tmp5"),
    Gate.mkAND jal_tmp4 (Wire.mk "jal_tmp5") is_jal_fetch
  ]

  -- Immediate extraction for branch target calculation
  -- B-type imm: {instr[31], instr[7], instr[30:25], instr[11:8], 0} sign-extended
  -- JAL imm: {instr[31], instr[19:12], instr[20], instr[30:21], 0} sign-extended
  -- We only need the sign bit (bit 31) for BTFN, and the full immediate for target calculation
  let predict_imm := makeIndexedWires "predict_imm" 32

  -- B-type immediate: {31, 7, 30:25, 11:8, 0}
  -- bit 0: always 0
  -- bits 4:1: instr[11:8]
  -- bits 10:5: instr[30:25]
  -- bit 11: instr[7]
  -- bit 12: instr[31]
  -- bits 31:13: sign extension (instr[31])
  let b_imm := makeIndexedWires "b_imm" 32
  let b_imm_gates :=
    [Gate.mkBUF const_0 b_imm[0]!] ++  -- bit 0 = 0
    (List.range 4).map (fun i => Gate.mkBUF instr[8+i]! b_imm[1+i]!) ++  -- bits 4:1 = instr[11:8]
    (List.range 6).map (fun i => Gate.mkBUF instr[25+i]! b_imm[5+i]!) ++  -- bits 10:5 = instr[30:25]
    [Gate.mkBUF instr[7]! b_imm[11]!,   -- bit 11 = instr[7]
     Gate.mkBUF instr[31]! b_imm[12]!] ++  -- bit 12 = instr[31]
    (List.range 19).map (fun i => Gate.mkBUF instr[31]! b_imm[13+i]!)  -- sign extension

  -- JAL immediate: {31, 19:12, 20, 30:21, 0}
  -- bit 0: always 0
  -- bits 10:1: instr[30:21]
  -- bit 11: instr[20]
  -- bits 19:12: instr[19:12]
  -- bit 20: instr[31]
  -- bits 31:21: sign extension (instr[31])
  let j_imm := makeIndexedWires "j_imm" 32
  let j_imm_gates :=
    [Gate.mkBUF const_0 j_imm[0]!] ++  -- bit 0 = 0
    (List.range 10).map (fun i => Gate.mkBUF instr[21+i]! j_imm[1+i]!) ++  -- bits 10:1 = instr[30:21]
    [Gate.mkBUF instr[20]! j_imm[11]!] ++  -- bit 11 = instr[20]
    (List.range 8).map (fun i => Gate.mkBUF instr[12+i]! j_imm[12+i]!) ++  -- bits 19:12 = instr[19:12]
    [Gate.mkBUF instr[31]! j_imm[20]!] ++  -- bit 20 = instr[31]
    (List.range 11).map (fun i => Gate.mkBUF instr[31]! j_imm[21+i]!)  -- sign extension

  -- MUX: predict_imm = is_jal ? j_imm : b_imm
  let predict_imm_gates := (List.range 32).map (fun i =>
    Gate.mkMUX b_imm[i]! j_imm[i]! is_jal_fetch predict_imm[i]!)

  -- BTFN prediction: predict_taken = (is_branch AND imm_sign) OR is_jal
  let branch_backward := Wire.mk "branch_backward"
  let predicted_taken_wire := Wire.mk "predicted_taken"
  let btfn_gates := [
    Gate.mkAND is_branch instr[31]! branch_backward,
    Gate.mkOR branch_backward is_jal_fetch predicted_taken_wire
  ]

  -- Predict target = PC + predict_imm
  let predict_target := makeIndexedWires "predict_target" 32

  -- Level 0 mux: predict_taken ? predict_target : pc_plus_4
  let level0_out := makeIndexedWires "level0_out" 32
  let level0_mux_gates := (List.range 32).map (fun i =>
    Gate.mkMUX (pc_plus_4[i]!) (predict_target[i]!) predicted_taken_wire (level0_out[i]!)
  )

  -- Level 1 mux: stall ? pc_reg : level0_out
  let stall_mux_out := makeIndexedWires "stall_mux" 32
  let stall_mux_gates := (List.range 32).map (fun i =>
    Gate.mkMUX (level0_out[i]!) (pc_reg[i]!) stall (stall_mux_out[i]!)
  )

  -- Level 2 mux: branch_valid ? branch_target : stall_mux_out
  let branch_mux_gates := (List.range 32).map (fun i =>
    Gate.mkMUX (stall_mux_out[i]!) (branch_target[i]!) branch_valid (next_pc[i]!)
  )

  -- Stalled status control
  let stalled_reg := Wire.mk "stalled_reg"
  let stalled_cleared := Wire.mk "stalled_cleared"
  let stall_and_not_branch := Wire.mk "stall_and_not_branch"

  let stalled_gates := [
    Gate.mkNOT branch_valid stalled_cleared,
    Gate.mkAND stall stalled_cleared stall_and_not_branch,
    Gate.mkDFF stall_and_not_branch clock reset stalled_reg
  ]

  -- Output wires (separate from internal pc_reg to avoid Chisel IO conflicts)
  let pc_out := makeIndexedWires "pc" 32
  let pc_out_gates := (List.range 32).map (fun i =>
    Gate.mkBUF (pc_reg[i]!) (pc_out[i]!)
  )

  -- PC register instance
  let pc_reg_inst : CircuitInstance := {
    moduleName := "Register32"
    instName := "u_pc_reg"
    portMap :=
      (next_pc.enum.map (fun ⟨i, w⟩ => (s!"d_{i}", w))) ++
      [("clock", clock), ("reset", reset)] ++
      (pc_reg.enum.map (fun ⟨i, w⟩ => (s!"q_{i}", w)))
  }

  -- PC incrementer instance (PC + 4)
  let adder_inst : CircuitInstance := {
    moduleName := "KoggeStoneAdder32"
    instName := "u_pc_adder"
    portMap :=
      (pc_reg.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
      (const_4.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w))) ++
      [("cin", const_0)] ++
      (pc_plus_4.enum.map (fun ⟨i, w⟩ => (s!"sum_{i}", w)))
  }

  -- Predict target adder instance (PC + imm)
  let predict_adder_inst : CircuitInstance := {
    moduleName := "KoggeStoneAdder32"
    instName := "u_predict_adder"
    portMap :=
      (pc_reg.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
      (predict_imm.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w))) ++
      [("cin", const_0)] ++
      (predict_target.enum.map (fun ⟨i, w⟩ => (s!"sum_{i}", w)))
  }

  { name := "FetchStage"
    inputs := [clock, reset, stall, branch_valid, const_0, const_1] ++ branch_target ++ instr
    outputs := pc_out ++ [stalled_reg, predicted_taken_wire]
    gates := const_4_gates ++
             btype_gates ++ jal_gates ++
             b_imm_gates ++ j_imm_gates ++ predict_imm_gates ++
             btfn_gates ++
             level0_mux_gates ++ stall_mux_gates ++ branch_mux_gates ++
             stalled_gates ++ pc_out_gates
    instances := [pc_reg_inst, adder_inst, predict_adder_inst]
    signalGroups := [
      { name := "branch_target", width := 32, wires := branch_target },
      { name := "instr", width := 32, wires := instr },
      { name := "pc", width := 32, wires := pc_out },
      { name := "pc_reg", width := 32, wires := pc_reg },
      { name := "next_pc", width := 32, wires := next_pc },
      { name := "const_4", width := 32, wires := const_4 },
      { name := "pc_plus_4", width := 32, wires := pc_plus_4 },
      { name := "predict_imm", width := 32, wires := predict_imm },
      { name := "predict_target", width := 32, wires := predict_target },
      { name := "level0_out", width := 32, wires := level0_out },
      { name := "stall_mux", width := 32, wires := stall_mux_out },
      { name := "b_imm", width := 32, wires := b_imm },
      { name := "j_imm", width := 32, wires := j_imm }
    ]
  }

end Shoumei.RISCV
