/-
Fetch Stage - Behavioral Model

The fetch stage retrieves instructions from instruction memory and manages
the program counter (PC). It handles three control flow scenarios:
1. Branch misprediction redirect (highest priority)
2. Pipeline stall (freeze PC)
3. Sequential execution (PC += 4)

Phase 8 scope: Behavioral model only. Structural circuit TBD.
-/

import Shoumei.RISCV.Config
import Shoumei.DSL
import Shoumei.Circuits.Sequential.Register
import Shoumei.Circuits.Combinational.RippleCarryAdder

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
Build Fetch Stage structural circuit.

Architecture:
- PC storage: Register32 instance (32-bit register with clock/reset)
- PC increment: RippleCarryAdder32 instance (PC + 4)
- Next PC mux: Two-level mux tree for priority logic
  - Level 1: stall ? current_pc : pc_plus_4
  - Level 2: branch_valid ? branch_target : level1_out
- Stalled tracking: 1-bit DFF with control logic

Inputs:
- clock, reset: Control signals
- stall: Pipeline stall signal
- branch_valid: Branch redirect valid
- branch_target[31:0]: Branch redirect target
- const_0, const_1: Constant values for adder

Outputs:
- pc[31:0]: Current program counter
- stalled: Fetch stalled status

Instances:
- Register32 (PC storage)
- RippleCarryAdder32 (PC + 4)

Gates: 227 total
- Constant generation: 32 BUF gates
- Stall mux: 96 gates (32 × 3-gate MUX)
- Branch mux: 96 gates (32 × 3-gate MUX)
- Stalled logic: 3 gates (NOT, AND, DFF)
-/
def mkFetchStage : Circuit :=
  -- Input wires
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let stall := Wire.mk "stall"
  let branch_valid := Wire.mk "branch_valid"
  let branch_target := makeIndexedWires "branch_target" 32
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

  -- Internal wires: Stall mux output
  let stall_mux_out := makeIndexedWires "stall_mux" 32

  -- Stall mux gates: stall_mux_out = stall ? pc_reg : pc_plus_4
  let stall_mux_gates := (List.range 32).map (fun i =>
    Gate.mkMUX (pc_plus_4[i]!) (pc_reg[i]!) stall (stall_mux_out[i]!)
  )

  -- Branch mux gates: next_pc = branch_valid ? branch_target : stall_mux_out
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

  -- PC incrementer instance
  let adder_inst : CircuitInstance := {
    moduleName := "RippleCarryAdder32"
    instName := "u_pc_adder"
    portMap :=
      (pc_reg.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
      (const_4.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w))) ++
      [("cin", const_0)] ++
      (pc_plus_4.enum.map (fun ⟨i, w⟩ => (s!"sum_{i}", w)))
  }

  { name := "FetchStage"
    inputs := [clock, reset, stall, branch_valid, const_0, const_1] ++ branch_target
    outputs := pc_out ++ [stalled_reg]
    gates := const_4_gates ++ stall_mux_gates ++ branch_mux_gates ++ stalled_gates ++ pc_out_gates
    instances := [pc_reg_inst, adder_inst]
    -- V2 codegen annotations
    signalGroups := [
      { name := "branch_target", width := 32, wires := branch_target },
      { name := "pc", width := 32, wires := pc_out },
      { name := "pc_reg", width := 32, wires := pc_reg },
      { name := "next_pc", width := 32, wires := next_pc },
      { name := "const_4", width := 32, wires := const_4 },
      { name := "pc_plus_4", width := 32, wires := pc_plus_4 },
      { name := "stall_mux", width := 32, wires := stall_mux_out }
    ]
  }

end Shoumei.RISCV
