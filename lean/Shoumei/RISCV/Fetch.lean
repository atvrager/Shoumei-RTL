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

end Shoumei.RISCV
