/-
DFFProofs.lean - Formal Proofs for D Flip-Flop Circuit

Proves correctness properties of the D flip-flop:
1. Reset behavior - when reset is high, output becomes 0
2. Data capture - when reset is low, output captures input d
3. State persistence - output holds value across cycles
4. Initial state - flip-flop starts at 0
-/

import Shoumei.Circuits.Sequential.DFF
import Shoumei.Semantics

namespace Shoumei.Circuits.Sequential

open Shoumei

-- Helper: Create input environment for one clock cycle
def makeDFFEnv (d_val reset_val : Bool) : Env :=
  mkEnv [
    (Wire.mk "d", d_val),
    (Wire.mk "clock", true),  -- Clock value doesn't matter for logic (edge-triggered)
    (Wire.mk "reset", reset_val)
  ]

-- Helper: Extract q output from state or environment
def getQOutput (env : Env) : Bool :=
  env (Wire.mk "q")

-- Theorem: Reset behavior
-- When reset is high, the next state of q is always 0, regardless of d
theorem dff_reset (d_val : Bool) :
  let env := makeDFFEnv d_val true  -- reset = true
  let (nextState, _) := evalCycleSequential mkDFlipFlop initState env
  nextState (Wire.mk "q") = false := by
  cases d_val <;> native_decide

-- Theorem: Data capture when not in reset
-- When reset is low, the next state of q equals the input d
theorem dff_capture (d_val : Bool) :
  let env := makeDFFEnv d_val false  -- reset = false
  let (nextState, _) := evalCycleSequential mkDFlipFlop initState env
  nextState (Wire.mk "q") = d_val := by
  cases d_val <;> native_decide

-- Theorem: Initial state
-- The flip-flop starts at 0
theorem dff_initialState :
  initState (Wire.mk "q") = false := by
  native_decide

-- Theorem: State persistence across cycles
-- If we set d=true without reset, then in next cycle q should be true
theorem dff_statePersistence :
  -- Cycle 1: Load d=true, reset=false
  let env1 := makeDFFEnv true false
  let (state1, _) := evalCycleSequential mkDFlipFlop initState env1
  -- Verify state1 has q=true
  state1 (Wire.mk "q") = true ∧
  -- Cycle 2: Keep d=false, reset=false (q should stay true from previous cycle)
  let env2 := makeDFFEnv false false
  let (state2, out2) := evalCycleSequential mkDFlipFlop state1 env2
  -- At start of cycle 2, q output should be true (from state1)
  getQOutput out2 = true ∧
  -- After cycle 2, next state should be false (captured new d=false)
  state2 (Wire.mk "q") = false := by
  native_decide

-- Theorem: Reset overrides data
-- Even if we had q=true from previous cycle, reset brings it to 0
theorem dff_resetOverride :
  -- Start with a state where q=true
  let stateWithQHigh : State := fun w => if w == Wire.mk "q" then true else false
  -- Apply reset
  let env := makeDFFEnv true true  -- d=true, reset=true
  let (nextState, _) := evalCycleSequential mkDFlipFlop stateWithQHigh env
  nextState (Wire.mk "q") = false := by
  native_decide

-- Theorem: Complete behavioral specification
-- Covers all combinations of d and reset
theorem dff_behavioral (d_val reset_val : Bool) :
  let env := makeDFFEnv d_val reset_val
  let (nextState, _) := evalCycleSequential mkDFlipFlop initState env
  let q_next := nextState (Wire.mk "q")
  -- If reset, q_next = 0; otherwise q_next = d_val
  (reset_val = true → q_next = false) ∧
  (reset_val = false → q_next = d_val) := by
  cases d_val <;> cases reset_val <;> native_decide

-- Theorem: Multi-cycle sequence verification
-- Verify a specific sequence: reset, load 1, load 0, load 1
theorem dff_sequence :
  let envs := [
    makeDFFEnv false true,   -- Cycle 0: reset
    makeDFFEnv true false,   -- Cycle 1: load d=1
    makeDFFEnv false false,  -- Cycle 2: load d=0
    makeDFFEnv true false    -- Cycle 3: load d=1
  ]
  let results := evalSequential mkDFlipFlop initState envs
  -- After cycle 0 (reset): q=0
  (results[0]?.map (·.1 (Wire.mk "q")) = some false) ∧
  -- After cycle 1 (load 1): q=1
  (results[1]?.map (·.1 (Wire.mk "q")) = some true) ∧
  -- After cycle 2 (load 0): q=0
  (results[2]?.map (·.1 (Wire.mk "q")) = some false) ∧
  -- After cycle 3 (load 1): q=1
  (results[3]?.map (·.1 (Wire.mk "q")) = some true) := by
  native_decide

end Shoumei.Circuits.Sequential
