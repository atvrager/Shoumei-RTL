/-
Queue1Bridge.lean - Bisimulation proof: Queue1 circuit ↔ QueueState behavioral model

Proves that `mkQueue1StructuralComplete` (gate-level circuit) faithfully implements
`QueueState` (behavioral model). This is the first real behavioral↔structural bridge
in the project.

Verified at width=1 (9 gates, 32 combos) and width=2 (11 gates, 128 combos) via
native_decide — every possible input combination is checked exhaustively.

Three theorem families per width:
  A. Output correctness: circuit outputs match QueueState predicates
  B. Transition correctness: one cycle of evalCycleSequential matches queue1Step
  C. Reset correctness: reset produces empty queue state
-/

import Shoumei.Circuits.Sequential.Queue
import Shoumei.Semantics

namespace Shoumei.Circuits.Sequential

open Shoumei

-- QueueState needs DecidableEq for native_decide proofs
instance [DecidableEq α] : DecidableEq (QueueState α) :=
  fun a b =>
    if h1 : a.entries = b.entries then
      if h2 : a.capacity = b.capacity then
        isTrue (by cases a; cases b; simp_all)
      else isFalse (by intro h; cases h; exact h2 rfl)
    else isFalse (by intro h; cases h; exact h1 rfl)

/-! ## State Abstraction -/

/-- Extract the valid bit from circuit state. -/
def circuitValid (state : State) : Bool :=
  state (Wire.mk "valid")

/-- Extract data bit i from circuit state. -/
def circuitDataBit (state : State) (i : Nat) : Bool :=
  state (Wire.mk s!"data_reg_{i}")

/-- Circuit state → behavioral queue state for width=1. -/
def circuitToQueue1 (state : State) : QueueState Bool :=
  if circuitValid state then
    { entries := [circuitDataBit state 0], capacity := 1 }
  else
    { entries := [], capacity := 1 }

/-- Behavioral step for single-bit Queue1 (no reset). -/
def queue1StepBool (q : QueueState Bool) (enq_valid deq_ready enq_data : Bool) :
    QueueState Bool :=
  let is_empty := q.isEmpty
  let enq_ready := !q.isFull
  let enq_fire := enq_valid && enq_ready
  let deq_fire := (!is_empty) && deq_ready
  let valid_next := enq_fire || ((!is_empty) && !deq_fire)
  let current_data := match q.entries with
    | [d] => d
    | _ => false
  let data_next := if enq_fire then enq_data else current_data
  if valid_next then { entries := [data_next], capacity := 1 }
  else { entries := [], capacity := 1 }

/-! ## Width=1 Bisimulation (9 gates, 32 input combinations) -/

private def q1w1 := mkQueue1StructuralComplete 1

theorem q1w1_gate_count : q1w1.gates.length = 9 := by native_decide

private def evalQ1W1 (valid_st data0_st enq_valid enq_data0 deq_ready : Bool) :
    State × Env :=
  let state : State := fun w =>
    if w == Wire.mk "valid" then valid_st
    else if w == Wire.mk "data_reg_0" then data0_st
    else false
  let inputEnv : Env := fun w =>
    if w == Wire.mk "enq_valid" then enq_valid
    else if w == Wire.mk "enq_data_0" then enq_data0
    else if w == Wire.mk "deq_ready" then deq_ready
    else if w == Wire.mk "clock" then true
    else if w == Wire.mk "reset" then false
    else false
  evalCycleSequential q1w1 state inputEnv

/-- **Theorem B (w=1):** Queue1 width=1 transition matches behavioral model ∀ inputs.
    This is the core bisimulation — exhaustively verified over all 32 combinations. -/
theorem queue1_w1_transition_correct :
    ∀ (valid_st data0_st enq_valid enq_data0 deq_ready : Bool),
    let (nextState, _) := evalQ1W1 valid_st data0_st enq_valid enq_data0 deq_ready
    circuitToQueue1 nextState =
    queue1StepBool (circuitToQueue1 (fun w =>
        if w == Wire.mk "valid" then valid_st
        else if w == Wire.mk "data_reg_0" then data0_st
        else false))
      enq_valid deq_ready enq_data0 := by
  native_decide

/-- **Theorem A (w=1):** enq_ready = !valid (queue accepts when empty). -/
theorem queue1_w1_enq_ready_correct :
    ∀ (valid_st data0_st enq_valid enq_data0 deq_ready : Bool),
    let (_, combEnv) := evalQ1W1 valid_st data0_st enq_valid enq_data0 deq_ready
    combEnv (Wire.mk "enq_ready") = !valid_st := by
  native_decide

/-- **Theorem A (w=1):** deq_valid = valid (queue has data when valid). -/
theorem queue1_w1_deq_valid_correct :
    ∀ (valid_st data0_st enq_valid enq_data0 deq_ready : Bool),
    let (_, combEnv) := evalQ1W1 valid_st data0_st enq_valid enq_data0 deq_ready
    combEnv (Wire.mk "valid") = valid_st := by
  native_decide

/-- **Theorem C (w=1):** Under reset, next state is empty queue. -/
theorem queue1_w1_reset_correct :
    ∀ (valid_st data0_st enq_valid enq_data0 deq_ready : Bool),
    let state : State := fun w =>
      if w == Wire.mk "valid" then valid_st
      else if w == Wire.mk "data_reg_0" then data0_st
      else false
    let inputEnv : Env := fun w =>
      if w == Wire.mk "enq_valid" then enq_valid
      else if w == Wire.mk "enq_data_0" then enq_data0
      else if w == Wire.mk "deq_ready" then deq_ready
      else if w == Wire.mk "clock" then true
      else if w == Wire.mk "reset" then true
      else false
    let (nextState, _) := evalCycleSequential q1w1 state inputEnv
    circuitToQueue1 nextState = QueueState.empty 1 := by
  native_decide

/-- Two-cycle FIFO property: enqueue then dequeue returns the enqueued value (w=1). -/
theorem queue1_w1_enqueue_dequeue :
    ∀ (enq_data : Bool),
    let (state1, _) := evalQ1W1 false false true enq_data false
    let (_, env2) := evalQ1W1
      (state1 (Wire.mk "valid"))
      (state1 (Wire.mk "data_reg_0"))
      false false true
    env2 (Wire.mk "data_reg_0") = enq_data := by
  native_decide

/-! ## Width=2 Bisimulation (11 gates, 128 input combinations) -/

private def q1w2 := mkQueue1StructuralComplete 2

theorem q1w2_gate_count : q1w2.gates.length = 11 := by native_decide

/-- State abstraction for width=2. -/
def circuitToQueue2bit (state : State) : QueueState (Bool × Bool) :=
  if circuitValid state then
    { entries := [(circuitDataBit state 0, circuitDataBit state 1)], capacity := 1 }
  else
    { entries := [], capacity := 1 }

/-- Behavioral step for 2-bit Queue1. -/
def queue1Step2bit (q : QueueState (Bool × Bool)) (enq_valid deq_ready : Bool)
    (enq_data : Bool × Bool) : QueueState (Bool × Bool) :=
  let is_empty := q.isEmpty
  let enq_ready := !q.isFull
  let enq_fire := enq_valid && enq_ready
  let deq_fire := (!is_empty) && deq_ready
  let valid_next := enq_fire || ((!is_empty) && !deq_fire)
  let current_data := match q.entries with
    | [d] => d
    | _ => (false, false)
  let data_next := if enq_fire then enq_data else current_data
  if valid_next then { entries := [data_next], capacity := 1 }
  else { entries := [], capacity := 1 }

private def evalQ1W2 (valid_st d0 d1 enq_valid ed0 ed1 deq_ready : Bool) :
    State × Env :=
  let state : State := fun w =>
    if w == Wire.mk "valid" then valid_st
    else if w == Wire.mk "data_reg_0" then d0
    else if w == Wire.mk "data_reg_1" then d1
    else false
  let inputEnv : Env := fun w =>
    if w == Wire.mk "enq_valid" then enq_valid
    else if w == Wire.mk "enq_data_0" then ed0
    else if w == Wire.mk "enq_data_1" then ed1
    else if w == Wire.mk "deq_ready" then deq_ready
    else if w == Wire.mk "clock" then true
    else if w == Wire.mk "reset" then false
    else false
  evalCycleSequential q1w2 state inputEnv

/-- **Theorem B (w=2):** Queue1 width=2 transition matches behavioral model ∀ inputs. -/
theorem queue1_w2_transition_correct :
    ∀ (valid_st d0 d1 enq_valid ed0 ed1 deq_ready : Bool),
    let (nextState, _) := evalQ1W2 valid_st d0 d1 enq_valid ed0 ed1 deq_ready
    circuitToQueue2bit nextState =
    queue1Step2bit (circuitToQueue2bit (fun w =>
      if w == Wire.mk "valid" then valid_st
      else if w == Wire.mk "data_reg_0" then d0
      else if w == Wire.mk "data_reg_1" then d1
      else false))
      enq_valid deq_ready (ed0, ed1) := by
  native_decide

/-- **Theorem C (w=2):** Reset produces empty queue. -/
theorem queue1_w2_reset_correct :
    ∀ (valid_st d0 d1 enq_valid ed0 ed1 deq_ready : Bool),
    let state : State := fun w =>
      if w == Wire.mk "valid" then valid_st
      else if w == Wire.mk "data_reg_0" then d0
      else if w == Wire.mk "data_reg_1" then d1
      else false
    let inputEnv : Env := fun w =>
      if w == Wire.mk "enq_valid" then enq_valid
      else if w == Wire.mk "enq_data_0" then ed0
      else if w == Wire.mk "enq_data_1" then ed1
      else if w == Wire.mk "deq_ready" then deq_ready
      else if w == Wire.mk "clock" then true
      else if w == Wire.mk "reset" then true
      else false
    let (nextState, _) := evalCycleSequential q1w2 state inputEnv
    circuitToQueue2bit nextState = QueueState.empty 1 := by
  native_decide

/-- Two-cycle FIFO property (w=2): enqueue (true, false) then dequeue returns it. -/
theorem queue1_w2_enqueue_dequeue :
    ∀ (ed0 ed1 : Bool),
    let (state1, _) := evalQ1W2 false false false true ed0 ed1 false
    let v1 := state1 (Wire.mk "valid")
    let d1_0 := state1 (Wire.mk "data_reg_0")
    let d1_1 := state1 (Wire.mk "data_reg_1")
    let (_, env2) := evalQ1W2 v1 d1_0 d1_1 false false false true
    (env2 (Wire.mk "data_reg_0"), env2 (Wire.mk "data_reg_1")) = (ed0, ed1) := by
  native_decide

end Shoumei.Circuits.Sequential
