/-
Temporal/Trace.lean - Trace Semantics and Temporal Logic for Shoumei Hardware

Defines:
1. Discrete-time execution traces (Nat → State × Env)
2. Validity of an execution trace with respect to a circuit's operational semantics
3. Core temporal properties: invariants (Always), step transitions (Next),
   implication (|-> and |=>), and protocol invariants (Decoupled handshake stability)
4. Semantic truth of temporal properties over traces
-/

import Shoumei.DSL
import Shoumei.Semantics

namespace Shoumei.Temporal

open Shoumei

/-- A single step in circuit simulation: the register state at the beginning
    of the cycle, and the combinational environment (inputs + gate outputs) during that cycle. -/
structure Step where
  state : State
  env   : Env

/-- An execution trace is a discrete-time sequence of simulation steps. -/
def Trace := Nat → Step

namespace Trace

/-- Initial state of a trace. -/
def initState (tr : Trace) : State := (tr 0).state

/-- State at cycle t. -/
def stateAt (tr : Trace) (t : Nat) : State := (tr t).state

/-- Combinational environment (inputs + outputs + internal wires) at cycle t. -/
def envAt (tr : Trace) (t : Nat) : Env := (tr t).env

/-- Signal value on wire `w` at cycle `t`. -/
def wireAt (tr : Trace) (w : Wire) (t : Nat) : Bool := (tr t).env w

/-- Multi-bit bus values on wires `ws` at cycle `t`. -/
def busAt (tr : Trace) (ws : List Wire) (t : Nat) : List Bool :=
  ws.map (fun w => (tr t).env w)

/-- A trace `tr` is a faithful execution of sequential circuit `c` starting from `s0`
    under external input sequence `inputs : Nat → Env`.

    Every step satisfies the operational semantics from `Semantics.lean`:
    - At t = 0, state is `s0`.
    - For all t, the environment is the combinational fixed-point given current state and inputs.
    - The state at t + 1 is the next state produced by clocking flip-flops on the rising edge. -/
def IsExecutionOf (c : Circuit) (s0 : State) (inputs : Nat → Env) (tr : Trace) : Prop :=
  tr.initState = s0 ∧
  ∀ t : Nat,
    let step := evalCycleSequential c (tr.stateAt t) (inputs t)
    tr.envAt t = step.2 ∧ tr.stateAt (t + 1) = step.1

/-- Closed-form recursive state computation at cycle t. -/
def evalStateAt (c : Circuit) (s0 : State) (inputs : Nat → Env) : Nat → State
  | 0 => s0
  | t + 1 => (evalCycleSequential c (evalStateAt c s0 inputs t) (inputs t)).1

/-- Construct the deterministic execution trace of circuit `c` from `s0` and `inputs`. -/
def runTrace (c : Circuit) (s0 : State) (inputs : Nat → Env) : Trace :=
  fun t =>
    let st := evalStateAt c s0 inputs t
    let env := (evalCycleSequential c st (inputs t)).2
    ⟨st, env⟩

/-- The generated `runTrace` is an execution of circuit `c`. -/
theorem runTrace_isExecution (c : Circuit) (s0 : State) (inputs : Nat → Env) :
    IsExecutionOf c s0 inputs (runTrace c s0 inputs) := by
  constructor
  · rfl
  · intro t
    exact ⟨rfl, rfl⟩

end Trace

/-! ## Temporal Assertions and Properties

These representations serve a dual purpose:
1. They are evaluated in Lean as mathematical propositions over `Trace`.
2. They are emitted by the SystemVerilog generator as synthesizable SVA assertions.
-/

/-- Atomic conditions checked on a single cycle step. -/
inductive Atom where
  | WireHigh (w : Wire)
  | WireLow (w : Wire)
  | BusEq (ws : List Wire) (vals : List Bool)
  deriving Repr, BEq, Inhabited

/-- Evaluate an atomic condition on a step environment. -/
def evalAtom (atom : Atom) (env : Env) : Bool :=
  match atom with
  | .WireHigh w => env w
  | .WireLow w => !(env w)
  | .BusEq ws vals => (ws.map env) == vals

/-- Temporal properties describing circuit behavior over time. -/
inductive TemporalProp where
  /-- Invariant: atom holds in every cycle (SVA: `assert property (p)`) -/
  | Always (p : Atom)
  /-- Overlapping implication: if ante holds at cycle t, conseq holds at cycle t (SVA: `ante |-> conseq`) -/
  | ImpliesOverlap (ante conseq : Atom)
  /-- Non-overlapping implication: if ante holds at cycle t, conseq holds at cycle t + 1 (SVA: `ante |=> conseq`) -/
  | ImpliesNext (ante conseq : Atom)
  /-- Decoupled Handshake Protocol Stability:
      When valid is asserted and ready is deasserted at cycle t,
      valid must remain asserted at cycle t + 1, and all data bits must remain stable ($stable).
      (SVA: `(valid && !ready) |=> (valid && $stable(data))`) -/
  | HandshakeStable (valid ready : Wire) (data : List Wire)
  /-- FIFO Capacity Invariant:
      When queue is full (count equals capacity), enqueue ready must be low. -/
  | FullNotReady (countWires : List Wire) (cap : Nat) (enqReady : Wire)
  /-- FIFO Empty Invariant:
      When queue is empty (count equals 0), dequeue valid must be low. -/
  | EmptyNotValid (countWires : List Wire) (deqValid : Wire)
  /-- Register Reset Invariant:
      When reset is asserted at cycle t, all qWires bits are low at cycle t + 1. -/
  | RegisterResetZero (resetWire : Wire) (qWires : List Wire)
  /-- Register Data Capture Invariant:
      When reset is not asserted at cycle t, qWires at cycle t + 1 equals dWires at cycle t. -/
  | RegisterDataCapture (resetWire : Wire) (dWires qWires : List Wire)
  /-- Register Enable Hold Invariant:
      When reset is low and enable is low at cycle t, qWires at cycle t + 1 retains qWires at cycle t. -/
  | RegisterEnableHolds (resetWire : Wire) (enWire : Wire) (qWires : List Wire)
  /-- Register Enable Capture Invariant:
      When reset is low and enable is high at cycle t, qWires at cycle t + 1 latches dWires at cycle t. -/
  | RegisterEnableCapture (resetWire : Wire) (enWire : Wire) (dWires qWires : List Wire)
  /-- Multi-cycle Pipeline Latency Invariant (Z^-k):
      When reset remains low for k consecutive cycles from cycle t, qWires at cycle t + k equals dWires at cycle t. -/
  | RegisterLatencyCapture (resetWire : Wire) (dWires qWires : List Wire) (cycles : Nat)
  /-- Decoupled Transaction Equivalence:
      When both channels handshake simultaneously at cycle t, output payload data matches. -/
  | DecoupledEquiv (valA rdyA : Wire) (dataA : List Wire) (valB rdyB : Wire) (dataB : List Wire)
  deriving Repr, Inhabited

/-- Semantic evaluation: whether a `Trace` satisfies a `TemporalProp`. -/
def satisfiesTrace (tr : Trace) : TemporalProp → Prop
  | .Always p =>
      ∀ t : Nat, evalAtom p (tr.envAt t) = true
  | .ImpliesOverlap ante conseq =>
      ∀ t : Nat, evalAtom ante (tr.envAt t) = true → evalAtom conseq (tr.envAt t) = true
  | .ImpliesNext ante conseq =>
      ∀ t : Nat, evalAtom ante (tr.envAt t) = true → evalAtom conseq (tr.envAt (t + 1)) = true
  | .HandshakeStable valid ready data =>
      ∀ t : Nat,
        (tr.wireAt valid t = true ∧ tr.wireAt ready t = false) →
          (tr.wireAt valid (t + 1) = true ∧ tr.busAt data (t + 1) = tr.busAt data t)
  | .FullNotReady countWires cap enqReady =>
      ∀ t : Nat,
        -- When decoded count is at capacity, enqReady is false
        (tr.wireAt enqReady t = true → ¬(tr.busAt countWires t = (List.range countWires.length).map (fun i => (cap >>> i) % 2 == 1)))
  | .EmptyNotValid countWires deqValid =>
      ∀ t : Nat,
        -- When count is all zeroes, deqValid is false
        (tr.busAt countWires t = countWires.map (fun _ => false)) → tr.wireAt deqValid t = false
  | .RegisterResetZero resetWire qWires =>
      ∀ t : Nat,
        tr.wireAt resetWire t = true →
          tr.busAt qWires (t + 1) = qWires.map (fun _ => false)
  | .RegisterDataCapture resetWire dWires qWires =>
      ∀ t : Nat,
        tr.wireAt resetWire t = false →
          tr.busAt qWires (t + 1) = tr.busAt dWires t
  | .RegisterEnableHolds resetWire enWire qWires =>
      ∀ t : Nat,
        tr.wireAt resetWire t = false →
        tr.wireAt enWire t = false →
          tr.busAt qWires (t + 1) = tr.busAt qWires t
  | .RegisterEnableCapture resetWire enWire dWires qWires =>
      ∀ t : Nat,
        tr.wireAt resetWire t = false →
        tr.wireAt enWire t = true →
          tr.busAt qWires (t + 1) = tr.busAt dWires t
  | .RegisterLatencyCapture resetWire dWires qWires cycles =>
      ∀ t : Nat,
        (∀ i, i < cycles → tr.wireAt resetWire (t + i) = false) →
          tr.busAt qWires (t + cycles) = tr.busAt dWires t
  | .DecoupledEquiv valA rdyA dataA valB rdyB dataB =>
      ∀ t : Nat,
        (tr.wireAt valA t = true ∧ tr.wireAt rdyA t = true ∧
         tr.wireAt valB t = true ∧ tr.wireAt rdyB t = true) →
          tr.busAt dataA t = tr.busAt dataB t

/-- Circuit satisfies a temporal property under valid reset initialization. -/
def CircuitSatisfies (c : Circuit) (s0 : State) (prop : TemporalProp) : Prop :=
  ∀ (inputs : Nat → Env) (tr : Trace),
    Trace.IsExecutionOf c s0 inputs tr →
    satisfiesTrace tr prop

end Shoumei.Temporal
