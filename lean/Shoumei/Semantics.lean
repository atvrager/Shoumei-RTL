/-
Semantics.lean - Operational Semantics for Hardware DSL

Defines how circuits are evaluated:
- Combinational evaluation: evalGate, evalCircuit
- Sequential evaluation: evalDFF, evalCycleSequential, evalSequential

Supports both combinational (stateless) and sequential (stateful) circuits.
Sequential circuits are evaluated cycle-by-cycle with explicit state management.
-/

import Shoumei.DSL

namespace Shoumei

-- Environment: maps wires to boolean values (for inputs and combinational signals)
abbrev Env := Wire → Bool

-- State: maps wires to boolean values (for flip-flop outputs)
-- This represents the current state of all sequential elements
abbrev State := Wire → Bool

-- Evaluate a combinational gate given an environment
-- For sequential gates (DFF), use evalDFF instead
def evalCombGate (g : Gate) (env : Env) : Bool :=
  match g.gateType with
  | GateType.AND =>
      match g.inputs with
      | [i0, i1] => env i0 && env i1
      | _ => false  -- Shouldn't happen for well-formed circuits
  | GateType.OR =>
      match g.inputs with
      | [i0, i1] => env i0 || env i1
      | _ => false
  | GateType.NOT =>
      match g.inputs with
      | [i0] => !(env i0)
      | _ => false
  | GateType.XOR =>
      match g.inputs with
      | [i0, i1] => xor (env i0) (env i1)
      | _ => false
  | GateType.BUF =>
      -- Buffer: pass-through (out = in)
      match g.inputs with
      | [i0] => env i0
      | _ => false
  | GateType.MUX =>
      -- Inputs: [in0, in1, sel], semantics: sel ? in1 : in0
      match g.inputs with
      | [in0, in1, sel] => if env sel then env in1 else env in0
      | _ => false
  | GateType.DFF =>
      false  -- DFF should not be evaluated as combinational

-- Evaluate a D Flip-Flop to get next state value
-- Inputs: [d, clk, reset], output: q
-- Semantics: On clock edge, if reset then q_next = 0 else q_next = d
-- Note: We model clock edge implicitly - each cycle represents one rising edge
def evalDFF (g : Gate) (env : Env) : Bool :=
  match g.gateType with
  | GateType.DFF =>
      match g.inputs with
      | [d, _clk, reset] =>
          -- On rising edge: if reset high, output is 0; otherwise capture d
          if env reset then false else env d
      | _ => false  -- Malformed DFF
  | _ => false  -- Not a DFF


-- Helper: update environment with a new wire-value binding
def updateEnv (env : Env) (w : Wire) (v : Bool) : Env :=
  fun w' => if w' == w then v else env w'

-- Evaluate a purely combinational circuit
-- Given input values (as an environment), compute output values
-- Note: For sequential circuits, use evalCycleSequential or evalSequential instead
def evalCircuit (c : Circuit) (inputEnv : Env) : Env :=
  -- Strategy:
  -- 1. Start with inputEnv for circuit inputs
  -- 2. For each gate in topological order:
  --    - Evaluate gate using current environment
  --    - Update environment with gate output
  -- 3. Return final environment
  --
  -- Note: Assumes gates are in topological order and circuit is purely combinational
  c.gates.foldl (fun env gate =>
    let result := evalCombGate gate env
    updateEnv env gate.output result
  ) inputEnv

-- Helper: evaluate circuit and extract specific output wire
def evalCircuitOutput (c : Circuit) (inputEnv : Env) (out : Wire) : Bool :=
  evalCircuit c inputEnv out

-- Helper: create environment from list of wire-value pairs
def mkEnv (bindings : List (Wire × Bool)) : Env :=
  fun w =>
    match bindings.find? (fun p => p.1 == w) with
    | some (_, v) => v
    | none => false  -- Default: unbound wires are false

-- Helper: merge state into environment (flip-flop outputs become available signals)
def mergeStateIntoEnv (state : State) (env : Env) (dffOutputs : List Wire) : Env :=
  fun w =>
    if dffOutputs.contains w then
      state w  -- Use state value for DFF outputs
    else
      env w    -- Use environment value for other wires

-- Helper: get all DFF output wires from a circuit
def getDFFOutputs (c : Circuit) : List Wire :=
  c.gates.filter (fun g => g.gateType == GateType.DFF) |>.map (fun g => g.output)

-- Helper: update state with new values from DFF evaluation
def updateState (state : State) (updates : List (Wire × Bool)) : State :=
  fun w =>
    match updates.find? (fun p => p.1 == w) with
    | some (_, v) => v
    | none => state w

-- Evaluate one clock cycle of a sequential circuit
-- Returns: (next state, output environment)
def evalCycleSequential (c : Circuit) (state : State) (inputEnv : Env) : State × Env :=
  -- Step 1: Merge current state (DFF outputs) into environment
  let dffOutputs := getDFFOutputs c
  let envWithState := mergeStateIntoEnv state inputEnv dffOutputs

  -- Step 2: Evaluate all combinational gates to build full environment
  let combEnv := c.gates.foldl (fun env gate =>
    if gate.gateType.isCombinational then
      let result := evalCombGate gate env
      updateEnv env gate.output result
    else
      env  -- Skip sequential gates in combinational phase
  ) envWithState

  -- Step 3: Evaluate all DFFs to compute next state
  let nextStateUpdates := c.gates.filterMap (fun gate =>
    if gate.gateType == GateType.DFF then
      let nextVal := evalDFF gate combEnv
      some (gate.output, nextVal)
    else
      none
  )
  let nextState := updateState state nextStateUpdates

  -- Return next state and final environment (for reading outputs)
  (nextState, combEnv)

-- Evaluate multiple clock cycles
-- Takes initial state, list of input environments (one per cycle)
-- Returns list of (state, output env) pairs (one per cycle)
def evalSequential (c : Circuit) (initState : State) (inputs : List Env) : List (State × Env) :=
  inputs.foldl (fun acc inputEnv =>
    let (currentState, _) := acc.getLast?.getD (initState, mkEnv [])
    let (nextState, outEnv) := evalCycleSequential c currentState inputEnv
    acc ++ [(nextState, outEnv)]
  ) []

-- Helper: create initial state (all flip-flops start at false)
def initState : State :=
  fun _ => false

end Shoumei
