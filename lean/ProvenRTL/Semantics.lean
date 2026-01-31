/-
Semantics.lean - Operational Semantics for Hardware DSL

Defines how circuits are evaluated:
- evalGate: Evaluate a single gate
- evalCircuit: Evaluate an entire circuit given input values

The semantics is pure combinational logic - no clocking or state.
-/

import ProvenRTL.DSL

namespace ProvenRTL

-- Environment: maps wires to boolean values
abbrev Env := Wire → Bool

-- Evaluate a single gate given an environment
def evalGate (g : Gate) (env : Env) : Bool :=
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

-- Helper: update environment with a new wire-value binding
def updateEnv (env : Env) (w : Wire) (v : Bool) : Env :=
  fun w' => if w' == w then v else env w'

-- Evaluate an entire circuit
-- Given input values (as an environment), compute output values
def evalCircuit (c : Circuit) (inputEnv : Env) : Env :=
  -- Strategy:
  -- 1. Start with inputEnv for circuit inputs
  -- 2. For each gate in topological order:
  --    - Evaluate gate using current environment
  --    - Update environment with gate output
  -- 3. Return final environment
  --
  -- Note: Assumes gates are in topological order (which they are for our full adder)
  c.gates.foldl (fun env gate =>
    let result := evalGate gate env
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

end ProvenRTL
