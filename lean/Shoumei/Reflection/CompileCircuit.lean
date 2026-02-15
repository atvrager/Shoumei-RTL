/-
Reflection/CompileCircuit.lean - Circuit compilation with correctness proof

`compileCircuit` folds `compileGate` over all gates, mirroring `evalCircuit`.
`compileCircuitHier` extends this to handle hierarchical circuits with instances.
-/

import Shoumei.Reflection.CompileGate

namespace Shoumei.Reflection

open Shoumei

/-- Compile a circuit by folding compileGate over all gates. -/
def compileCircuit (c : Circuit) (initMap : WireMap) : WireMap :=
  c.gates.foldl compileGate initMap

/-- Compile a gate list (for induction). -/
def compileGates (gates : List Gate) (m : WireMap) : WireMap :=
  gates.foldl compileGate m

/-- evalCircuit expressed as a foldl over gates (for induction). -/
def evalGates (gates : List Gate) (env : Env) : Env :=
  gates.foldl (fun env gate => updateEnv env gate.output (evalGate gate env)) env

theorem evalGates_eq_evalCircuit (c : Circuit) (env : Env) :
    evalGates c.gates env = evalCircuit c env := by
  simp [evalGates, evalCircuit]

/-- Core correctness: compileGates agrees with evalGates. -/
theorem compileGates_correct (gates : List Gate) (m : WireMap) (env : Env)
    (h : ∀ w, m.lookup w = env w) :
    ∀ w, (compileGates gates m).lookup w = evalGates gates env w := by
  induction gates generalizing m env with
  | nil => exact h
  | cons g rest ih =>
    simp [compileGates, evalGates, List.foldl]
    apply ih
    exact compileGate_correct g m env h

/-- Main theorem: compileCircuit agrees with evalCircuit. -/
theorem compileCircuit_correct (c : Circuit) (initMap : WireMap) (inputEnv : Env)
    (h : ∀ w, initMap.lookup w = inputEnv w) :
    ∀ w, (compileCircuit c initMap).lookup w = evalCircuit c inputEnv w := by
  intro w
  simp [compileCircuit]
  rw [← evalGates_eq_evalCircuit]
  exact compileGates_correct c.gates initMap inputEnv h w

/-! ## Hierarchical Circuit Compilation

For circuits with `CircuitInstance`s, we compile in two phases:
1. Process instances: for each instance, apply its submodule specification
   to compute output wires from input wires, then add results to the WireMap
2. Process gates: fold `compileGate` over the gate list as before

Submodule specifications are provided as a lookup function, enabling
compositional verification: prove each submodule separately, then
compose at the top level.
-/

/-- A submodule specification: given input wire values, produce output wire values. -/
structure SubmoduleSpec where
  /-- Module name this spec applies to. -/
  moduleName : String
  /-- Input port names (in the submodule's namespace). -/
  inputPorts : List String
  /-- Output port names (in the submodule's namespace). -/
  outputPorts : List String
  /-- The specification function: given input values, produce output values.
      Input order matches `inputPorts`, output order matches `outputPorts`. -/
  eval : List Bool → List Bool

/-- Apply a submodule spec to an instance, reading inputs from and writing outputs to a WireMap. -/
def applyInstance (spec : SubmoduleSpec) (inst : CircuitInstance) (m : WireMap) : WireMap :=
  -- Read input values from the WireMap using the port map
  let inputVals := spec.inputPorts.map fun portName =>
    match inst.portMap.find? (fun p => p.1 == portName) with
    | some (_, wire) => m.lookup wire
    | none => false
  -- Compute output values
  let outputVals := spec.eval inputVals
  -- Write output values to the WireMap
  let outputs := spec.outputPorts.zip outputVals
  outputs.foldl (fun m (portName, val) =>
    match inst.portMap.find? (fun p => p.1 == portName) with
    | some (_, wire) => m.insert wire val
    | none => m
  ) m

/-- Compile a hierarchical circuit: first apply instance specs, then compile gates. -/
def compileCircuitHier (c : Circuit) (specs : List SubmoduleSpec) (initMap : WireMap) : WireMap :=
  -- Phase 1: Apply submodule specs for each instance
  let afterInstances := c.instances.foldl (fun m inst =>
    match specs.find? (fun s => s.moduleName == inst.moduleName) with
    | some spec => applyInstance spec inst m
    | none => m  -- Unknown module: skip (wires stay at default false)
  ) initMap
  -- Phase 2: Compile top-level gates
  compileCircuit c afterInstances

/-! ## Circuit Flattening

Recursively inline all `CircuitInstance`s to produce a flat gate-only circuit.
This allows `compileCircuit` (which only processes gates) to evaluate
hierarchical circuits correctly.
-/

/-- Recursively flatten a hierarchical circuit by inlining all instances.
    The registry maps module names to their `Circuit` definitions.
    Gate ordering: gates whose outputs feed instance inputs come first,
    then inlined instance gates, then remaining top-level gates. -/
partial def flattenAll (registry : List (String × Circuit)) (c : Circuit) : Circuit :=
  -- Collect all instance input wires (parent-side)
  let instInputWires : List Wire := c.instances.flatMap fun inst =>
    match registry.find? (fun p => p.1 == inst.moduleName) with
    | some (_, sub) =>
      let inputPortNames := sub.inputs.map (fun w => w.name.replace "_" "")
      inst.portMap.filterMap fun (portKey, parentWire) =>
        if inputPortNames.any (· == portKey) then some parentWire else none
    | none => []
  -- Split gates: those feeding instances (pre) vs those consuming from instances (post)
  let (preGates, postGates) := c.gates.partition fun g =>
    instInputWires.any (· == g.output)
  let inlinedGates := c.instances.enum.flatMap fun (idx, inst) =>
    match registry.find? (fun p => p.1 == inst.moduleName) with
    | some (_, subCircuit) =>
      let flat := flattenAll registry subCircuit
      let wireRemap : Wire → Wire := fun w =>
        let portKey := w.name.replace "_" ""
        match inst.portMap.find? (fun p => p.1 == portKey) with
        | some (_, parentWire) => parentWire
        | none => Wire.mk s!"_i{idx}_{w.name}"
      Circuit.inline flat wireRemap
    | none => []
  { c with gates := preGates ++ inlinedGates ++ postGates, instances := [] }

/-- Non-partial version of `flattenAll` with explicit recursion depth bound.
    Returns the circuit unchanged if fuel runs out. -/
def flattenAllFuel (registry : List (String × Circuit)) (c : Circuit) (fuel : Nat) : Circuit :=
  match fuel with
  | 0 => c
  | fuel + 1 =>
    let instInputWires : List Wire := c.instances.flatMap fun inst =>
      match registry.find? (fun p => p.1 == inst.moduleName) with
      | some (_, sub) =>
        let inputPortNames := sub.inputs.map (fun w => w.name.replace "_" "")
        inst.portMap.filterMap fun (portKey, parentWire) =>
          if inputPortNames.any (· == portKey) then some parentWire else none
      | none => []
    let (preGates, postGates) := c.gates.partition fun g =>
      instInputWires.any (· == g.output)
    let inlinedGates := c.instances.enum.flatMap fun (idx, inst) =>
      match registry.find? (fun p => p.1 == inst.moduleName) with
      | some (_, subCircuit) =>
        let flat := flattenAllFuel registry subCircuit fuel
        let wireRemap : Wire → Wire := fun w =>
          let portKey := w.name.replace "_" ""
          match inst.portMap.find? (fun p => p.1 == portKey) with
          | some (_, parentWire) => parentWire
          | none => Wire.mk s!"_i{idx}_{w.name}"
        Circuit.inline flat wireRemap
      | none => []
    { c with gates := preGates ++ inlinedGates ++ postGates, instances := [] }

end Shoumei.Reflection
