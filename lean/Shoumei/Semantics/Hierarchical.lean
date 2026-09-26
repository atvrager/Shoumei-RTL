/-
Semantics/Hierarchical.lean - Hierarchical Circuit Operational Semantics

Extends flat circuit semantics to hierarchical circuits containing CircuitInstances:
- `evalHier`: Combinational evaluation with recursive submodule instance elaboration
- `stepHier`: Sequential evaluation threading scoped instance states
  (`hierStepFold` is the shared single-instance fold step, parameterized by
  the sub-evaluation function so proofs can substitute specs for recursion)
- Soundness theorems:
  - `evalHier_no_instances`: Flat circuits match `evalCircuit`
  - `stepHier_no_instances`: Flat sequential circuits match `evalCycleSequential`
  - `runHierTrace_isExecution`: Trace construction satisfies hierarchical execution
-/

import Shoumei.DSL
import Shoumei.DSL.PortResolve
import Shoumei.Semantics
import Shoumei.Temporal.Trace

namespace Shoumei.Semantics.Hierarchical

open Shoumei
open Shoumei.DSL.PortResolve
open Shoumei.Temporal

/-- Submodule wire name scoped under an instance name to prevent state aliasing. -/
def instScope (instName : String) (w : Wire) : Wire :=
  Wire.mk s!"{instName}/{w.name}"

/-- Evaluate a list of combinational gates, skipping sequential DFF gates. -/
def evalCombGates (gates : List Gate) (env : Env) : Env :=
  gates.foldl (fun env gate =>
    if gate.gateType.isCombinational then
      updateEnv env gate.output (evalGate gate env)
    else
      env
  ) env

@[simp] theorem evalCombGates_nil (env : Env) : evalCombGates [] env = env := rfl

/-- Collect all parent wires that drive input ports of any instance in `c`. -/
def instanceInputWires (reg : ModuleRegistry) (c : Circuit) : List Wire :=
  c.instances.flatMap fun inst =>
    match reg.find? (fun p => p.1 == inst.moduleName) with
    | some (_, sub) => sub.inputs.filterMap (resolvePort sub inst)
    | none => []

/-- Compute the backwards combinational fan-in cone of `seed` wires across
    `gates` via a right-to-left pass. For topologically ordered `gates`, a
    single reverse pass collects every transitive upstream wire feeding `seed`. -/
def faninConeWires (gates : List Gate) (seed : List Wire) : List Wire :=
  gates.foldr (fun g needed =>
    if needed.contains g.output then
      g.inputs ++ needed
    else
      needed
  ) seed

/-- Top-level gates in the transitive fan-in cone of any instance input wire. -/
def preGates (reg : ModuleRegistry) (c : Circuit) : List Gate :=
  let preWires := faninConeWires c.gates (instanceInputWires reg c)
  c.gates.filter fun g => preWires.contains g.output

/-- Top-level gates outside the transitive fan-in cone of instance inputs. -/
def postGates (reg : ModuleRegistry) (c : Circuit) : List Gate :=
  let preWires := faninConeWires c.gates (instanceInputWires reg c)
  c.gates.filter fun g => !preWires.contains g.output

/-- Construct the submodule input environment from the parent environment. -/
def subInputEnv (sub : Circuit) (inst : CircuitInstance) (env : Env) : Env :=
  fun w =>
    match resolvePort sub inst w with
    | some pw => env pw
    | none =>
      if w.name == "zero" then false
      else if w.name == "one" then true
      else false

/-- Apply one submodule instance in the combinational evaluation. -/
def applyInst (reg : ModuleRegistry) (evalSub : Circuit → Env → Env) (env : Env) (inst : CircuitInstance) : Env :=
  match reg.find? (fun p => p.1 == inst.moduleName) with
  | none => env
  | some (_, sub) =>
    let inEnv := subInputEnv sub inst env
    let outEnv := evalSub sub inEnv
    sub.outputs.foldl (fun e outWire =>
      match resolvePort sub inst outWire with
      | some pw => updateEnv e pw (outEnv outWire)
      | none => e
    ) env

/-- Combinational evaluation with instance elaboration.
    Pre-gates run first, then instances, then post-gates. -/
def evalHier (reg : ModuleRegistry) : Nat → Circuit → Env → Env
  | 0, _, env => env
  | fuel + 1, c, env =>
    let env₁ := evalGates (preGates reg c) env
    let env₂ := c.instances.foldl (applyInst reg (evalHier reg fuel)) env₁
    evalGates (postGates reg c) env₂

/-- Recursively collect all DFF output wires across a circuit and all its sub-instances,
    with nested instance names prepended using `instScope`. -/
def allDFFWiresAux (reg : ModuleRegistry) : Nat → Circuit → List Wire
  | 0, c => getDFFOutputs c
  | fuel + 1, c =>
    let localDffs := getDFFOutputs c
    let subDffs := c.instances.flatMap fun inst =>
      match reg.find? (fun p => p.1 == inst.moduleName) with
      | some (_, sub) =>
        (allDFFWiresAux reg fuel sub).map (instScope inst.instName)
      | none => []
    localDffs ++ subDffs

/-- All DFF output wires across the instance hierarchy of circuit `c`. -/
def allDFFWires (reg : ModuleRegistry) (fuel : Nat) (c : Circuit) : List Wire :=
  allDFFWiresAux reg fuel c

/-- Single-instance sequential fold step, parameterized by the sub-evaluation
    function so hierarchical stepping and spec assembly share one schedule.
    `recurse inst sub` evaluates the submodule from its scoped sub-state and
    wired input environment; hierarchical stepping passes
    `fun _ sub => stepHier reg fuel sub`, while composition proofs substitute
    a verified child spec. -/
def hierStepFold (recurse : CircuitInstance → Circuit → State → Env → State × Env)
    (reg : ModuleRegistry) (fuel : Nat) (s : State)
    (acc : List (Wire × Bool) × Env) (inst : CircuitInstance) :
    List (Wire × Bool) × Env :=
  match reg.find? (fun p => p.1 == inst.moduleName) with
  | none => acc
  | some (_, sub) =>
    let (accUpdates, accEnv) := acc
    let inEnv := subInputEnv sub inst accEnv
    let subState : State := fun w => s (instScope inst.instName w)
    let (subNextState, subOutEnv) := recurse inst sub subState inEnv
    let subDffs := allDFFWires reg fuel sub
    let scopedUpdates := subDffs.map fun w =>
      (instScope inst.instName w, subNextState w)
    let updatedEnv := sub.outputs.foldl (fun e outWire =>
      match resolvePort sub inst outWire with
      | some pw => updateEnv e pw (subOutEnv outWire)
      | none => e
    ) accEnv
    (accUpdates ++ scopedUpdates, updatedEnv)

/-- Evaluate one clock cycle of a hierarchical circuit.
    Instance states are threaded via `instScope`. -/
def stepHier (reg : ModuleRegistry) : Nat → Circuit → State → Env → State × Env
  | 0, _, s, env => (s, env)
  | fuel + 1, c, s, inputEnv =>
    let dffOutputs := getDFFOutputs c
    let envWithState := mergeStateIntoEnv s inputEnv dffOutputs
    let env₁ := evalCombGates (preGates reg c) envWithState
    let (subNextStates, env₂) := c.instances.foldl
      (hierStepFold (fun _ sub => stepHier reg fuel sub) reg fuel s) ([], env₁)
    let combEnv := evalCombGates (postGates reg c) env₂
    let topDFFUpdates := c.gates.filterMap fun gate =>
      if gate.gateType.isDFF then
        some (gate.output, evalDFF gate combEnv)
      else none
    let nextState := updateState s (topDFFUpdates ++ subNextStates)
    (nextState, combEnv)

/-- Recursive helper for instance depth calculation bounded by fuel. -/
def instanceDepthAux (reg : ModuleRegistry) : Nat → Circuit → Nat
  | 0, _ => 0
  | fuel + 1, c =>
    match c.instances with
    | [] => 0
    | insts =>
      1 + (insts.map fun inst =>
        match reg.find? (fun p => p.1 == inst.moduleName) with
        | some (_, sub) => instanceDepthAux reg fuel sub
        | none => 0
      ).foldl max 0

/-- Instance depth of a circuit in the registry. -/
def instanceDepth (reg : ModuleRegistry) (c : Circuit) : Nat :=
  instanceDepthAux reg (reg.length + 1) c

@[simp] theorem instanceInputWires_nil (reg : ModuleRegistry) (c : Circuit) (h : c.instances = []) :
    instanceInputWires reg c = [] := by
  dsimp [instanceInputWires]
  rw [h]
  rfl

@[simp] theorem faninConeWires_nil_seed (gates : List Gate) :
    faninConeWires gates [] = [] := by
  induction gates with
  | nil => rfl
  | cons g rest ih =>
    unfold faninConeWires at ih ⊢
    simp only [List.foldr_cons, ih, List.contains_nil, Bool.false_eq_true, ↓reduceIte]

/-- A 2-gate chain `g₁ → g₂ → inst_in` includes both `g₁.output` and `g₂.output`
    in `faninConeWires`, so both gates are scheduled in `preGates` before any
    submodule instance executes. -/
theorem faninConeWires_two_hop (g₁ g₂ : Gate) (seed : List Wire)
    (h_g₂ : seed.contains g₂.output = true)
    (h_chain : g₂.inputs.contains g₁.output = true) :
    let cone := faninConeWires [g₁, g₂] seed
    cone.contains g₁.output = true ∧ cone.contains g₂.output = true := by
  dsimp [faninConeWires]
  simp only [h_g₂, ↓reduceIte]
  have h₁ : (g₂.inputs ++ seed).contains g₁.output = true := by
    rw [List.contains_append, h_chain, Bool.true_or]
  simp only [h₁, ↓reduceIte, List.contains_append, Bool.or_eq_true]
  simp [h_g₂]

@[simp] theorem preGates_nil (reg : ModuleRegistry) (c : Circuit) (h : c.instances = []) :
    preGates reg c = [] := by
  dsimp [preGates]
  rw [instanceInputWires_nil reg c h, faninConeWires_nil_seed]
  dsimp [List.contains]
  generalize c.gates = gs
  induction gs with
  | nil => rfl
  | cons g rest ih =>
    dsimp [List.filter]
    exact ih

@[simp] theorem postGates_nil (reg : ModuleRegistry) (c : Circuit) (h : c.instances = []) :
    postGates reg c = c.gates := by
  dsimp [postGates]
  rw [instanceInputWires_nil reg c h, faninConeWires_nil_seed]
  dsimp [List.contains]
  generalize c.gates = gs
  induction gs with
  | nil => rfl
  | cons g rest ih =>
    dsimp [List.filter]
    rw [ih]
    rfl

/-! ## Soundness Theorems -/

/-- For flat circuits (no instances), evalHier matches evalCircuit for any fuel ≥ 1. -/
theorem evalHier_no_instances (reg : ModuleRegistry) (fuel : Nat) (c : Circuit)
    (h_inst : c.instances = []) (env : Env) :
    evalHier reg (fuel + 1) c env = evalCircuit c env := by
  dsimp [evalHier]
  rw [preGates_nil reg c h_inst, postGates_nil reg c h_inst, h_inst]
  dsimp
  rw [evalGates_nil]
  exact evalGates_eq_evalCircuit c env

/-- For flat circuits (no instances), stepHier matches evalCycleSequential for any fuel ≥ 1. -/
theorem stepHier_no_instances (reg : ModuleRegistry) (fuel : Nat) (c : Circuit)
    (h_inst : c.instances = []) (s : State) (i : Env) :
    stepHier reg (fuel + 1) c s i = evalCycleSequential c s i := by
  dsimp [stepHier, evalCycleSequential]
  rw [preGates_nil reg c h_inst, postGates_nil reg c h_inst, h_inst]
  dsimp [evalCombGates_nil]
  rw [List.append_nil]
  rfl

@[simp] theorem allDFFWires_nil (reg : ModuleRegistry) (fuel : Nat) (c : Circuit) (h : c.instances = []) :
    allDFFWires reg fuel c = getDFFOutputs c := by
  cases fuel with
  | zero => rfl
  | succ f =>
    dsimp [allDFFWires, allDFFWiresAux]
    rw [h]
    dsimp [List.flatMap]
    exact List.append_nil (getDFFOutputs c)

/-- Fuel independence of evalHier for flat circuits. -/
theorem evalHier_fuel_mono (reg : ModuleRegistry) (f₁ f₂ : Nat) (c : Circuit)
    (h_inst : c.instances = []) (env : Env) :
    evalHier reg (f₁ + 1) c env = evalHier reg (f₂ + 1) c env := by
  rw [evalHier_no_instances reg f₁ c h_inst, evalHier_no_instances reg f₂ c h_inst]

/-! ## Hierarchical Trace Construction -/

/-- A trace `tr` is a faithful hierarchical execution of circuit `c`. -/
def IsHierExecutionOf (reg : ModuleRegistry) (fuel : Nat) (c : Circuit)
    (s0 : State) (inputs : Nat → Env) (tr : Trace) : Prop :=
  tr.initState = s0 ∧
  ∀ t : Nat,
    let step := stepHier reg fuel c (tr.stateAt t) (inputs t)
    tr.envAt t = step.2 ∧ tr.stateAt (t + 1) = step.1

/-- Closed-form recursive state computation for hierarchical circuits. -/
def evalHierStateAt (reg : ModuleRegistry) (fuel : Nat) (c : Circuit)
    (s0 : State) (inputs : Nat → Env) : Nat → State
  | 0 => s0
  | t + 1 => (stepHier reg fuel c (evalHierStateAt reg fuel c s0 inputs t) (inputs t)).1

/-- Construct the deterministic execution trace of hierarchical circuit `c`. -/
def runHierTrace (reg : ModuleRegistry) (fuel : Nat) (c : Circuit)
    (s0 : State) (inputs : Nat → Env) : Trace :=
  fun t =>
    let st := evalHierStateAt reg fuel c s0 inputs t
    let env := (stepHier reg fuel c st (inputs t)).2
    ⟨st, env⟩

/-- The generated `runHierTrace` is an execution of hierarchical circuit `c`. -/
theorem runHierTrace_isExecution (reg : ModuleRegistry) (fuel : Nat) (c : Circuit)
    (s0 : State) (inputs : Nat → Env) :
    IsHierExecutionOf reg fuel c s0 inputs (runHierTrace reg fuel c s0 inputs) := by
  constructor
  · rfl
  · intro t
    exact ⟨rfl, rfl⟩

/-- For flat circuits, hierarchical execution is equivalent to standard trace execution. -/
theorem isHierExecutionOf_no_instances (reg : ModuleRegistry) (fuel : Nat) (c : Circuit)
    (h_inst : c.instances = []) (s0 : State) (inputs : Nat → Env) (tr : Trace) :
    IsHierExecutionOf reg (fuel + 1) c s0 inputs tr ↔ Trace.IsExecutionOf c s0 inputs tr := by
  dsimp [IsHierExecutionOf, Trace.IsExecutionOf]
  constructor
  · intro ⟨h_init, h_step⟩
    refine ⟨h_init, fun t => ?_⟩
    have ht := h_step t
    rw [stepHier_no_instances reg fuel c h_inst] at ht
    exact ht
  · intro ⟨h_init, h_step⟩
    refine ⟨h_init, fun t => ?_⟩
    have ht := h_step t
    rw [stepHier_no_instances reg fuel c h_inst]
    exact ht

end Shoumei.Semantics.Hierarchical
