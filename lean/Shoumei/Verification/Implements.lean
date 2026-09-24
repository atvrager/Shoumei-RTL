/-
Verification/Implements.lean - Commuting-Square Refinement Semantics

Defines transition-system behavioral refinement between a gate-level circuit and
a specification model:
- `Behavior`: Behavioral model of a synchronous module (init, step, out)
- `Implements`: Commuting square for state step and output decoding over `stepHier`
  with inductive state reachability invariant `inv : State → Prop`
- `CombBehavior`: Pure function input -> output
- `ImplementsComb`: Combinational refinement over `evalHier`
- Lifting theorems:
  - `implements_of_flat`: Lifting flat sequential proofs to `Implements`
  - `implementsComb_of_flat`: Lifting flat combinational proofs to `ImplementsComb`
  - `implements_trace`: Trace-level behavioral preservation over `runHierTrace`
  - `implements_refines_of_flat`: Connection to `Trace.IsExecutionOf`
- Non-vacuous specification guarantees:
  - `CertifiedRefinementAtom`: Couples non-vacuous behavior with refinement proof
  - `CertifiedCombRefinementAtom`: Combinational non-vacuous refinement
  - Proofs that trivial constant behaviors cannot be certified
-/

import Shoumei.DSL
import Shoumei.DSL.PortResolve
import Shoumei.Semantics
import Shoumei.Semantics.Hierarchical
import Shoumei.Temporal.Trace
import Shoumei.Verification.Compositional

namespace Shoumei.Verification

open Shoumei
open Shoumei.DSL.PortResolve
open Shoumei.Semantics
open Shoumei.Semantics.Hierarchical
open Shoumei.Temporal

/-- A behavioral model of a synchronous state machine / hardware module. -/
structure Behavior (σ ι ω : Type) where
  init : σ
  step : σ → ι → σ
  out  : σ → ι → ω

/-- Compute the model state after `t` steps on input stream `inputs`. -/
def evalBehaviorState (B : Behavior σ ι ω) (inputs : Nat → ι) : Nat → σ
  | 0 => B.init
  | t + 1 => B.step (evalBehaviorState B inputs t) (inputs t)

/-- `Implements`: Commuting-square refinement between hierarchical circuit `c` and
    behavioral model `B` under an inductive reachability invariant `inv`.
    - `absS`: State abstraction function (circuit State -> model state σ)
    - `encI`: Input encoder (model input ι -> circuit input Env)
    - `decO`: Output decoder (circuit output Env -> model output ω)
    - `inv` : Inductive state invariant (defaults to `fun _ => True`)
-/
structure Implements (reg : ModuleRegistry) (fuel : Nat) (c : Circuit)
    (B : Behavior σ ι ω)
    (absS : State → σ) (encI : ι → Env) (decO : Env → ω)
    (inv : State → Prop := fun _ => True) : Prop where
  init_inv : inv initState
  step_inv : ∀ s i, inv s → inv (stepHier reg fuel c s (encI i)).1
  init_ok  : absS initState = B.init
  step_ok  : ∀ s i, inv s → absS (stepHier reg fuel c s (encI i)).1 = B.step (absS s) i
  out_ok   : ∀ s i, inv s → decO (stepHier reg fuel c s (encI i)).2 = B.out (absS s) i

/-- Pure combinational behavior: input to output function. -/
structure CombBehavior (ι ω : Type) where
  eval : ι → ω

/-- Lift a combinational behavior to a synchronous behavior over Unit state. -/
def CombBehavior.toBehavior (B : CombBehavior ι ω) : Behavior Unit ι ω where
  init := ()
  step := fun () _ => ()
  out  := fun () i => B.eval i

/-- Refinement for combinational circuits: the circuit evaluated via `evalHier`
    matches the behavioral model's evaluation for all inputs. -/
def ImplementsComb (reg : ModuleRegistry) (fuel : Nat) (c : Circuit)
    (B : CombBehavior ι ω) (encI : ι → Env) (decO : Env → ω) : Prop :=
  ∀ i, decO (evalHier reg fuel c (encI i)) = B.eval i

/-! ## Lifting Lemmas for Flat Circuits -/

/-- Lift a flat sequential circuit proof to `Implements` under a state invariant. -/
theorem implements_of_flat
    (reg : ModuleRegistry) (fuel : Nat) (c : Circuit)
    (h_inst : c.instances = [])
    (B : Behavior σ ι ω)
    (absS : State → σ) (encI : ι → Env) (decO : Env → ω)
    (inv : State → Prop)
    (h_init_inv : inv initState)
    (h_step_inv : ∀ s i, inv s → inv (evalCycleSequential c s (encI i)).1)
    (h_init : absS initState = B.init)
    (h_step : ∀ s i, inv s → absS (evalCycleSequential c s (encI i)).1 = B.step (absS s) i)
    (h_out  : ∀ s i, inv s → decO (evalCycleSequential c s (encI i)).2 = B.out (absS s) i) :
    Implements reg (fuel + 1) c B absS encI decO inv := by
  refine ⟨h_init_inv, fun s i h_inv => ?_, h_init, fun s i h_inv => ?_, fun s i h_inv => ?_⟩
  · rw [stepHier_no_instances reg fuel c h_inst]
    exact h_step_inv s i h_inv
  · rw [stepHier_no_instances reg fuel c h_inst]
    exact h_step s i h_inv
  · rw [stepHier_no_instances reg fuel c h_inst]
    exact h_out s i h_inv

/-- Lift a flat sequential circuit proof without an invariant (inv := fun _ => True). -/
theorem implements_of_flat_trivial
    (reg : ModuleRegistry) (fuel : Nat) (c : Circuit)
    (h_inst : c.instances = [])
    (B : Behavior σ ι ω)
    (absS : State → σ) (encI : ι → Env) (decO : Env → ω)
    (h_init : absS initState = B.init)
    (h_step : ∀ s i, absS (evalCycleSequential c s (encI i)).1 = B.step (absS s) i)
    (h_out  : ∀ s i, decO (evalCycleSequential c s (encI i)).2 = B.out (absS s) i) :
    Implements reg (fuel + 1) c B absS encI decO (fun _ => True) := by
  refine ⟨trivial, fun _ _ _ => trivial, h_init, fun s i _ => ?_, fun s i _ => ?_⟩
  · rw [stepHier_no_instances reg fuel c h_inst]
    exact h_step s i
  · rw [stepHier_no_instances reg fuel c h_inst]
    exact h_out s i

/-- Lift a flat combinational circuit proof to `ImplementsComb`. -/
theorem implementsComb_of_flat
    (reg : ModuleRegistry) (fuel : Nat) (c : Circuit)
    (h_inst : c.instances = [])
    (B : CombBehavior ι ω)
    (encI : ι → Env) (decO : Env → ω)
    (h_eval : ∀ i, decO (evalCircuit c (encI i)) = B.eval i) :
    ImplementsComb reg (fuel + 1) c B encI decO := by
  intro i
  rw [evalHier_no_instances reg fuel c h_inst]
  exact h_eval i

/-! ## Composition (Phase 3: `implements_compose`)

A parent assembled from instances implements the composed behaviour, given an
atom for every child module and a proof that the parent's own gates plus
wiring carry the children's outputs to the parent's behaviour.

Child correctness is stated with a per-module spec dispatch
(`childSpec : Circuit → ...`), so one lemma covers heterogeneous children
without existential types: the spec assembly reuses `applyInst` /
`hierStepFold` with the spec in place of recursion, i.e. the exact schedule
`evalHier` / `stepHier` use. The demos in `Verification/CompositionDemos.lean`
instantiate these lemmas on the two plan-nominated hierarchies (`Mux8x32`,
`Register160`). -/

/-- Child atom (combinational): hierarchical evaluation of the submodule
    agrees with its spec on every wired input environment. -/
def ChildCombAtom (reg : ModuleRegistry) (fuel : Nat) (inst : CircuitInstance)
    (childSpec : Circuit → Env → Env) : Prop :=
  ∀ (nm : String) (sub : Circuit),
    reg.find? (fun p => p.1 == inst.moduleName) = some (nm, sub) →
    ∀ inEnv, evalHier reg fuel sub inEnv = childSpec sub inEnv

/-- Spec-assembled parent evaluation: pre-gates, then spec instances, then
    post-gates — the same schedule `evalHier` uses. -/
def specParentEval (childSpec : Circuit → Env → Env)
    (reg : ModuleRegistry) (parent : Circuit) (env : Env) : Env :=
  let env₁ := evalGates (preGates reg parent) env
  let env₂ := parent.instances.foldl (applyInst reg childSpec) env₁
  evalGates (postGates reg parent) env₂

/-- Glue obligation (combinational): the spec-assembled environment decodes to
    the parent behaviour. -/
def GlueCombCommutes (reg : ModuleRegistry) (parent : Circuit)
    (B : CombBehavior ι ω) (encI : ι → Env) (decO : Env → ω)
    (childSpec : Circuit → Env → Env) : Prop :=
  ∀ i, decO (specParentEval childSpec reg parent (encI i)) = B.eval i

/-- Fold congruence: pointwise-equal step functions give equal folds. -/
theorem foldl_apply_congr {f g : Env → CircuitInstance → Env}
    {insts : List CircuitInstance}
    (h : ∀ inst ∈ insts, ∀ env, f env inst = g env inst) :
    ∀ init, insts.foldl f init = insts.foldl g init := by
  induction insts with
  | nil => intro init; rfl
  | cons hd tl ih =>
    intro init
    simp only [List.foldl_cons]
    have h_hd : ∀ env, f env hd = g env hd :=
      fun env => h hd List.mem_cons_self env
    have h_tl : ∀ inst ∈ tl, ∀ env, f env inst = g env inst :=
      fun inst h_mem env => h inst (List.Mem.tail _ h_mem) env
    rw [h_hd init]
    exact ih h_tl _

/-- Parent hierarchical evaluation equals spec-assembled evaluation when every
    child atom holds. -/
theorem evalHier_eq_specParentEval
    (reg : ModuleRegistry) (fuel : Nat) (parent : Circuit)
    (childSpec : Circuit → Env → Env)
    (h_children : ∀ inst ∈ parent.instances,
      ChildCombAtom reg fuel inst childSpec) :
    ∀ env, evalHier reg (fuel + 1) parent env =
             specParentEval childSpec reg parent env := by
  intro env
  have h_fold : parent.instances.foldl (applyInst reg (evalHier reg fuel))
      (evalGates (preGates reg parent) env)
      = parent.instances.foldl (applyInst reg childSpec)
        (evalGates (preGates reg parent) env) := by
    apply foldl_apply_congr
    intro inst h_mem acc
    have h_atom := h_children inst h_mem
    match h_sub : reg.find? (fun p => p.1 == inst.moduleName) with
    | none => simp only [applyInst, h_sub]
    | some (nm, sub) =>
      have h_eq : ∀ inEnv, evalHier reg fuel sub inEnv = childSpec sub inEnv :=
        fun inEnv => h_atom nm sub h_sub inEnv
      simp only [applyInst, h_sub, h_eq]
  dsimp only [evalHier, specParentEval]
  rw [h_fold]

/-- Given an atom for every module the parent instantiates, and a proof that
    the parent's own gates plus wiring carry the children's outputs to the
    parent's behaviour, the parent implements its behaviour. -/
theorem implementsComb_compose
    (reg : ModuleRegistry) (fuel : Nat) (parent : Circuit)
    (h_wired : WellWired reg parent = true)
    (B : CombBehavior ι ω) (encI : ι → Env) (decO : Env → ω)
    (childSpec : Circuit → Env → Env)
    (h_children : ∀ inst ∈ parent.instances,
      ChildCombAtom reg fuel inst childSpec)
    (h_glue : GlueCombCommutes reg parent B encI decO childSpec) :
    ImplementsComb reg (fuel + 1) parent B encI decO := by
  have _ := h_wired
  intro i
  have h_eq := evalHier_eq_specParentEval reg fuel parent childSpec h_children (encI i)
  rw [h_eq]
  exact h_glue i

/-! ## Sequential composition -/

/-- Child atom (sequential): hierarchical stepping of the submodule agrees
    with its spec from every sub-state and wired input environment. -/
def ChildAtom (reg : ModuleRegistry) (fuel : Nat) (inst : CircuitInstance)
    (childSpec : Circuit → State → Env → State × Env) : Prop :=
  ∀ (nm : String) (sub : Circuit),
    reg.find? (fun p => p.1 == inst.moduleName) = some (nm, sub) →
    ∀ sSub inEnv, stepHier reg fuel sub sSub inEnv = childSpec sub sSub inEnv

/-- Spec-assembled parent cycle: same schedule as `stepHier` (pre-gates,
    spec instances via `hierStepFold`, post-gates, top DFF updates). -/
def specParentStep (childSpec : Circuit → State → Env → State × Env)
    (reg : ModuleRegistry) (fuel : Nat) (parent : Circuit)
    (s : State) (inputEnv : Env) : State × Env :=
  let dffOutputs := getDFFOutputs parent
  let envWithState := mergeStateIntoEnv s inputEnv dffOutputs
  let env₁ := evalCombGates (preGates reg parent) envWithState
  let (subUpdates, env₂) :=
    parent.instances.foldl
      (hierStepFold (fun _ sub => childSpec sub) reg fuel s) ([], env₁)
  let combEnv := evalCombGates (postGates reg parent) env₂
  let topUpdates := parent.gates.filterMap fun gate =>
    if gate.gateType.isDFF then
      some (gate.output, evalDFF gate combEnv)
    else none
  (updateState s (topUpdates ++ subUpdates), combEnv)

/-- Glue obligation (sequential): the spec-assembled cycle preserves the
    invariant and commutes with the parent behaviour. -/
structure GlueCommutes (reg : ModuleRegistry) (fuel : Nat) (parent : Circuit)
    (B : Behavior σ ι ω)
    (absS : State → σ) (encI : ι → Env) (decO : Env → ω)
    (inv : State → Prop)
    (childSpec : Circuit → State → Env → State × Env) : Prop where
  step_inv : ∀ s i, inv s → inv (specParentStep childSpec reg fuel parent s (encI i)).1
  step_ok : ∀ s i, inv s →
    absS (specParentStep childSpec reg fuel parent s (encI i)).1 = B.step (absS s) i
  out_ok : ∀ s i, inv s →
    decO (specParentStep childSpec reg fuel parent s (encI i)).2 = B.out (absS s) i

/-- Fold congruence for the sequential accumulator. -/
theorem foldl_step_congr
    {f g : (List (Wire × Bool) × Env) → CircuitInstance → (List (Wire × Bool) × Env)}
    {insts : List CircuitInstance}
    (h : ∀ inst ∈ insts, ∀ acc, f acc inst = g acc inst) :
    ∀ init, insts.foldl f init = insts.foldl g init := by
  induction insts with
  | nil => intro init; rfl
  | cons hd tl ih =>
    intro init
    simp only [List.foldl_cons]
    have h_hd : ∀ acc, f acc hd = g acc hd :=
      fun acc => h hd List.mem_cons_self acc
    have h_tl : ∀ inst ∈ tl, ∀ acc, f acc inst = g acc inst :=
      fun inst h_mem acc => h inst (List.Mem.tail _ h_mem) acc
    rw [h_hd init]
    exact ih h_tl _

/-- Parent hierarchical stepping equals spec-assembled stepping when every
    child atom holds. -/
theorem stepHier_eq_specParentStep
    (reg : ModuleRegistry) (fuel : Nat) (parent : Circuit)
    (childSpec : Circuit → State → Env → State × Env)
    (h_children : ∀ inst ∈ parent.instances,
      ChildAtom reg fuel inst childSpec) :
    ∀ s inputEnv, stepHier reg (fuel + 1) parent s inputEnv =
                   specParentStep childSpec reg fuel parent s inputEnv := by
  intro s inputEnv
  have h_fold : parent.instances.foldl
        (hierStepFold (fun _ sub => stepHier reg fuel sub) reg fuel s)
        ([], evalCombGates (preGates reg parent)
          (mergeStateIntoEnv s inputEnv (getDFFOutputs parent)))
      = parent.instances.foldl
        (hierStepFold (fun _ sub => childSpec sub) reg fuel s)
        ([], evalCombGates (preGates reg parent)
          (mergeStateIntoEnv s inputEnv (getDFFOutputs parent))) := by
    apply foldl_step_congr
    intro inst h_mem acc
    have h_atom := h_children inst h_mem
    match h_sub : reg.find? (fun p => p.1 == inst.moduleName) with
    | none => simp only [hierStepFold, h_sub]
    | some (nm, sub) =>
      have h_eq : ∀ sSub inEnv,
          stepHier reg fuel sub sSub inEnv = childSpec sub sSub inEnv :=
        fun sSub inEnv => h_atom nm sub h_sub sSub inEnv
      simp only [hierStepFold, h_sub, h_eq]
  dsimp only [stepHier, specParentStep]
  rw [h_fold]

/-- Given an atom for every module the parent instantiates, and a proof that
    the parent's own gates plus wiring carry the children's outputs to the
    parent's behaviour, the parent implements its behaviour. -/
theorem implements_compose
    (reg : ModuleRegistry) (fuel : Nat) (parent : Circuit)
    (h_wired : WellWired reg parent = true)
    (B : Behavior σ ι ω)
    (absS : State → σ) (encI : ι → Env) (decO : Env → ω)
    (inv : State → Prop)
    (h_init_inv : inv initState)
    (h_init : absS initState = B.init)
    (childSpec : Circuit → State → Env → State × Env)
    (h_children : ∀ inst ∈ parent.instances,
      ChildAtom reg fuel inst childSpec)
    (h_glue : GlueCommutes reg fuel parent B absS encI decO inv childSpec) :
    Implements reg (fuel + 1) parent B absS encI decO inv := by
  have _ := h_wired
  have h_eq : ∀ s i, stepHier reg (fuel + 1) parent s (encI i) =
                   specParentStep childSpec reg fuel parent s (encI i) :=
    fun s i => stepHier_eq_specParentStep reg fuel parent childSpec h_children s (encI i)
  refine ⟨h_init_inv, fun s i h_inv => ?_, h_init, fun s i h_inv => ?_, fun s i h_inv => ?_⟩
  · rw [h_eq s i]
    exact h_glue.step_inv s i h_inv
  · rw [h_eq s i]
    exact h_glue.step_ok s i h_inv
  · rw [h_eq s i]
    exact h_glue.out_ok s i h_inv

/-! ## Trace-Level Refinement -/

/-- Every execution of `runHierTrace` matches the behavior state step and output. -/
theorem implements_trace
    (reg : ModuleRegistry) (fuel : Nat) (c : Circuit)
    (B : Behavior σ ι ω)
    (absS : State → σ) (encI : ι → Env) (decO : Env → ω)
    (inv : State → Prop)
    (h_impl : Implements reg fuel c B absS encI decO inv)
    (inputs : Nat → ι) :
    let tr := runHierTrace reg fuel c initState (fun t => encI (inputs t))
    (∀ t, inv (tr.stateAt t)) ∧
    (∀ t, absS (tr.stateAt t) = evalBehaviorState B inputs t) ∧
    (∀ t, decO (tr.envAt t) = B.out (evalBehaviorState B inputs t) (inputs t)) := by
  intro tr
  have h_inv : ∀ t, inv (tr.stateAt t) := by
    intro t
    induction t with
    | zero =>
      have h_zero : tr.stateAt 0 = initState := rfl
      rw [h_zero]
      exact h_impl.init_inv
    | succ t ih =>
      have h_next : tr.stateAt (t + 1) = (stepHier reg fuel c (tr.stateAt t) (encI (inputs t))).1 := rfl
      rw [h_next]
      exact h_impl.step_inv (tr.stateAt t) (inputs t) ih
  have h_state : ∀ t, absS (tr.stateAt t) = evalBehaviorState B inputs t := by
    intro t
    induction t with
    | zero =>
      have h_zero : tr.stateAt 0 = initState := rfl
      rw [h_zero]
      exact h_impl.init_ok
    | succ t ih =>
      have h_next : tr.stateAt (t + 1) = (stepHier reg fuel c (tr.stateAt t) (encI (inputs t))).1 := rfl
      rw [h_next, h_impl.step_ok (tr.stateAt t) (inputs t) (h_inv t), ih]
      rfl
  refine ⟨h_inv, h_state, fun t => ?_⟩
  have h_env : tr.envAt t = (stepHier reg fuel c (tr.stateAt t) (encI (inputs t))).2 := rfl
  rw [h_env, h_impl.out_ok (tr.stateAt t) (inputs t) (h_inv t), h_state t]

/-- State equivalence for executions of flat circuits. -/
theorem isExecutionOf_state_eq (c : Circuit) (s0 : State) (inputs : Nat → Env) (tr : Trace)
    (h_exec : Trace.IsExecutionOf c s0 inputs tr) :
    ∀ t, tr.stateAt t = Trace.evalStateAt c s0 inputs t := by
  intro t
  induction t with
  | zero => exact h_exec.1
  | succ t ih =>
    dsimp [Trace.evalStateAt]
    have ht := (h_exec.2 t).2
    rw [ht, ih]

/-- For flat circuits, `Implements` guarantees that any trace execution under encoded inputs
    satisfies the behavioral output specification. -/
theorem implements_refines_of_flat
    (reg : ModuleRegistry) (fuel : Nat) (c : Circuit)
    (h_inst : c.instances = [])
    (B : Behavior σ ι ω)
    (absS : State → σ) (encI : ι → Env) (decO : Env → ω)
    (inv : State → Prop)
    (h_impl : Implements reg (fuel + 1) c B absS encI decO inv)
    (inputs : Nat → ι) (tr : Trace)
    (h_exec : Trace.IsExecutionOf c initState (fun t => encI (inputs t)) tr) :
    (∀ t, inv (tr.stateAt t)) ∧
    (∀ t, absS (tr.stateAt t) = evalBehaviorState B inputs t) ∧
    (∀ t, decO (tr.envAt t) = B.out (evalBehaviorState B inputs t) (inputs t)) := by
  have h_inv : ∀ t, inv (tr.stateAt t) := by
    intro t
    induction t with
    | zero =>
      have h_init : tr.stateAt 0 = tr.initState := rfl
      rw [h_init, h_exec.1]
      exact h_impl.init_inv
    | succ t ih =>
      have ht := (h_exec.2 t).2
      rw [ht]
      have h_step_inv := h_impl.step_inv (tr.stateAt t) (inputs t) ih
      rw [stepHier_no_instances reg fuel c h_inst] at h_step_inv
      exact h_step_inv
  have h_state : ∀ t, absS (tr.stateAt t) = evalBehaviorState B inputs t := by
    intro t
    induction t with
    | zero =>
      have h_init : tr.stateAt 0 = tr.initState := rfl
      rw [h_init, h_exec.1]
      exact h_impl.init_ok
    | succ t ih =>
      have ht := (h_exec.2 t).2
      rw [ht]
      have h_step := h_impl.step_ok (tr.stateAt t) (inputs t) (h_inv t)
      rw [stepHier_no_instances reg fuel c h_inst] at h_step
      rw [h_step, ih]
      rfl
  refine ⟨h_inv, h_state, fun t => ?_⟩
  have ht_env := (h_exec.2 t).1
  rw [ht_env]
  have h_out := h_impl.out_ok (tr.stateAt t) (inputs t) (h_inv t)
  rw [stepHier_no_instances reg fuel c h_inst] at h_out
  rw [h_out, h_state t]

/-! ## Non-Vacuous Specification Guarantees -/

/-- Trace specification induced by a Behavior and decoders:
    output decodes to the behavioral model output at all cycles. -/
def behaviorTraceSpec (B : Behavior σ ι ω) (decO : Env → ω) (inputs : Nat → ι) : TraceSpec :=
  fun tr => ∀ t, decO (tr.envAt t) = B.out (evalBehaviorState B inputs t) (inputs t)

/-- An Implements refinement is non-vacuous if its induced trace specification is non-trivial. -/
def Implements.nonVacuous (B : Behavior σ ι ω) (decO : Env → ω) : Prop :=
  ∃ inputs : Nat → ι, NonTrivialSpec (behaviorTraceSpec B decO inputs)

/-- A behavior is non-vacuous if its output function is not constant. -/
def NonVacuousBehavior (B : Behavior σ ι ω) : Prop :=
  ∃ s₁ s₂ i₁ i₂, B.out s₁ i₁ ≠ B.out s₂ i₂

/-- Trivial constant behaviors are not non-vacuous. -/
theorem constant_behavior_is_not_non_vacuous (ι : Type) (s0 : σ) (step : σ → ι → σ) (c : ω) :
    ¬ NonVacuousBehavior ({ init := s0, step := step, out := fun _ _ => c } : Behavior σ ι ω) := by
  intro ⟨s₁, s₂, i₁, i₂, h_ne⟩
  exact h_ne rfl

/-- A combinational behavior is non-vacuous if it produces at least two distinct outputs. -/
def NonVacuousCombBehavior (B : CombBehavior ι ω) : Prop :=
  ∃ i₁ i₂, B.eval i₁ ≠ B.eval i₂

/-- Trivial constant combinational behaviors are not non-vacuous. -/
theorem constant_comb_behavior_is_not_non_vacuous (ι : Type) (c : ω) :
    ¬ NonVacuousCombBehavior ({ eval := fun (_ : ι) => c } : CombBehavior ι ω) := by
  intro ⟨i₁, i₂, h_ne⟩
  exact h_ne rfl

/-- Certified Refinement Atom: Requires both an inductive Implements proof and a non-vacuous behavior,
    banning trivial constant behaviors by construction. -/
structure CertifiedRefinementAtom (reg : ModuleRegistry) (fuel : Nat) (c : Circuit)
    (B : Behavior σ ι ω)
    (absS : State → σ) (encI : ι → Env) (decO : Env → ω)
    (inv : State → Prop := fun _ => True) where
  non_vacuous : NonVacuousBehavior B
  implements  : Implements reg fuel c B absS encI decO inv

/-- Certified Combinational Refinement Atom: Requires both an ImplementsComb proof and a non-vacuous
    combinational behavior. -/
structure CertifiedCombRefinementAtom (reg : ModuleRegistry) (fuel : Nat) (c : Circuit)
    (B : CombBehavior ι ω)
    (encI : ι → Env) (decO : Env → ω) where
  non_vacuous : NonVacuousCombBehavior B
  implements  : ImplementsComb reg fuel c B encI decO

/-- Theorem: It is mathematically impossible to certify a trivial constant behavior. -/
theorem constant_behavior_cannot_be_certified (ι : Type) (s0 : σ) (step : σ → ι → σ) (c_val : ω) :
    ¬ NonVacuousBehavior ({ init := s0, step := step, out := fun _ _ => c_val } : Behavior σ ι ω) :=
  constant_behavior_is_not_non_vacuous ι s0 step c_val

/-- Theorem: It is mathematically impossible to certify a trivial constant combinational behavior. -/
theorem constant_comb_behavior_cannot_be_certified (ι : Type) (c_val : ω) :
    ¬ NonVacuousCombBehavior ({ eval := fun (_ : ι) => c_val } : CombBehavior ι ω) :=
  constant_comb_behavior_is_not_non_vacuous ι c_val

end Shoumei.Verification
