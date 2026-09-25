/-
Reflection/FlattenSoundness.lean - Multi-level & Sequential Flattener Soundness

Extends `CompileCircuit.lean` with:
1. `flattenRegistry` & `flatten_sound_step`: Inductive multi-level combinational
   flattener soundness (`evalHier reg (k + 2) parent` agrees with
   `evalCircuit (flattenAllFuel reg parent (k + 1))` whenever flattened children
   satisfy `ChildFlatOK` and inductive soundness).
2. `flatten_step_sound`: Sequential cycle bisimulation over `StateCorr` between
   `stepHier` and `evalCycleSequential (flattenAllFuel reg parent 1)`.
-/

import Shoumei.Reflection.CompileCircuit

namespace Shoumei.Reflection

open Shoumei
open Shoumei.DSL.PortResolve
open Shoumei.Semantics
open Shoumei.Semantics.Hierarchical

/-! ## Multi-level combinational flattener soundness (`flatten_sound_step`) -/

/-- Flatten every module in `reg` by `fuel` steps. Reducing depth-(k+1) flattening
    of `parent` over `reg` to depth-1 flattening of `parent` over
    `flattenRegistry reg k` reuses `flatten_sound_depth1` directly. -/
def flattenRegistry (reg : ModuleRegistry) (fuel : Nat) : ModuleRegistry :=
  reg.map (fun p => (p.1, flattenAllFuel reg p.2 fuel))

@[simp] theorem flattenAllFuel_inputs (reg : ModuleRegistry) (c : Circuit) (fuel : Nat) :
    (flattenAllFuel reg c fuel).inputs = c.inputs := by
  cases fuel <;> rfl

@[simp] theorem flattenAllFuel_outputs (reg : ModuleRegistry) (c : Circuit) (fuel : Nat) :
    (flattenAllFuel reg c fuel).outputs = c.outputs := by
  cases fuel <;> rfl

@[simp] theorem flattenAllFuel_signalGroups (reg : ModuleRegistry) (c : Circuit) (fuel : Nat) :
    (flattenAllFuel reg c fuel).signalGroups = c.signalGroups := by
  cases fuel <;> rfl

@[simp] theorem resolvePortWithIndex_flattenAllFuel (reg : ModuleRegistry) (c : Circuit)
    (idx : InstancePortMapIndex) (fuel : Nat) (w : Wire) :
    resolvePortWithIndex (flattenAllFuel reg c fuel) idx w = resolvePortWithIndex c idx w := by
  dsimp [resolvePortWithIndex]
  rw [flattenAllFuel_signalGroups]

@[simp] theorem resolvePort_flattenAllFuel (reg : ModuleRegistry) (c : Circuit)
    (inst : CircuitInstance) (fuel : Nat) :
    resolvePort (flattenAllFuel reg c fuel) inst = resolvePort c inst := by
  funext w
  exact resolvePortWithIndex_flattenAllFuel reg c (buildInstanceIndex inst) fuel w

@[simp] theorem flattenRemap_flattenAllFuel (reg : ModuleRegistry) (c : Circuit)
    (inst : CircuitInstance) (fuel : Nat) :
    flattenRemap (flattenAllFuel reg c fuel) inst = flattenRemap c inst := by
  funext w
  dsimp [flattenRemap]
  rw [resolvePort_flattenAllFuel]

@[simp] theorem subInputEnv_flattenAllFuel (reg : ModuleRegistry) (c : Circuit)
    (inst : CircuitInstance) (fuel : Nat) (env : Env) :
    subInputEnv (flattenAllFuel reg c fuel) inst env = subInputEnv c inst env := by
  funext w
  dsimp [subInputEnv]
  rw [resolvePort_flattenAllFuel]

theorem find?_map_fst {α β γ : Type} (xs : List (α × β)) (f : β → γ) (p : α → Bool) :
    (xs.map (fun x => (x.1, f x.2))).find? (fun x => p x.1) =
    (xs.find? (fun x => p x.1)).map (fun x => (x.1, f x.2)) := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    dsimp [List.find?]
    cases p hd.1 with
    | true => rfl
    | false => exact ih

theorem flattenRegistry_find? (reg : ModuleRegistry) (fuel : Nat) (name : String) :
    (flattenRegistry reg fuel).find? (fun p => p.1 == name) =
    (reg.find? (fun p => p.1 == name)).map (fun p => (p.1, flattenAllFuel reg p.2 fuel)) :=
  find?_map_fst reg (fun c => flattenAllFuel reg c fuel) (· == name)

@[simp] theorem instanceInputWires_flattenRegistry (reg : ModuleRegistry) (c : Circuit) (fuel : Nat) :
    instanceInputWires (flattenRegistry reg fuel) c = instanceInputWires reg c := by
  dsimp [instanceInputWires]
  congr 1
  funext inst
  rw [flattenRegistry_find?]
  cases reg.find? (fun p => p.1 == inst.moduleName) with
  | none => rfl
  | some p =>
    dsimp only [Option.map]
    rw [flattenAllFuel_inputs, resolvePort_flattenAllFuel]

@[simp] theorem preGates_flattenRegistry (reg : ModuleRegistry) (c : Circuit) (fuel : Nat) :
    preGates (flattenRegistry reg fuel) c = preGates reg c := by
  dsimp [preGates]
  rw [instanceInputWires_flattenRegistry]

@[simp] theorem postGates_flattenRegistry (reg : ModuleRegistry) (c : Circuit) (fuel : Nat) :
    postGates (flattenRegistry reg fuel) c = postGates reg c := by
  dsimp [postGates]
  rw [instanceInputWires_flattenRegistry]

/-- Flattening `c` with fuel `k + 1` over `reg` is identical to flattening `c`
    with fuel `1` over `flattenRegistry reg k`. -/
theorem flattenAllFuel_succ_eq_depth1 (reg : ModuleRegistry) (c : Circuit) (k : Nat) :
    flattenAllFuel reg c (k + 1) = flattenAllFuel (flattenRegistry reg k) c 1 := by
  change ({ c with
      gates := preGates reg c ++
        (c.instances.flatMap fun inst =>
          match reg.find? (fun p => p.1 == inst.moduleName) with
          | some (_, subCircuit) =>
            Circuit.inline (flattenAllFuel reg subCircuit k) (flattenRemap subCircuit inst)
          | none => []) ++
        postGates reg c
      instances := [] } : Circuit) =
    { c with
      gates := preGates (flattenRegistry reg k) c ++
        (c.instances.flatMap fun inst =>
          match (flattenRegistry reg k).find? (fun p => p.1 == inst.moduleName) with
          | some (_, subCircuit) =>
            Circuit.inline subCircuit (flattenRemap subCircuit inst)
          | none => []) ++
        postGates (flattenRegistry reg k) c
      instances := [] }
  simp only [preGates_flattenRegistry, postGates_flattenRegistry]
  congr 1
  congr 1
  congr 1
  congr 1
  funext inst
  rw [flattenRegistry_find?]
  cases reg.find? (fun p => p.1 == inst.moduleName) with
  | none => rfl
  | some p =>
    dsimp only [Option.map]
    rw [flattenRemap_flattenAllFuel]

/-- Output propagation depends only on the child output environment values at `outs`. -/
theorem foldl_propagate_congr (outs : List Wire) (sub : Circuit)
    (inst : CircuitInstance) (outEnv₁ outEnv₂ : Env) (eH : Env)
    (h_eq : ∀ w ∈ outs, outEnv₁ w = outEnv₂ w) :
    outs.foldl (fun e outWire =>
      match resolvePort sub inst outWire with
      | some p => updateEnv e p (outEnv₁ outWire)
      | none => e) eH =
    outs.foldl (fun e outWire =>
      match resolvePort sub inst outWire with
      | some p => updateEnv e p (outEnv₂ outWire)
      | none => e) eH := by
  induction outs generalizing eH with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    have h_hd := h_eq hd (List.Mem.head _)
    have h_tl : ∀ w ∈ tl, outEnv₁ w = outEnv₂ w :=
      fun w hw => h_eq w (List.Mem.tail _ hw)
    rw [h_hd]
    exact ih _ h_tl

/-- When every child in `parent.instances` is flattened by `flattenAllFuel reg sub k`
    and agrees with `evalHier reg (k + 1) sub` on its outputs, evaluating `parent`
    at fuel `k + 2` over `reg` equals evaluating `parent` at fuel `2` over
    `flattenRegistry reg k`. -/
theorem evalHier_eq_evalHier_flattenRegistry (reg : ModuleRegistry) (k : Nat) (parent : Circuit)
    (h_children_flat : ∀ inst ∈ parent.instances, ∀ nm sub,
      (flattenRegistry reg k).find? (fun p => p.1 == inst.moduleName) = some (nm, sub) →
      ChildFlatOK (flattenRegistry reg k) parent inst sub)
    (h_children_sound : ∀ inst ∈ parent.instances, ∀ nm sub,
      reg.find? (fun p => p.1 == inst.moduleName) = some (nm, sub) →
      ∀ inEnv, ∀ w ∈ sub.outputs,
        evalHier reg (k + 1) sub inEnv w = evalCircuit (flattenAllFuel reg sub k) inEnv w)
    (env : Env) :
    evalHier reg (k + 2) parent env = evalHier (flattenRegistry reg k) 2 parent env := by
  change Shoumei.evalGates (postGates reg parent)
      (parent.instances.foldl (applyInst reg (evalHier reg (k + 1)))
        (Shoumei.evalGates (preGates reg parent) env)) =
    Shoumei.evalGates (postGates (flattenRegistry reg k) parent)
      (parent.instances.foldl (applyInst (flattenRegistry reg k) (evalHier (flattenRegistry reg k) 1))
        (Shoumei.evalGates (preGates (flattenRegistry reg k) parent) env))
  simp only [preGates_flattenRegistry, postGates_flattenRegistry]
  congr 1
  have h_fold : ∀ (insts : List CircuitInstance),
      (∀ inst ∈ insts, inst ∈ parent.instances) →
      ∀ eH,
      insts.foldl (applyInst reg (evalHier reg (k + 1))) eH =
      insts.foldl (applyInst (flattenRegistry reg k) (evalHier (flattenRegistry reg k) 1)) eH := by
    intro insts h_sub eH
    induction insts generalizing eH with
    | nil => rfl
    | cons inst tl ih =>
      simp only [List.foldl_cons]
      have h_mem : inst ∈ parent.instances := h_sub inst (List.Mem.head _)
      have h_tl : ∀ i ∈ tl, i ∈ parent.instances :=
        fun i hi => h_sub i (List.Mem.tail _ hi)
      have h_step :
          applyInst reg (evalHier reg (k + 1)) eH inst =
          applyInst (flattenRegistry reg k) (evalHier (flattenRegistry reg k) 1) eH inst := by
        dsimp only [applyInst]
        rw [flattenRegistry_find?]
        match h_lookup : reg.find? (fun p => p.1 == inst.moduleName) with
        | none =>
          rw [h_lookup]
          rfl
        | some (nm, sub) =>
          rw [h_lookup]
          dsimp only [Option.map]
          rw [flattenAllFuel_outputs, subInputEnv_flattenAllFuel, resolvePort_flattenAllFuel]
          have h_lookup_flat :
              (flattenRegistry reg k).find? (fun p => p.1 == inst.moduleName) =
              some (nm, flattenAllFuel reg sub k) := by
            rw [flattenRegistry_find?, h_lookup]
            rfl
          have h_ok := h_children_flat inst h_mem nm (flattenAllFuel reg sub k) h_lookup_flat
          have h_flat_eval := evalHier_no_instances (flattenRegistry reg k) 0
            (flattenAllFuel reg sub k) h_ok.flat (subInputEnv sub inst eH)
          rw [h_flat_eval]
          exact foldl_propagate_congr sub.outputs sub inst
            (evalHier reg (k + 1) sub (subInputEnv sub inst eH))
            (evalCircuit (flattenAllFuel reg sub k) (subInputEnv sub inst eH))
            eH
            (h_children_sound inst h_mem nm sub h_lookup (subInputEnv sub inst eH))
      rw [h_step]
      exact ih h_tl _
  exact h_fold parent.instances (fun _ h => h) _

/-- Multi-level combinational flattener soundness: if every child of `parent`
    flattened with fuel `k` satisfies `ChildFlatOK` and agrees with `evalHier reg (k + 1)`
    on its outputs, then `evalHier reg (k + 2) parent` agrees with
    `evalCircuit (flattenAllFuel reg parent (k + 1))` on all parent outputs. -/
theorem flatten_sound_step (reg : ModuleRegistry) (k : Nat) (parent : Circuit)
    (h_wired : WellWired (flattenRegistry reg k) parent = true)
    (h_fresh : FlattenFresh (flattenRegistry reg k) parent)
    (h_children : ∀ inst ∈ parent.instances, ∀ nm sub,
      (flattenRegistry reg k).find? (fun p => p.1 == inst.moduleName) = some (nm, sub) →
      ChildFlatOK (flattenRegistry reg k) parent inst sub)
    (h_children_sound : ∀ inst ∈ parent.instances, ∀ nm sub,
      reg.find? (fun p => p.1 == inst.moduleName) = some (nm, sub) →
      ∀ inEnv, ∀ w ∈ sub.outputs,
        evalHier reg (k + 1) sub inEnv w = evalCircuit (flattenAllFuel reg sub k) inEnv w)
    (env : Env) :
    ∀ w ∈ parent.outputs,
      evalHier reg (k + 2) parent env w = evalCircuit (flattenAllFuel reg parent (k + 1)) env w := by
  intro w hw
  rw [evalHier_eq_evalHier_flattenRegistry reg k parent h_children h_children_sound env]
  rw [flattenAllFuel_succ_eq_depth1 reg parent k]
  exact flatten_sound_depth1 (flattenRegistry reg k) parent h_wired h_fresh h_children env w hw

/-! ## Sequential flattener soundness (`flatten_step_sound`) -/

theorem isDFF_false_of_isCombinational (gt : GateType) (h : gt.isCombinational = true) :
    gt.isDFF = false := by
  cases gt <;> simp_all [GateType.isCombinational, GateType.isDFF]

theorem evalCombGates_append (gs₁ gs₂ : List Gate) (env : Env) :
    evalCombGates (gs₁ ++ gs₂) env = evalCombGates gs₂ (evalCombGates gs₁ env) := by
  dsimp [evalCombGates]
  rw [List.foldl_append]

theorem evalCombGates_eq_evalGates (gs : List Gate)
    (h_comb : ∀ g ∈ gs, g.gateType.isCombinational = true) (env : Env) :
    evalCombGates gs env = Shoumei.evalGates gs env := by
  induction gs generalizing env with
  | nil => rfl
  | cons hd tl ih =>
    have h_hd := h_comb hd (List.Mem.head _)
    have h_tl : ∀ g ∈ tl, g.gateType.isCombinational = true :=
      fun g hg => h_comb g (List.Mem.tail _ hg)
    dsimp [evalCombGates, Shoumei.evalGates]
    rw [h_hd, if_pos rfl]
    exact ih h_tl _

theorem filter_isDFF_nil_of_comb (gs : List Gate)
    (h_comb : ∀ g ∈ gs, g.gateType.isCombinational = true) :
    gs.filter (fun g => g.gateType.isDFF) = [] := by
  induction gs with
  | nil => rfl
  | cons hd tl ih =>
    have h_hd := isDFF_false_of_isCombinational hd.gateType (h_comb hd (List.Mem.head _))
    have h_tl : ∀ g ∈ tl, g.gateType.isCombinational = true :=
      fun g hg => h_comb g (List.Mem.tail _ hg)
    dsimp [List.filter]
    rw [h_hd]
    exact ih h_tl

theorem getDFFOutputs_of_comb (c : Circuit)
    (h_comb : ∀ g ∈ c.gates, g.gateType.isCombinational = true) :
    getDFFOutputs c = [] := by
  dsimp [getDFFOutputs]
  rw [filter_isDFF_nil_of_comb c.gates h_comb]
  rfl

theorem filterMap_dff_nil_of_comb (gs : List Gate) (env : Env)
    (h_comb : ∀ g ∈ gs, g.gateType.isCombinational = true) :
    (gs.filterMap fun g =>
      if g.gateType.isDFF then some (g.output, evalDFF g env) else none) = [] := by
  induction gs with
  | nil => rfl
  | cons hd tl ih =>
    have h_hd := isDFF_false_of_isCombinational hd.gateType (h_comb hd (List.Mem.head _))
    have h_tl : ∀ g ∈ tl, g.gateType.isCombinational = true :=
      fun g hg => h_comb g (List.Mem.tail _ hg)
    dsimp [List.filterMap]
    rw [h_hd, if_neg Bool.false_ne_true]
    exact ih h_tl

theorem evalCycleSequential_of_comb (c : Circuit)
    (h_comb : ∀ g ∈ c.gates, g.gateType.isCombinational = true)
    (s : State) (env : Env) :
    evalCycleSequential c s env = (s, evalCircuit c env) := by
  dsimp [evalCycleSequential]
  rw [getDFFOutputs_of_comb c h_comb]
  have h_merge : mergeStateIntoEnv s env [] = env := by
    funext w
    simp [mergeStateIntoEnv]
  rw [h_merge]
  have h_comb_eq : (c.gates.foldl (fun env gate =>
      if gate.gateType.isCombinational then
        updateEnv env gate.output (evalGate gate env)
      else env) env) = evalCircuit c env :=
    evalCombGates_eq_evalGates c.gates h_comb env
  rw [h_comb_eq]
  rw [filterMap_dff_nil_of_comb c.gates (evalCircuit c env) h_comb]
  have h_upd : updateState s [] = s := by
    funext w
    simp [updateState]
  rw [h_upd]

theorem inline_comb_of_comb (sub : Circuit) (remap : Wire → Wire)
    (h_comb : ∀ g ∈ sub.gates, g.gateType.isCombinational = true) :
    ∀ g ∈ Circuit.inline sub remap, g.gateType.isCombinational = true := by
  intro g hg
  dsimp [Circuit.inline] at hg
  obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.mp hg
  exact h_comb g₀ hg₀

theorem inlined_comb_of_children_comb (reg : ModuleRegistry) (insts : List CircuitInstance)
    (h_sub_comb : ∀ inst ∈ insts, ∀ nm sub,
      reg.find? (fun p => p.1 == inst.moduleName) = some (nm, sub) →
      ∀ g ∈ sub.gates, g.gateType.isCombinational = true)
    (h_sub_flat : ∀ inst ∈ insts, ∀ nm sub,
      reg.find? (fun p => p.1 == inst.moduleName) = some (nm, sub) →
      sub.instances = []) :
    ∀ g ∈ (insts.flatMap fun inst =>
      match reg.find? (fun p => p.1 == inst.moduleName) with
      | some (_, subCircuit) =>
        Circuit.inline subCircuit (flattenRemap subCircuit inst)
      | none => []), g.gateType.isCombinational = true := by
  intro g hg
  obtain ⟨inst, h_inst, hg_inst⟩ := List.mem_flatMap.mp hg
  have _ := h_sub_flat
  match h_lookup : reg.find? (fun p => p.1 == inst.moduleName) with
  | none =>
    rw [h_lookup] at hg_inst
    cases hg_inst
  | some (nm, sub) =>
    rw [h_lookup] at hg_inst
    exact inline_comb_of_comb sub (flattenRemap sub inst)
      (h_sub_comb inst h_inst nm sub h_lookup) g hg_inst

theorem hierStepFold_comb_children (reg : ModuleRegistry) (parent : Circuit)
    (h_children : ∀ inst ∈ parent.instances, ∀ nm sub,
      reg.find? (fun p => p.1 == inst.moduleName) = some (nm, sub) →
      ChildFlatOK reg parent inst sub)
    (h_sub_comb : ∀ inst ∈ parent.instances, ∀ nm sub,
      reg.find? (fun p => p.1 == inst.moduleName) = some (nm, sub) →
      ∀ g ∈ sub.gates, g.gateType.isCombinational = true)
    (s : State) (insts : List CircuitInstance)
    (h_insts : ∀ inst ∈ insts, inst ∈ parent.instances)
    (accUpdates : List (Wire × Bool)) (eH : Env) :
    insts.foldl (hierStepFold (fun _ sub => stepHier reg 1 sub) reg 1 s) (accUpdates, eH) =
    (accUpdates, insts.foldl (applyInst reg (evalHier reg 1)) eH) := by
  induction insts generalizing accUpdates eH with
  | nil => rfl
  | cons inst tl ih =>
    simp only [List.foldl_cons]
    have h_mem := h_insts inst (List.Mem.head _)
    have h_tl : ∀ i ∈ tl, i ∈ parent.instances :=
      fun i hi => h_insts i (List.Mem.tail _ hi)
    have h_step :
        hierStepFold (fun _ sub => stepHier reg 1 sub) reg 1 s (accUpdates, eH) inst =
        (accUpdates, applyInst reg (evalHier reg 1) eH inst) := by
      dsimp only [hierStepFold, applyInst]
      match h_lookup : reg.find? (fun p => p.1 == inst.moduleName) with
      | none =>
        rw [h_lookup]
      | some (nm, sub) =>
        rw [h_lookup]
        dsimp only
        have h_ok := h_children inst h_mem nm sub h_lookup
        have h_comb := h_sub_comb inst h_mem nm sub h_lookup
        have h_step_sub : stepHier reg 1 sub (fun w => s (instScope inst.instName w)) (subInputEnv sub inst eH) =
            (fun w => s (instScope inst.instName w), evalCircuit sub (subInputEnv sub inst eH)) := by
          rw [stepHier_no_instances reg 0 sub h_ok.flat]
          exact evalCycleSequential_of_comb sub h_comb _ _
        have h_eval_sub : evalHier reg 1 sub (subInputEnv sub inst eH) =
            evalCircuit sub (subInputEnv sub inst eH) :=
          evalHier_no_instances reg 0 sub h_ok.flat (subInputEnv sub inst eH)
        have h_dffs : allDFFWires reg 1 sub = [] := by
          rw [allDFFWires_nil reg 1 sub h_ok.flat]
          exact getDFFOutputs_of_comb sub h_comb
        rw [h_step_sub, h_eval_sub, h_dffs]
        simp
    rw [h_step]
    exact ih h_tl accUpdates _

theorem evalCombGates_congr_parent (c : Circuit) (gs : List Gate)
    (h_gs : ∀ g ∈ gs, g ∈ c.gates) (e₁ e₂ : Env)
    (h_agree : AgreeOn (parentWires c) e₁ e₂) :
    AgreeOn (parentWires c) (evalCombGates gs e₁) (evalCombGates gs e₂) := by
  induction gs generalizing e₁ e₂ with
  | nil => exact h_agree
  | cons g rest ih =>
    have hg_mem : g ∈ c.gates := h_gs g (List.Mem.head _)
    have h_rest : ∀ g' ∈ rest, g' ∈ c.gates :=
      fun g' hg' => h_gs g' (List.Mem.tail _ hg')
    dsimp [evalCombGates]
    cases h_comb : g.gateType.isCombinational with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact ih h_rest e₁ e₂ h_agree
    | true =>
      simp only [↓reduceIte]
      have h_inputs_agree : ∀ w ∈ g.inputs, e₁ w = e₂ w :=
        fun w hw => h_agree w (gate_input_mem_parentWires c g hg_mem w hw)
      have h_eval : evalGate g e₁ = evalGate g e₂ :=
        evalGate_congr_inputs g e₁ e₂ h_inputs_agree
      have h_step_agree : AgreeOn (parentWires c)
          (updateEnv e₁ g.output (evalGate g e₁))
          (updateEnv e₂ g.output (evalGate g e₂)) := by
        intro w hw
        by_cases h_eq : w = g.output
        · subst h_eq
          simp [updateEnv, wire_beq_self, h_eval]
        · simp [updateEnv, wire_beq_ne w g.output h_eq, h_agree w hw]
      exact ih h_rest _ _ h_step_agree

theorem evalDFF_congr_inputs (g : Gate) (e₁ e₂ : Env)
    (h : ∀ w ∈ g.inputs, e₁ w = e₂ w) : evalDFF g e₁ = evalDFF g e₂ := by
  cases g with
  | mk gateType inputs output =>
    cases gateType with
    | DFF => match inputs with
      | [d, clk, reset] => simp_all [evalDFF]
      | [] => simp [evalDFF]
      | [_] => simp [evalDFF]
      | [_, _] => simp [evalDFF]
      | _ :: _ :: _ :: _ :: _ => simp [evalDFF]
    | DFF_SET => match inputs with
      | [d, clk, reset] => simp_all [evalDFF]
      | [] => simp [evalDFF]
      | [_] => simp [evalDFF]
      | [_, _] => simp [evalDFF]
      | _ :: _ :: _ :: _ :: _ => simp [evalDFF]
    | _ => simp [evalDFF]

theorem filter_postGates_isDFF (reg : ModuleRegistry) (parent : Circuit)
    (h_pre_comb : ∀ g ∈ preGates reg parent, g.gateType.isCombinational = true) :
    (postGates reg parent).filter (fun g => g.gateType.isDFF) =
    parent.gates.filter (fun g => g.gateType.isDFF) := by
  dsimp [postGates]
  rw [List.filter_filter]
  apply List.filter_congr
  intro g hg
  cases h_dff : g.gateType.isDFF with
  | false => simp
  | true =>
    cases h_in : (faninConeWires parent.gates (instanceInputWires reg parent)).contains g.output with
    | false => rfl
    | true =>
      have hg_pre : g ∈ preGates reg parent := by
        dsimp [preGates]
        exact List.mem_filter.mpr ⟨hg, h_in⟩
      have h_false := isDFF_false_of_isCombinational g.gateType (h_pre_comb g hg_pre)
      rw [h_dff] at h_false
      cases h_false

theorem getDFFOutputs_flatten_depth1 (reg : ModuleRegistry) (parent : Circuit)
    (h_children : ∀ inst ∈ parent.instances, ∀ nm sub,
      reg.find? (fun p => p.1 == inst.moduleName) = some (nm, sub) →
      ChildFlatOK reg parent inst sub)
    (h_pre_comb : ∀ g ∈ preGates reg parent, g.gateType.isCombinational = true)
    (h_sub_comb : ∀ inst ∈ parent.instances, ∀ nm sub,
      reg.find? (fun p => p.1 == inst.moduleName) = some (nm, sub) →
      ∀ g ∈ sub.gates, g.gateType.isCombinational = true) :
    getDFFOutputs (flattenAllFuel reg parent 1) = getDFFOutputs parent := by
  dsimp [getDFFOutputs, flattenAllFuel]
  rw [List.filter_append, List.filter_append]
  have h_pre_nil := filter_isDFF_nil_of_comb (preGates reg parent) h_pre_comb
  have h_inl_comb := inlined_comb_of_children_comb reg parent.instances h_sub_comb
    (fun inst h_m nm sub h_l => (h_children inst h_m nm sub h_l).flat)
  have h_inl_nil := filter_isDFF_nil_of_comb _ h_inl_comb
  erw [h_pre_nil, h_inl_nil, List.nil_append]
  rw [filter_postGates_isDFF reg parent h_pre_comb]

theorem filterMap_postGates_isDFF (reg : ModuleRegistry) (parent : Circuit)
    (h_pre_comb : ∀ g ∈ preGates reg parent, g.gateType.isCombinational = true)
    (e₁ e₂ : Env) (h_agree : AgreeOn (parentWires parent) e₁ e₂) :
    (parent.gates.filterMap fun g =>
      if g.gateType.isDFF then some (g.output, evalDFF g e₁) else none) =
    ((postGates reg parent).filterMap fun g =>
      if g.gateType.isDFF then some (g.output, evalDFF g e₂) else none) := by
  have h_pre : ∀ g ∈ parent.gates, g.gateType.isDFF = true →
      (faninConeWires parent.gates (instanceInputWires reg parent)).contains g.output = false := by
    intro g hg h_dff
    cases h_in : (faninConeWires parent.gates (instanceInputWires reg parent)).contains g.output with
    | false => rfl
    | true =>
      have hg_pre : g ∈ preGates reg parent := List.mem_filter.mpr ⟨hg, h_in⟩
      have h_false := isDFF_false_of_isCombinational g.gateType (h_pre_comb g hg_pre)
      rw [h_dff] at h_false
      cases h_false
  dsimp [postGates]
  have h_gen : ∀ (gs : List Gate), (∀ g ∈ gs, g ∈ parent.gates) →
      (gs.filterMap fun g =>
        if g.gateType.isDFF then some (g.output, evalDFF g e₁) else none) =
      ((gs.filter fun g => !(faninConeWires parent.gates (instanceInputWires reg parent)).contains g.output).filterMap fun g =>
        if g.gateType.isDFF then some (g.output, evalDFF g e₂) else none) := by
    intro gs h_sub
    induction gs with
    | nil => rfl
    | cons hd tl ih =>
      have hd_mem := h_sub hd (List.Mem.head _)
      have h_tl : ∀ g ∈ tl, g ∈ parent.gates := fun g hg => h_sub g (List.Mem.tail _ hg)
      dsimp [List.filter, List.filterMap]
      cases h_dff : hd.gateType.isDFF with
      | false =>
        cases !(faninConeWires parent.gates (instanceInputWires reg parent)).contains hd.output <;>
          simp [h_dff, ih h_tl]
      | true =>
        have h_not_in := h_pre hd hd_mem h_dff
        rw [h_not_in]
        dsimp [List.filterMap]
        have h_ev : evalDFF hd e₁ = evalDFF hd e₂ :=
          evalDFF_congr_inputs hd e₁ e₂ (fun w hw => h_agree w (gate_input_mem_parentWires parent hd hd_mem w hw))
        rw [h_ev, ih h_tl]
        simp [h_dff]
  exact h_gen parent.gates (fun _ h => h)

theorem mem_of_contains_eq_true (l : List Wire) (w : Wire)
    (h : l.contains w = true) : w ∈ l := by
  induction l with
  | nil => cases h
  | cons hd tl ih =>
    simp only [List.contains, List.elem] at h
    cases h_eq : (w == hd) with
    | true =>
      rw [wire_beq_eq w hd h_eq]
      exact List.Mem.head _
    | false =>
      rw [h_eq] at h
      exact List.Mem.tail _ (ih h)

/-- Depth-1 sequential flattener soundness (`flatten_step_sound`):
    Given state correspondence `StateCorr reg parent s_hier s_flat`, stepping
    `parent` hierarchically (`stepHier reg 2 parent`) and stepping its flattened
    circuit (`evalCycleSequential (flattenAllFuel reg parent 1)`) produce identical
    outputs on all parent output wires and preserve `StateCorr` into the next cycle. -/
theorem flatten_step_sound (reg : ModuleRegistry) (parent : Circuit)
    (h_wired : WellWired reg parent = true)
    (h_fresh : FlattenFresh reg parent)
    (h_children : ∀ inst ∈ parent.instances, ∀ nm sub,
      reg.find? (fun p => p.1 == inst.moduleName) = some (nm, sub) →
      ChildFlatOK reg parent inst sub)
    (h_pre_comb : ∀ g ∈ preGates reg parent, g.gateType.isCombinational = true)
    (h_sub_comb : ∀ inst ∈ parent.instances, ∀ nm sub,
      reg.find? (fun p => p.1 == inst.moduleName) = some (nm, sub) →
      ∀ g ∈ sub.gates, g.gateType.isCombinational = true)
    (s_hier s_flat : State)
    (h_corr : StateCorr reg parent s_hier s_flat)
    (inputEnv : Env) :
    (∀ w ∈ parent.outputs,
      (stepHier reg 2 parent s_hier inputEnv).2 w =
      (evalCycleSequential (flattenAllFuel reg parent 1) s_flat inputEnv).2 w) ∧
    StateCorr reg parent
      (stepHier reg 2 parent s_hier inputEnv).1
      (evalCycleSequential (flattenAllFuel reg parent 1) s_flat inputEnv).1 := by
  have h_dffs_eq := getDFFOutputs_flatten_depth1 reg parent h_children h_pre_comb h_sub_comb
  have h_merge_eq :
      mergeStateIntoEnv s_flat inputEnv (getDFFOutputs (flattenAllFuel reg parent 1)) =
      mergeStateIntoEnv s_hier inputEnv (getDFFOutputs parent) := by
    rw [h_dffs_eq]
    funext w
    dsimp [mergeStateIntoEnv]
    cases h_c : (getDFFOutputs parent).contains w with
    | false => rfl
    | true =>
      exact h_corr.1 w (mem_of_contains_eq_true (getDFFOutputs parent) w h_c)
  let env₀ := mergeStateIntoEnv s_hier inputEnv (getDFFOutputs parent)
  let env₁ := evalCombGates (preGates reg parent) env₀
  have h_fold_hier := hierStepFold_comb_children reg parent h_children h_sub_comb
    s_hier parent.instances (fun _ h => h) [] env₁
  have h_inl_comb := inlined_comb_of_children_comb reg parent.instances h_sub_comb
    (fun inst h_m nm sub h_l => (h_children inst h_m nm sub h_l).flat)
  have h_inl_eval := evalCombGates_eq_evalGates _ h_inl_comb env₁
  have h_inlined_fold := evalGates_flatMap_foldl (fun inst =>
      match reg.find? (fun p => p.1 == inst.moduleName) with
      | some (_, subCircuit) => Circuit.inline subCircuit (flattenRemap subCircuit inst)
      | none => []) parent.instances env₁
  have h_step_eq : (fun env inst => match reg.find? (fun p => p.1 == inst.moduleName) with
      | some (_, subCircuit) => Shoumei.evalGates (Circuit.inline subCircuit (flattenRemap subCircuit inst)) env
      | none => env)
    = (fun env inst => Shoumei.evalGates (match reg.find? (fun p => p.1 == inst.moduleName) with
      | some (_, subCircuit) => Circuit.inline subCircuit (flattenRemap subCircuit inst)
      | none => []) env) := by
    ext env inst
    match h_find : reg.find? (fun p => p.1 == inst.moduleName) with
    | some (nm, subCircuit) => simp only [h_find]
    | none => simp only [h_find, Shoumei.evalGates, List.foldl_nil]
  have h_mid_agree : AgreeOn (parentWires parent)
      (parent.instances.foldl (applyInst reg (evalHier reg 1)) env₁)
      (evalCombGates (parent.instances.flatMap fun inst =>
        match reg.find? (fun p => p.1 == inst.moduleName) with
        | some (_, subCircuit) => Circuit.inline subCircuit (flattenRemap subCircuit inst)
        | none => []) env₁) := by
    rw [h_inl_eval, h_inlined_fold, ← h_step_eq]
    exact foldl_instances_agree reg parent h_wired h_fresh h_children
      parent.instances (fun _ h => h) env₁ env₁ (fun _ _ => rfl)
  have h_post_sub : ∀ g ∈ postGates reg parent, g ∈ parent.gates := by
    intro g hg
    exact (List.mem_filter.mp hg).1
  have h_comb_agree : AgreeOn (parentWires parent)
      (evalCombGates (postGates reg parent)
        (parent.instances.foldl (applyInst reg (evalHier reg 1)) env₁))
      (evalCombGates (postGates reg parent)
        (evalCombGates (parent.instances.flatMap fun inst =>
          match reg.find? (fun p => p.1 == inst.moduleName) with
          | some (_, subCircuit) => Circuit.inline subCircuit (flattenRemap subCircuit inst)
          | none => []) env₁)) :=
    evalCombGates_congr_parent parent (postGates reg parent) h_post_sub _ _ h_mid_agree
  have h_comb_flat_eq :
      (evalCycleSequential (flattenAllFuel reg parent 1) s_flat inputEnv).2 =
      evalCombGates (postGates reg parent)
        (evalCombGates (parent.instances.flatMap fun inst =>
          match reg.find? (fun p => p.1 == inst.moduleName) with
          | some (_, subCircuit) => Circuit.inline subCircuit (flattenRemap subCircuit inst)
          | none => []) env₁) := by
    dsimp [evalCycleSequential]
    rw [h_merge_eq]
    change evalCombGates ((flattenAllFuel reg parent 1).gates) env₀ = _
    dsimp [flattenAllFuel]
    rw [evalCombGates_append, evalCombGates_append]
    rfl
  have h_comb_hier_eq :
      (stepHier reg 2 parent s_hier inputEnv).2 =
      evalCombGates (postGates reg parent)
        (parent.instances.foldl (applyInst reg (evalHier reg 1)) env₁) := by
    dsimp [stepHier]
    change (let p := parent.instances.foldl (hierStepFold (fun _ sub => stepHier reg 1 sub) reg 1 s_hier) ([], env₁);
            evalCombGates (postGates reg parent) p.2) = _
    rw [h_fold_hier]
  refine ⟨?_, ?_⟩
  · intro w hw
    rw [h_comb_hier_eq, h_comb_flat_eq]
    exact h_comb_agree w (output_mem_parentWires parent w hw)
  · have h_upd_eq :
        ((flattenAllFuel reg parent 1).gates.filterMap fun g =>
          if g.gateType.isDFF then
            some (g.output, evalDFF g (evalCycleSequential (flattenAllFuel reg parent 1) s_flat inputEnv).2)
          else none) =
        (parent.gates.filterMap fun g =>
          if g.gateType.isDFF then
            some (g.output, evalDFF g (stepHier reg 2 parent s_hier inputEnv).2)
          else none) := by
      change (((preGates reg parent ++
          (parent.instances.flatMap fun inst =>
            match reg.find? (fun p => p.1 == inst.moduleName) with
            | some (_, subCircuit) => Circuit.inline subCircuit (flattenRemap subCircuit inst)
            | none => []) ++
          postGates reg parent).filterMap fun g =>
            if g.gateType.isDFF then
              some (g.output, evalDFF g (evalCycleSequential (flattenAllFuel reg parent 1) s_flat inputEnv).2)
            else none) = _)
      rw [List.filterMap_append, List.filterMap_append]
      have h_pre_fm := filterMap_dff_nil_of_comb (preGates reg parent)
        (evalCycleSequential (flattenAllFuel reg parent 1) s_flat inputEnv).2 h_pre_comb
      have h_inl_fm := filterMap_dff_nil_of_comb _
        (evalCycleSequential (flattenAllFuel reg parent 1) s_flat inputEnv).2 h_inl_comb
      rw [h_pre_fm, h_inl_fm, List.nil_append, List.nil_append]
      rw [h_comb_hier_eq, h_comb_flat_eq]
      exact (filterMap_postGates_isDFF reg parent h_pre_comb _ _ h_comb_agree).symm
    have h_state_hier_eq :
        (stepHier reg 2 parent s_hier inputEnv).1 =
        updateState s_hier (parent.gates.filterMap fun g =>
          if g.gateType.isDFF then
            some (g.output, evalDFF g (stepHier reg 2 parent s_hier inputEnv).2)
          else none) := by
      rw [h_comb_hier_eq]
      change (let p := parent.instances.foldl (hierStepFold (fun _ sub => stepHier reg 1 sub) reg 1 s_hier) ([], env₁);
              updateState s_hier ((parent.gates.filterMap fun g =>
                if g.gateType.isDFF then
                  some (g.output, evalDFF g (evalCombGates (postGates reg parent) p.2))
                else none) ++ p.1)) = _
      rw [h_fold_hier]
      dsimp only
      rw [List.append_nil]
    have h_state_flat_eq :
        (evalCycleSequential (flattenAllFuel reg parent 1) s_flat inputEnv).1 =
        updateState s_flat (parent.gates.filterMap fun g =>
          if g.gateType.isDFF then
            some (g.output, evalDFF g (stepHier reg 2 parent s_hier inputEnv).2)
          else none) := by
      dsimp [evalCycleSequential]
      change updateState s_flat ((flattenAllFuel reg parent 1).gates.filterMap fun g =>
        if g.gateType.isDFF then
          some (g.output, evalDFF g (evalCycleSequential (flattenAllFuel reg parent 1) s_flat inputEnv).2)
        else none) = _
      rw [h_upd_eq]
    rw [h_state_hier_eq, h_state_flat_eq]
    refine ⟨?_, ?_⟩
    · intro w hw
      dsimp [updateState]
      cases (parent.gates.filterMap fun g =>
        if g.gateType.isDFF then
          some (g.output, evalDFF g (stepHier reg 2 parent s_hier inputEnv).2)
        else none).find? (fun p => p.1 == w) with
      | some p => rfl
      | none => exact h_corr.1 w hw
    · intro inst h_inst nm sub h_lookup w hw
      have h_empty := getDFFOutputs_of_comb sub (h_sub_comb inst h_inst nm sub h_lookup)
      rw [h_empty] at hw
      cases hw

end Shoumei.Reflection
