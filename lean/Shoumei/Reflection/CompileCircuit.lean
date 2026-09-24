/-
Reflection/CompileCircuit.lean - Circuit compilation with correctness proof

`compileCircuit` folds `compileGate` over all gates, mirroring `evalCircuit`.
`flattenAllFuel` inlines hierarchical instances with the canonical port
resolution (`resolvePort`, shared with the emitter and `evalHier`), so the
flattened circuit evaluates like the hierarchical one (`flatten_sound`).
-/

import Shoumei.Reflection.CompileGate
import Shoumei.DSL.PortResolve
import Shoumei.Semantics.Hierarchical

namespace Shoumei.Reflection

open Shoumei
open Shoumei.DSL.PortResolve
open Shoumei.Semantics.Hierarchical

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
  simp [evalGates, evalCircuit, Shoumei.evalGates]

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

/-! ## Circuit Flattening

Recursively inline all `CircuitInstance`s to produce a flat gate-only circuit.
Port bindings resolve with the canonical `resolvePort` — the same rule the
emitter and `evalHier` use — so the flattener cannot mis-wire families whose
port keys use brackets or bare suffixes. Wires with no binding are scoped
under the instance name (with the enumeration index for sibling uniqueness),
so inlined state lines up with `stepHier`'s `instScope` threading. Gate
ordering mirrors `evalHier`: pre-gates, inlined instances, post-gates. This
allows `compileCircuit` (which only processes gates) to evaluate hierarchical
circuits correctly (`flatten_sound` below).
-/

/-- Remap a submodule wire into the parent scope: bound ports resolve to
    their parent wire, everything else to the instance-scoped name (the same
    scoping `stepHier` threads state under). Scoped names contain `/`, which
    emitted wires never do, so they cannot collide with parent wires;
    sibling instances must have distinct names (`FlattenNodup`). -/
def flattenRemap (sub : Circuit) (inst : CircuitInstance) : Wire → Wire :=
  fun w =>
    match resolvePort sub inst w with
    | some pw => pw
    | none => instScope inst.instName w

/-- Sibling instances have distinct names, so scoped wires cannot alias
    across instances. (Duplicate instance names are illegal SystemVerilog,
    so every emitted circuit satisfies this.) -/
def FlattenNodup (c : Circuit) : Prop :=
  (c.instances.map (fun inst => inst.instName)).Nodup

/-- Flatten with explicit recursion depth bound.
    Fully inlines every instance whose module resolves in `registry`, provided
    fuel covers the instance depth (see `flatten_sound`); returns the circuit
    unchanged if fuel runs out. -/
def flattenAllFuel (registry : ModuleRegistry) (c : Circuit) (fuel : Nat) : Circuit :=
  match fuel with
  | 0 => c
  | fuel + 1 =>
    let pre := preGates registry c
    let post := postGates registry c
    let inlined := c.instances.flatMap fun inst =>
      match registry.find? (fun p => p.1 == inst.moduleName) with
      | some (_, subCircuit) =>
        let flat := flattenAllFuel registry subCircuit fuel
        Circuit.inline flat (flattenRemap subCircuit inst)
      | none => []
    { c with gates := pre ++ inlined ++ post, instances := [] }

/-! ## Flattener soundness (Phase 4: `flatten_sound`)

Evaluating the flattened circuit agrees with hierarchical evaluation, given
well-formed wiring, enough fuel, and fresh scoped names. The schedule is
shared by construction (`preGates` / `postGates` / `resolvePort` on both
sides); the proof work is the per-instance correspondence between inlined
remapped gates and `applyInst` / `hierStepFold`.
-/

/-- Every wire a parent circuit can observe: inputs, outputs, gate wires. -/
def parentWires (c : Circuit) : List Wire :=
  c.inputs ++ c.outputs ++ c.gates.flatMap (fun g => g.output :: g.inputs)

/-- Every wire of a submodule. -/
def subWires (sub : Circuit) : List Wire :=
  sub.inputs ++ sub.outputs ++ sub.gates.flatMap (fun g => g.output :: g.inputs)

/-- Scoped remapped names miss every parent wire unless bound: a remap hit on
    a parent wire always comes from the port binding. -/
def FlattenFresh (reg : ModuleRegistry) (c : Circuit) : Prop :=
  ∀ inst ∈ c.instances, ∀ (nm : String) (sub : Circuit),
    reg.find? (fun p => p.1 == inst.moduleName) = some (nm, sub) →
    ∀ w ∈ subWires sub, ∀ pw ∈ parentWires c,
      flattenRemap sub inst w = pw → resolvePort sub inst w = some pw

/-- Remapping is injective on submodule wires: no two distinct sub wires
    share a parent wire. (Absent in every emitted hierarchy; stating it keeps
    the simulation step case-free.) -/
def RemapInj (sub : Circuit) (inst : CircuitInstance) : Prop :=
  ∀ w₁ ∈ subWires sub, ∀ w₂ ∈ subWires sub,
    flattenRemap sub inst w₁ = flattenRemap sub inst w₂ → w₁ = w₂

/-- Boolean check backing `RemapInj`. -/
def remapInjCheck (sub : Circuit) (inst : CircuitInstance) : Bool :=
  (subWires sub).all fun w₁ =>
    (subWires sub).all fun w₂ =>
      decide (flattenRemap sub inst w₁ ≠ flattenRemap sub inst w₂ ∨ w₁ = w₂)

/-- `remapInjCheck` implies `RemapInj`. -/
theorem RemapInj_of_check (sub : Circuit) (inst : CircuitInstance)
    (h : remapInjCheck sub inst = true) : RemapInj sub inst := by
  intro w₁ h₁ w₂ h₂ h_eq
  have h1 := (List.all_eq_true.mp h) w₁ h₁
  have h2 := (List.all_eq_true.mp h1) w₂ h₂
  exact (of_decide_eq_true h2).resolve_left (fun h_ne => absurd h_eq h_ne)

/-- `any`-true implies membership (manual bridge using `wire_beq_eq`). -/
theorem mem_of_any_eq_true (l : List Wire) (w : Wire)
    (h : l.any (· == w) = true) : w ∈ l := by
  rw [List.any_eq_true] at h
  obtain ⟨x, h_mem, h_beq⟩ := h
  have h_eq : x = w := wire_beq_eq _ _ h_beq
  subst h_eq
  exact h_mem

structure SubWf (sub : Circuit) : Prop where
  reads : ∀ g ∈ sub.gates, ∀ w ∈ g.inputs,
    w ∈ sub.inputs ∨ w ∈ sub.gates.map (fun g => g.output)
  out : ∀ w ∈ sub.outputs,
    w ∈ sub.inputs ∨ w ∈ sub.gates.map (fun g => g.output)
  src : ∀ w ∈ sub.inputs, w ∉ sub.gates.map (fun g => g.output)

/-- Boolean check backing `SubWf`. -/
def subWfCheck (sub : Circuit) : Bool :=
  (sub.gates.all fun g =>
    g.inputs.all fun w =>
      decide ((sub.inputs.any (· == w)) = true ∨
              ((sub.gates.map (fun g => g.output)).any (· == w)) = true))
  && (sub.outputs.all fun w =>
      decide ((sub.inputs.any (· == w)) = true ∨
              ((sub.gates.map (fun g => g.output)).any (· == w)) = true))
  && (sub.inputs.all fun w =>
      decide (((sub.gates.map (fun g => g.output)).any (· == w)) = false))

/-- `subWfCheck` implies `SubWf`. -/
theorem SubWf_of_check (sub : Circuit) (h : subWfCheck sub = true) : SubWf sub := by
  dsimp [subWfCheck] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h_reads, h_out⟩, h_src⟩ := h
  refine ⟨fun g h_g w h_w => ?_, fun w h_w => ?_, fun w h_w h_con => ?_⟩
  · have h1 := (List.all_eq_true.mp h_reads) g h_g
    have h2 := (List.all_eq_true.mp h1) w h_w
    rcases of_decide_eq_true h2 with h_c | h_c
    · exact Or.inl (mem_of_any_eq_true _ _ h_c)
    · exact Or.inr (mem_of_any_eq_true _ _ h_c)
  · have h1 := (List.all_eq_true.mp h_out) w h_w
    rcases of_decide_eq_true h1 with h_c | h_c
    · exact Or.inl (mem_of_any_eq_true _ _ h_c)
    · exact Or.inr (mem_of_any_eq_true _ _ h_c)
  · have h1 := (List.all_eq_true.mp h_src) w h_w
    have h_false := of_decide_eq_true h1
    obtain ⟨g, h_g, h_eq⟩ := List.mem_map.mp h_con
    have h_true : ((sub.gates.map (fun g => g.output)).any (· == w)) = true := by
      rw [List.any_eq_true]
      exact ⟨g.output, List.mem_map.mpr ⟨g, h_g, rfl⟩,
        by rw [h_eq]; exact wire_beq_self _⟩
    rw [h_false] at h_true
    exact Bool.false_ne_true h_true

/-- One topo-check step: conjoin the reads check, snoc the driven output. -/
def topoStep (inputs : List Wire) (acc : Bool × List Wire) (g : Gate) :
    Bool × List Wire :=
  (acc.1 && g.inputs.all fun w =>
    decide ((inputs.any (· == w)) = true ∨
            ((acc.2.any (· == w)) = true)),
   acc.2 ++ [g.output])

/-- Topologically ordered gates: every gate's reads come from primary inputs
    or strictly earlier gates. -/
def TopoOrdered (sub : Circuit) : Prop :=
  ∀ (pre : List Gate) (g : Gate) (suf : List Gate),
    sub.gates = pre ++ g :: suf →
    ∀ w ∈ g.inputs, w ∈ sub.inputs ∨ w ∈ pre.map (fun g => g.output)

/-- Boolean check backing `TopoOrdered`: single pass threading outputs-so-far. -/
def topoCheck (sub : Circuit) : Bool :=
  (sub.gates.foldl (topoStep sub.inputs) (true, [])).1

/-- The ok-component only decreases: a true total implies a true prefix. -/
theorem topoStep_ok_mono (rest : List Gate) (inputs : List Wire)
    (ok : Bool) (outs : List Wire)
    (h : ((rest.foldl (topoStep inputs) (ok, outs)).1 = true)) : ok = true := by
  induction rest generalizing ok outs with
  | nil =>
    simpa using h
  | cons hd tl ih =>
    have h_step : ((hd :: tl).foldl (topoStep inputs) (ok, outs))
        = (tl.foldl (topoStep inputs)
            ((ok && hd.inputs.all fun w =>
              decide ((inputs.any (· == w)) = true ∨
                      ((outs.any (· == w)) = true)),
             outs ++ [hd.output]))) := by
      simp only [List.foldl_cons, topoStep]
    rw [h_step] at h
    have h_ih := ih _ _ h
    simp only [Bool.and_eq_true] at h_ih
    exact h_ih.1

/-- Fold accumulation: outputs-so-far is exactly the mapped prefix. -/
theorem topoFold_accum (gs : List Gate) (inputs : List Wire)
    (ok : Bool) (outs : List Wire) :
    ((gs.foldl (topoStep inputs) (ok, outs)).2
      = outs ++ gs.map (fun g => g.output)) := by
  induction gs generalizing ok outs with
  | nil =>
    simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, topoStep, List.map_cons]
    rw [ih]
    simp [List.append_assoc]

/-- `topoCheck` implies `TopoOrdered`. -/
theorem TopoOrdered_of_check (sub : Circuit)
    (h : topoCheck sub = true) : TopoOrdered sub := by
  intro pre g suf h_split w h_w
  dsimp [topoCheck] at h
  rw [h_split] at h
  have h_app : ((pre ++ g :: suf).foldl (topoStep sub.inputs) (true, []))
      = ((g :: suf).foldl (topoStep sub.inputs)
          (pre.foldl (topoStep sub.inputs) (true, []))) := by
    simp only [List.foldl_append]
  rw [h_app] at h
  match hP : pre.foldl (topoStep sub.inputs) (true, []) with
  | (ok_pre, outs_pre) =>
    have h_g_step : ((g :: suf).foldl (topoStep sub.inputs) (ok_pre, outs_pre))
        = (suf.foldl (topoStep sub.inputs)
            ((ok_pre && g.inputs.all fun w =>
              decide ((sub.inputs.any (· == w)) = true ∨
                      ((outs_pre.any (· == w)) = true)),
             outs_pre ++ [g.output]))) := by
      simp only [List.foldl_cons, topoStep]
    rw [hP] at h
    rw [h_g_step] at h
    have h_mono := topoStep_ok_mono suf sub.inputs _ _ h
    simp only [Bool.and_eq_true] at h_mono
    have h_check := h_mono.2
    have h1 := (List.all_eq_true.mp h_check) w h_w
    have h2 := of_decide_eq_true h1
    rcases h2 with h_c | h_c
    · exact Or.inl (mem_of_any_eq_true _ _ h_c)
    · have h_outs_eq : outs_pre = pre.map (fun g => g.output) := by
        have h2 := topoFold_accum pre sub.inputs true []
        rw [hP] at h2
        simpa using h2
      have h_mem : w ∈ outs_pre := mem_of_any_eq_true _ _ h_c
      rw [← h_outs_eq]
      exact Or.inr h_mem

/-- Per-instance flattening obligations bundled: flat child, well-formed
    reads, topological ordering, injective remap, bound wires in parent, ports only
    inputs/outputs. (Freshness comes from parent-level `FlattenFresh`.) -/
structure ChildFlatOK (reg : ModuleRegistry) (parent : Circuit)
    (inst : CircuitInstance) (sub : Circuit) : Prop where
  flat : sub.instances = []
  wf : SubWf sub
  topo : TopoOrdered sub
  inj : RemapInj sub inst
  bound : ∀ w ∈ sub.inputs ++ sub.outputs, ∀ pw,
    resolvePort sub inst w = some pw → pw ∈ parentWires parent
  ports : ∀ w ∈ subWires sub, ∀ pw,
    resolvePort sub inst w = some pw → w ∈ sub.inputs ∨ w ∈ sub.outputs
  outnodup : sub.outputs.Nodup

/-- Boolean check backing per-instance obligations across a parent. -/
def childrenOKCheck (reg : ModuleRegistry) (parent : Circuit) : Bool :=
  parent.instances.all fun inst =>
    match reg.find? (fun p => p.1 == inst.moduleName) with
    | none => true
    | some (_, sub) =>
      decide (sub.instances.length = 0)
      && subWfCheck sub
      && topoCheck sub
      && remapInjCheck sub inst
      && ((sub.inputs ++ sub.outputs).all fun w =>
        match resolvePort sub inst w with
        | none => true
        | some pw => parentWires parent |>.any (· == pw))
      && ((subWires sub).all fun w =>
        match resolvePort sub inst w with
        | none => true
        | some _ => ((sub.inputs.any (· == w)) || (sub.outputs.any (· == w))))
      && decide (sub.outputs.Nodup)

/-- `childrenOKCheck` implies per-instance obligations. -/
theorem ChildrenOK_of_check (reg : ModuleRegistry) (parent : Circuit)
    (h : childrenOKCheck reg parent = true) :
    ∀ inst ∈ parent.instances, ∀ (nm : String) (sub : Circuit),
      reg.find? (fun p => p.1 == inst.moduleName) = some (nm, sub) →
      ChildFlatOK reg parent inst sub := by
  intro inst h_mem nm sub h_lookup
  dsimp [childrenOKCheck] at h
  have h_all := (List.all_eq_true.mp h) inst h_mem
  rw [h_lookup] at h_all
  dsimp only at h_all
  simp only [Bool.and_eq_true] at h_all
  obtain ⟨⟨⟨⟨⟨⟨h_flat, h_wf_c⟩, h_topo_c⟩, h_inj_c⟩, h_bound_c⟩, h_ports_c⟩, h_nodup_c⟩ := h_all
  refine ⟨?_, SubWf_of_check sub h_wf_c, TopoOrdered_of_check sub h_topo_c, RemapInj_of_check sub inst h_inj_c, ?_, ?_,
    of_decide_eq_true h_nodup_c⟩
  · exact List.length_eq_zero_iff.mp (of_decide_eq_true h_flat)
  · intro w h_w pw h_res
    have h1 := (List.all_eq_true.mp h_bound_c) w h_w
    rw [h_res] at h1
    dsimp only at h1
    exact mem_of_any_eq_true _ _ h1
  · intro w h_w pw h_res
    have h1 := (List.all_eq_true.mp h_ports_c) w h_w
    rw [h_res] at h1
    dsimp only at h1
    rw [Bool.or_eq_true] at h1
    rcases h1 with h_a | h_a
    · exact Or.inl (mem_of_any_eq_true _ _ h_a)
    · exact Or.inr (mem_of_any_eq_true _ _ h_a)

/-- Driven-or-primary wires live in the submodule wire universe. -/
theorem mem_subWires_of_driven (sub : Circuit) (w : Wire)
    (h : w ∈ sub.inputs ++ sub.gates.map (fun g => g.output)) :
    w ∈ subWires sub := by
  dsimp [subWires]
  rcases List.mem_append.mp h with h_in | h_dr
  · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl h_in)))
  · obtain ⟨g, h_g, rfl⟩ := List.mem_map.mp h_dr
    exact List.mem_append.mpr (Or.inr
      (List.mem_flatMap.mpr ⟨g, h_g, List.Mem.head _⟩))

/-- Output wires live in the submodule wire universe. -/
theorem mem_subWires_of_output (sub : Circuit) (w : Wire) (h : w ∈ sub.outputs) :
    w ∈ subWires sub := by
  dsimp [subWires]
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr h)))

/-- Input wires live in the submodule wire universe. -/
theorem mem_subWires_of_input (sub : Circuit) (w : Wire) (h : w ∈ sub.inputs) :
    w ∈ subWires sub := by
  dsimp [subWires]
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl h)))

/-- A gate evaluates the same under envs agreeing on its inputs. -/
theorem evalGate_congr_inputs (g : Gate) (e₁ e₂ : Env)
    (h : ∀ w ∈ g.inputs, e₁ w = e₂ w) : evalGate g e₁ = evalGate g e₂ := by
  cases g with
  | mk gateType inputs output =>
    cases gateType with
    | AND => match inputs with
      | [i0, i1] => simp_all [evalGate]
      | [] => simp [evalGate]
      | [_] => simp [evalGate]
      | _ :: _ :: _ :: _ => simp [evalGate]
    | OR => match inputs with
      | [i0, i1] => simp_all [evalGate]
      | [] => simp [evalGate]
      | [_] => simp [evalGate]
      | _ :: _ :: _ :: _ => simp [evalGate]
    | XOR => match inputs with
      | [i0, i1] => simp_all [evalGate]
      | [] => simp [evalGate]
      | [_] => simp [evalGate]
      | _ :: _ :: _ :: _ => simp [evalGate]
    | NOT => match inputs with
      | [i0] => simp_all [evalGate]
      | [] => simp [evalGate]
      | _ :: _ :: _ => simp [evalGate]
    | BUF => match inputs with
      | [i0] => simp_all [evalGate]
      | [] => simp [evalGate]
      | _ :: _ :: _ => simp [evalGate]
    | MUX => match inputs with
      | [i0, i1, i2] => simp_all [evalGate]
      | [] => simp [evalGate]
      | [_] => simp [evalGate]
      | [_, _] => simp [evalGate]
      | _ :: _ :: _ :: _ :: _ => simp [evalGate]
    | DFF => simp [evalGate]
    | DFF_SET => simp [evalGate]

/-- A remapped gate evaluates like the original under the remapped env. -/
theorem evalGate_remap (g : Gate) (remap : Wire → Wire) (env : Env) :
    evalGate { gateType := g.gateType, inputs := g.inputs.map remap,
               output := remap g.output } env =
    evalGate g (fun w => env (remap w)) := by
  cases g with
  | mk gateType inputs output =>
    cases gateType with
    | AND => match inputs with
      | [i0, i1] => simp [evalGate]
      | [] => simp [evalGate]
      | [_] => simp [evalGate]
      | _ :: _ :: _ :: _ => simp [evalGate]
    | OR => match inputs with
      | [i0, i1] => simp [evalGate]
      | [] => simp [evalGate]
      | [_] => simp [evalGate]
      | _ :: _ :: _ :: _ => simp [evalGate]
    | XOR => match inputs with
      | [i0, i1] => simp [evalGate]
      | [] => simp [evalGate]
      | [_] => simp [evalGate]
      | _ :: _ :: _ :: _ => simp [evalGate]
    | NOT => match inputs with
      | [i0] => simp [evalGate]
      | [] => simp [evalGate]
      | _ :: _ :: _ => simp [evalGate]
    | BUF => match inputs with
      | [i0] => simp [evalGate]
      | [] => simp [evalGate]
      | _ :: _ :: _ => simp [evalGate]
    | MUX => match inputs with
      | [i0, i1, i2] => simp [evalGate]
      | [] => simp [evalGate]
      | [_] => simp [evalGate]
      | [_, _] => simp [evalGate]
      | _ :: _ :: _ :: _ :: _ => simp [evalGate]
    | DFF => simp [evalGate]
    | DFF_SET => simp [evalGate]

/-- A remapped DFF evaluates like the original under the remapped env. -/
theorem evalDFF_remap (g : Gate) (remap : Wire → Wire) (env : Env) :
    evalDFF { gateType := g.gateType, inputs := g.inputs.map remap,
              output := remap g.output } env =
    evalDFF g (fun w => env (remap w)) := by
  cases g with
  | mk gateType inputs output =>
    cases gateType with
    | DFF => match inputs with
      | [d, clk, reset] => simp [evalDFF]
      | [] => simp [evalDFF]
      | [_] => simp [evalDFF]
      | [_, _] => simp [evalDFF]
      | _ :: _ :: _ :: _ :: _ => simp [evalDFF]
    | DFF_SET => match inputs with
      | [d, clk, reset] => simp [evalDFF]
      | [] => simp [evalDFF]
      | [_] => simp [evalDFF]
      | [_, _] => simp [evalDFF]
      | _ :: _ :: _ :: _ :: _ => simp [evalDFF]
    | _ => simp [evalDFF]

/-- One remapped gate extends agreement from done-prefix to done ++ [g]. -/
theorem inline_step_prefix_agree (g : Gate) (sub : Circuit) (inst : CircuitInstance)
    (done : List Gate)
    (h_done_sub : ∀ g' ∈ done, g' ∈ sub.gates)
    (h_g_mem : g ∈ sub.gates)
    (h_reads : ∀ w ∈ g.inputs, w ∈ sub.inputs ∨ w ∈ done.map (fun g => g.output))
    (h_inj : RemapInj sub inst)
    (envP envS : Env)
    (h_inv : ∀ w ∈ sub.inputs ++ done.map (fun g => g.output),
      envP (flattenRemap sub inst w) = envS w) :
    ∀ w ∈ sub.inputs ++ (done ++ [g]).map (fun g => g.output),
      (updateEnv envP (flattenRemap sub inst g.output)
        (evalGate { gateType := g.gateType, inputs := g.inputs.map (flattenRemap sub inst),
                    output := flattenRemap sub inst g.output } envP))
        (flattenRemap sub inst w)
      = (updateEnv envS g.output (evalGate g envS)) w := by
  intro w h_w
  have h_v : evalGate { gateType := g.gateType, inputs := g.inputs.map (flattenRemap sub inst),
                        output := flattenRemap sub inst g.output } envP
             = evalGate g envS := by
    rw [evalGate_remap]
    apply evalGate_congr_inputs
    intro w' h_w'
    have h_mem : w' ∈ sub.inputs ++ done.map (fun g => g.output) := by
      rcases h_reads w' h_w' with h_in | h_dr
      · exact List.mem_append.mpr (Or.inl h_in)
      · exact List.mem_append.mpr (Or.inr h_dr)
    exact h_inv w' h_mem
  by_cases h_eq : w = g.output
  · subst h_eq
    simp [updateEnv, wire_beq_self, h_v]
  · have h_w_old : w ∈ sub.inputs ++ done.map (fun g => g.output) := by
      have h_map_app : (done ++ [g]).map (fun g => g.output) = done.map (fun g => g.output) ++ [g.output] := by
        simp
      rw [h_map_app, ← List.append_assoc] at h_w
      rcases List.mem_append.mp h_w with h_in | h_single
      · exact h_in
      · rcases List.mem_cons.mp h_single with h_hit | h_nil
        · exact (h_eq h_hit).elim
        · cases h_nil
    have h_wm : w ∈ subWires sub := by
      rcases List.mem_append.mp h_w_old with h_in | h_dr
      · exact mem_subWires_of_driven sub w (List.mem_append.mpr (Or.inl h_in))
      · obtain ⟨g', h_g', rfl⟩ := List.mem_map.mp h_dr
        have h_g'_sub : g' ∈ sub.gates := h_done_sub g' h_g'
        exact mem_subWires_of_driven sub _ (List.mem_append.mpr (Or.inr
          (List.mem_map.mpr ⟨g', h_g'_sub, rfl⟩)))
    have h_om : g.output ∈ subWires sub :=
      mem_subWires_of_driven sub _ (List.mem_append.mpr (Or.inr
        (List.mem_map.mpr ⟨g, h_g_mem, rfl⟩)))
    have h_ne : flattenRemap sub inst w ≠ flattenRemap sub inst g.output := by
      intro h_con
      exact h_eq (h_inj w h_wm _ h_om h_con)
    simp [updateEnv, wire_beq_ne _ _ h_ne, wire_beq_ne _ _ h_eq, h_inv w h_w_old]

/-- Evaluating inlined gates simulates the submodule across all driven wires,
    inducting over the todo suffix with done prefix accumulated. -/
theorem evalGates_inline_agree_prefix (todo : List Gate) (sub : Circuit)
    (inst : CircuitInstance)
    (h_topo : TopoOrdered sub)
    (h_inj : RemapInj sub inst)
    (done : List Gate)
    (h_split : sub.gates = done ++ todo)
    (envP envS : Env)
    (h_agree : ∀ w ∈ sub.inputs ++ done.map (fun g => g.output),
      envP (flattenRemap sub inst w) = envS w) :
    ∀ w ∈ sub.inputs ++ (done ++ todo).map (fun g => g.output),
      (Shoumei.evalGates (todo.map fun g =>
        { gateType := g.gateType, inputs := g.inputs.map (flattenRemap sub inst),
          output := flattenRemap sub inst g.output }) envP)
        (flattenRemap sub inst w)
      = (Shoumei.evalGates todo envS) w := by
  induction todo generalizing done envP envS with
  | nil =>
    intro w h_w
    rw [List.append_nil] at h_w
    dsimp [Shoumei.evalGates]
    exact h_agree w h_w
  | cons hd tl ih =>
    have h_split_hd : sub.gates = done ++ hd :: tl := h_split
    have h_hd_reads := h_topo done hd tl h_split_hd
    have h_hd_mem : hd ∈ sub.gates := by
      rw [h_split]
      exact List.mem_append.mpr (Or.inr (List.Mem.head _))
    have h_done_sub : ∀ g' ∈ done, g' ∈ sub.gates := by
      intro g' hg'
      rw [h_split]
      exact List.mem_append.mpr (Or.inl hg')
    have h_step : ∀ w ∈ sub.inputs ++ (done ++ [hd]).map (fun g => g.output),
        (updateEnv envP (flattenRemap sub inst hd.output)
          (evalGate { gateType := hd.gateType, inputs := hd.inputs.map (flattenRemap sub inst),
                      output := flattenRemap sub inst hd.output } envP))
          (flattenRemap sub inst w)
        = (updateEnv envS hd.output (evalGate hd envS)) w :=
      inline_step_prefix_agree hd sub inst done h_done_sub h_hd_mem h_hd_reads h_inj envP envS h_agree
    have h_split_tl : sub.gates = (done ++ [hd]) ++ tl := by
      rw [h_split, List.append_assoc]
      rfl
    have h_w_assoc : ∀ w, w ∈ sub.inputs ++ (done ++ hd :: tl).map (fun g => g.output) ↔
                          w ∈ sub.inputs ++ ((done ++ [hd]) ++ tl).map (fun g => g.output) := by
      intro w
      simp [List.append_assoc]
    dsimp only [Shoumei.evalGates, List.map_cons, List.foldl_cons]
    intro w h_w
    have h_w' : w ∈ sub.inputs ++ ((done ++ [hd]) ++ tl).map (fun g => g.output) :=
      (h_w_assoc w).mp h_w
    exact ih (done ++ [hd]) h_split_tl _ _ h_step w h_w'

/-- Inlined remapped gates simulate the submodule over primary-or-driven
    wires, starting from agreement on inputs alone. -/
theorem evalGates_inline_agree (sub : Circuit) (inst : CircuitInstance)
    (h_topo : TopoOrdered sub)
    (h_inj : RemapInj sub inst)
    (envP envS : Env)
    (h_env : ∀ w ∈ sub.inputs, envP (flattenRemap sub inst w) = envS w)
    (w : Wire) (h_w : w ∈ sub.inputs ++ sub.gates.map (fun g => g.output)) :
    (Shoumei.evalGates (Circuit.inline sub (flattenRemap sub inst)) envP)
      (flattenRemap sub inst w)
    = (Shoumei.evalGates sub.gates envS) w := by
  have h_split : sub.gates = [] ++ sub.gates := rfl
  have h_agree_nil : ∀ w ∈ sub.inputs ++ ([] : List Gate).map (fun g => g.output),
      envP (flattenRemap sub inst w) = envS w := by
    intro w' hw'
    simp only [List.map_nil, List.append_nil] at hw'
    exact h_env w' hw'
  have h_w' : w ∈ sub.inputs ++ ([] ++ sub.gates).map (fun (g : Gate) => g.output) := by
    simpa using h_w
  exact evalGates_inline_agree_prefix sub.gates sub inst h_topo h_inj [] h_split envP envS h_agree_nil w h_w'

/-- Evaluating gates preserves any wire not driven by those gates. -/
theorem evalGates_preserve (gates : List Gate) (env : Env) (w : Wire)
    (h_none : ∀ g ∈ gates, g.output ≠ w) :
    Shoumei.evalGates gates env w = env w := by
  induction gates generalizing env with
  | nil => rfl
  | cons g rest ih =>
    have h_ne : g.output ≠ w := h_none g (List.Mem.head _)
    have h_rest : ∀ g' ∈ rest, g'.output ≠ w := fun g' hg' => h_none g' (List.Mem.tail _ hg')
    have h_ih := ih (updateEnv env g.output (evalGate g env)) h_rest
    change Shoumei.evalGates rest (updateEnv env g.output (evalGate g env)) w = env w
    rw [h_ih]
    simp [updateEnv, wire_beq_ne w g.output (Ne.symm h_ne)]

/-- Boolean check backing `FlattenFresh`, discharged by `native_decide` per
    concrete hierarchy. -/
def flattenFreshCheck (reg : ModuleRegistry) (c : Circuit) : Bool :=
  c.instances.all fun inst =>
    match reg.find? (fun p => p.1 == inst.moduleName) with
    | none => true
    | some (_, sub) =>
      (subWires sub).all fun w =>
        (parentWires c).all fun pw =>
          decide (flattenRemap sub inst w ≠ pw ∨
            resolvePort sub inst w = some pw)

/-- `flattenFreshCheck` implies `FlattenFresh`. -/
theorem FlattenFresh_of_check (reg : ModuleRegistry) (c : Circuit)
    (h : flattenFreshCheck reg c = true) : FlattenFresh reg c := by
  intro inst h_mem nm sub h_lookup w h_w pw h_pw h_eq
  dsimp [flattenFreshCheck] at h
  have h_all := (List.all_eq_true.mp h) inst h_mem
  rw [h_lookup] at h_all
  dsimp only at h_all
  have h_w' := (List.all_eq_true.mp h_all) w h_w
  have h_dec := (List.all_eq_true.mp h_w') pw h_pw
  exact (of_decide_eq_true h_dec).resolve_left (fun h_ne => absurd h_eq h_ne)

/-- `evalGates` distributes over gate-list append. -/
theorem evalGates_append (gates₁ gates₂ : List Gate) (env : Env) :
    Shoumei.evalGates (gates₁ ++ gates₂) env
      = Shoumei.evalGates gates₂ (Shoumei.evalGates gates₁ env) := by
  dsimp [Shoumei.evalGates]
  rw [List.foldl_append]

/-- Agreement on a wire list. -/
def AgreeOn (ws : List Wire) (eH eF : Env) : Prop :=
  ∀ w ∈ ws, eH w = eF w

/-- Inputs wired through the parent registry resolve. -/
theorem input_bound_of_wellwired (reg : ModuleRegistry) (parent : Circuit)
    (h_wired : WellWired reg parent = true)
    (inst : CircuitInstance) (h_mem : inst ∈ parent.instances)
    (nm : String) (sub : Circuit)
    (h_lookup : reg.find? (fun p => p.1 == inst.moduleName) = some (nm, sub))
    (w : Wire) (h_w : w ∈ sub.inputs) :
    ∃ pw, resolvePort sub inst w = some pw := by
  have h_ne : resolvePort sub inst w ≠ none := by
    intro h_con
    have h_mem2 : ({ parentModule := parent.name, instName := inst.instName,
                     childModule := inst.moduleName, portWire := w } : MissingPort)
        ∈ checkInstanceInputs reg parent.name inst := by
      dsimp [checkInstanceInputs]
      rw [h_lookup]
      rw [List.mem_filterMap]
      refine ⟨w, h_w, ?_⟩
      have h_con' : resolvePortWithIndex sub (buildInstanceIndex inst) w = none :=
        h_con
      rw [h_con']
    have h_mem3 : ({ parentModule := parent.name, instName := inst.instName,
                     childModule := inst.moduleName, portWire := w } : MissingPort)
        ∈ checkCircuitWiring reg parent := by
      dsimp [checkCircuitWiring]
      rw [List.mem_flatMap]
      exact ⟨inst, h_mem, h_mem2⟩
    match h_l : checkCircuitWiring reg parent with
    | [] =>
      rw [h_l] at h_mem3
      cases h_mem3
    | _ :: _ =>
      dsimp [WellWired] at h_wired
      rw [h_l] at h_wired
      simp at h_wired
  obtain ⟨x, h_x⟩ := Option.ne_none_iff_exists.mp h_ne
  exact ⟨x, h_x.symm⟩

/-- Evaluating concatenated inlined gates folds per instance. -/
theorem evalGates_flatMap_foldl (F : CircuitInstance → List Gate)
    (insts : List CircuitInstance) (env : Env) :
    Shoumei.evalGates (insts.flatMap F) env
    = insts.foldl (fun env inst => Shoumei.evalGates (F inst) env) env := by
  induction insts generalizing env with
  | nil =>
    simp only [List.flatMap_nil, Shoumei.evalGates, List.foldl_nil]
  | cons hd tl ih =>
    simp only [List.flatMap_cons, List.foldl_cons]
    rw [evalGates_append]
    exact ih _

/-- A folded output-propagation preserves wires nothing binds. -/
theorem foldl_propagate_preserve (outs : List Wire) (sub : Circuit)
    (inst : CircuitInstance) (outEnv : Env) (eH : Env) (pw : Wire)
    (h_nobind : ∀ w' ∈ outs, ∀ p, resolvePort sub inst w' = some p → p ≠ pw) :
    (outs.foldl (fun e outWire =>
      match resolvePort sub inst outWire with
      | some p => updateEnv e p (outEnv outWire)
      | none => e) eH) pw = eH pw := by
  induction outs generalizing eH with
  | nil => rfl
  | cons hd tl ih =>
    have h_rest : ∀ w' ∈ tl, ∀ p, resolvePort sub inst w' = some p → p ≠ pw :=
      fun w' h_w' p h_p => h_nobind w' (List.Mem.tail _ h_w') p h_p
    match h_hd : resolvePort sub inst hd with
    | some p =>
      have h_ne : p ≠ pw := h_nobind hd (List.Mem.head _) p h_hd
      have h_fold : ((hd :: tl).foldl (fun e outWire =>
          match resolvePort sub inst outWire with
          | some p => updateEnv e p (outEnv outWire)
          | none => e) eH)
          = (tl.foldl (fun e outWire =>
            match resolvePort sub inst outWire with
            | some p => updateEnv e p (outEnv outWire)
            | none => e) (updateEnv eH p (outEnv hd))) := by
        simp only [List.foldl_cons]
        rw [h_hd]
      rw [h_fold]
      have h_ih := ih (updateEnv eH p (outEnv hd)) h_rest
      have h_miss : (updateEnv eH p (outEnv hd)) pw = eH pw := by
        simp [updateEnv, wire_beq_ne pw p (Ne.symm h_ne)]
      rw [h_ih]
      exact h_miss
    | none =>
      have h_fold : ((hd :: tl).foldl (fun e outWire =>
          match resolvePort sub inst outWire with
          | some p => updateEnv e p (outEnv outWire)
          | none => e) eH)
          = (tl.foldl (fun e outWire =>
            match resolvePort sub inst outWire with
            | some p => updateEnv e p (outEnv outWire)
            | none => e) eH) := by
        simp only [List.foldl_cons]
        rw [h_hd]
      rw [h_fold]
      exact ih _ h_rest

/-- A folded output-propagation reads back the uniquely written value. -/
theorem foldl_propagate_lookup (sub : Circuit)
    (inst : CircuitInstance) (outEnv : Env) (pw : Wire) (w : Wire)
    (h_bind : resolvePort sub inst w = some pw)
    (outs : List Wire) :
    w ∈ outs → outs.Nodup →
    (∀ w' ∈ outs, w' ≠ w →
      ∀ p, resolvePort sub inst w' = some p → p ≠ pw) →
    ∀ (eH : Env),
    (outs.foldl (fun e outWire =>
      match resolvePort sub inst outWire with
      | some p => updateEnv e p (outEnv outWire)
      | none => e) eH) pw = outEnv w := by
  induction outs with
  | nil =>
    intro h_w _ _ _
    simp at h_w
  | cons hd tl ih =>
    intro h_w h_nodup h_uniq eH
    by_cases h_eq : hd = w
    · have h_nodup_tl : tl.Nodup := (List.nodup_cons.mp h_nodup).2
      have h_notmem : hd ∉ tl := (List.nodup_cons.mp h_nodup).1
      rw [h_eq] at h_notmem
      have h_hd_bind : resolvePort sub inst hd = some pw := by rw [h_eq, h_bind]
      have h_step : ((hd :: tl).foldl (fun e outWire =>
          match resolvePort sub inst outWire with
          | some p => updateEnv e p (outEnv outWire)
          | none => e) eH)
          = (tl.foldl (fun e outWire =>
            match resolvePort sub inst outWire with
            | some p => updateEnv e p (outEnv outWire)
            | none => e) (updateEnv eH pw (outEnv hd))) := by
        simp only [List.foldl_cons]
        rw [h_hd_bind]
      rw [h_step]
      have h_tl_nobind : ∀ w' ∈ tl, ∀ p,
          resolvePort sub inst w' = some p → p ≠ pw := by
        intro w' h_w' p h_p
        have h_ne : w' ≠ w := fun h_con => h_notmem (h_con ▸ h_w')
        exact h_uniq w' (List.Mem.tail _ h_w') h_ne p h_p
      have h_pres := foldl_propagate_preserve tl sub inst outEnv
        (updateEnv eH pw (outEnv hd)) pw h_tl_nobind
      have h_hit : (updateEnv eH pw (outEnv hd)) pw = outEnv w := by
        simp [updateEnv, wire_beq_self, h_eq]
      exact h_pres.trans h_hit
    · have h_w_tl : w ∈ tl := by
        rcases List.mem_cons.mp h_w with h | h
        · exact (h_eq h.symm).elim
        · exact h
      have h_uniq_tl : ∀ w' ∈ tl, w' ≠ w →
          ∀ p, resolvePort sub inst w' = some p → p ≠ pw :=
        fun w' h_w' h_ne p h_p =>
          h_uniq w' (List.Mem.tail _ h_w') h_ne p h_p
      have h_nodup_tl : tl.Nodup := (List.nodup_cons.mp h_nodup).2
      have h_step : ((hd :: tl).foldl (fun e outWire =>
          match resolvePort sub inst outWire with
          | some p => updateEnv e p (outEnv outWire)
          | none => e) eH)
          = (tl.foldl (fun e outWire =>
            match resolvePort sub inst outWire with
            | some p => updateEnv e p (outEnv outWire)
            | none => e)
            (match resolvePort sub inst hd with
             | some p => updateEnv eH p (outEnv hd)
             | none => eH)) := by
        simp only [List.foldl_cons]
      rw [h_step]
      exact ih h_w_tl h_nodup_tl h_uniq_tl _

/-- Per-instance preservation: hierarchical instance application agrees with
    inlined remapped gates on parent wires. -/
theorem applyInst_inline_agree
    (reg : ModuleRegistry) (parent : Circuit)
    (h_wired : WellWired reg parent = true)
    (inst : CircuitInstance) (h_mem : inst ∈ parent.instances)
    (nm : String) (sub : Circuit)
    (h_lookup : reg.find? (fun p => p.1 == inst.moduleName) = some (nm, sub))
    (h_ok : ChildFlatOK reg parent inst sub)
    (h_fresh : ∀ w ∈ subWires sub, ∀ pw ∈ parentWires parent,
      flattenRemap sub inst w = pw → resolvePort sub inst w = some pw)
    (eH eF : Env)
    (h_agree : AgreeOn (parentWires parent) eH eF) :
    AgreeOn (parentWires parent)
      (applyInst reg (evalHier reg 1) eH inst)
      (Shoumei.evalGates (Circuit.inline (flattenAllFuel reg sub 1)
        (flattenRemap sub inst)) eF) := by
  intro pw h_pw
  have h_fl : (flattenAllFuel reg sub 1).gates = sub.gates := by
    simp [flattenAllFuel, h_ok.flat]
  have h_inline_eq : Circuit.inline (flattenAllFuel reg sub 1) (flattenRemap sub inst)
      = Circuit.inline sub (flattenRemap sub inst) := by
    dsimp [Circuit.inline]
    rw [h_fl]
  rw [h_inline_eq]
  simp only [applyInst, h_lookup]
  have h_eval_hier : evalHier reg 1 sub (subInputEnv sub inst eH)
      = Shoumei.evalGates sub.gates (subInputEnv sub inst eH) := by
    have h1 := evalHier_no_instances reg 0 sub h_ok.flat (subInputEnv sub inst eH)
    rw [← evalGates_eq_evalCircuit] at h1
    exact h1
  rw [h_eval_hier]
  have h_in_agree : ∀ w ∈ sub.inputs, eF (flattenRemap sub inst w) = subInputEnv sub inst eH w := by
    intro w hw
    obtain ⟨ipw, h_ipw⟩ := input_bound_of_wellwired reg parent h_wired inst h_mem nm sub h_lookup w hw
    have h_remap : flattenRemap sub inst w = ipw := by
      dsimp [flattenRemap]; rw [h_ipw]
    have h_sub_env : subInputEnv sub inst eH w = eH ipw := by
      dsimp [subInputEnv]; rw [h_ipw]
    have h_ipw_parent : ipw ∈ parentWires parent :=
      h_ok.bound w (List.mem_append.mpr (Or.inl hw)) ipw h_ipw
    have h_agree_ipw : eH ipw = eF ipw := h_agree ipw h_ipw_parent
    rw [h_remap, h_sub_env, ← h_agree_ipw]
  match h_find : sub.outputs.find? (fun w' => match resolvePort sub inst w' with | some p => p == pw | none => false) with
  | some w =>
    have h_w_mem : w ∈ sub.outputs := List.mem_of_find?_eq_some h_find
    have h_w_cond := List.find?_some h_find
    match h_res : resolvePort sub inst w with
    | some p =>
      rw [h_res] at h_w_cond
      have h_p_eq : p = pw := wire_beq_eq _ _ h_w_cond
      have h_bind : resolvePort sub inst w = some pw := by rw [← h_p_eq]; exact h_res
      have h_uniq : ∀ w' ∈ sub.outputs, w' ≠ w → ∀ p, resolvePort sub inst w' = some p → p ≠ pw := by
        intro w' hw' h_ne p' hp'
        intro h_con
        have h_bind' : resolvePort sub inst w' = some pw := by rw [← h_con]; exact hp'
        have h_remap_w : flattenRemap sub inst w = pw := by dsimp [flattenRemap]; rw [h_bind]
        have h_remap_w' : flattenRemap sub inst w' = pw := by dsimp [flattenRemap]; rw [h_bind']
        have h_eq_remap : flattenRemap sub inst w' = flattenRemap sub inst w := by rw [h_remap_w', h_remap_w]
        have hw'_sub : w' ∈ subWires sub := mem_subWires_of_output sub w' hw'
        have hw_sub : w ∈ subWires sub := mem_subWires_of_output sub w h_w_mem
        exact h_ne (h_ok.inj w' hw'_sub w hw_sub h_eq_remap)
      have h_lhs := foldl_propagate_lookup sub inst (Shoumei.evalGates sub.gates (subInputEnv sub inst eH))
        pw w h_bind sub.outputs h_w_mem h_ok.outnodup h_uniq eH
      have h_remap_w : flattenRemap sub inst w = pw := by dsimp [flattenRemap]; rw [h_bind]
      have h_out_driven : w ∈ sub.inputs ++ sub.gates.map (fun g => g.output) := by
        rcases h_ok.wf.out w h_w_mem with h_in | h_dr
        · exact List.mem_append.mpr (Or.inl h_in)
        · exact List.mem_append.mpr (Or.inr h_dr)
      have h_eval := evalGates_inline_agree sub inst h_ok.topo h_ok.inj eF (subInputEnv sub inst eH) h_in_agree w h_out_driven
      rw [h_remap_w] at h_eval
      exact h_lhs.trans h_eval.symm
    | none =>
      rw [h_res] at h_w_cond
      cases h_w_cond
  | none =>
    have h_nobind : ∀ w' ∈ sub.outputs, ∀ p, resolvePort sub inst w' = some p → p ≠ pw := by
      intro w' hw' p hp
      have h_pred := List.find?_eq_none.mp h_find w' hw'
      rw [hp] at h_pred
      intro h_con
      subst h_con
      simp [wire_beq_self] at h_pred
    have h_lhs := foldl_propagate_preserve sub.outputs sub inst
      (Shoumei.evalGates sub.gates (subInputEnv sub inst eH)) eH pw h_nobind
    have h_no_gate : ∀ g ∈ Circuit.inline sub (flattenRemap sub inst), g.output ≠ pw := by
      intro g hg
      dsimp [Circuit.inline] at hg
      obtain ⟨g_orig, hg_orig, rfl⟩ := List.mem_map.mp hg
      dsimp only
      intro h_con
      have h_orig_wires : g_orig.output ∈ subWires sub :=
        mem_subWires_of_driven sub _ (List.mem_append.mpr (Or.inr
          (List.mem_map.mpr ⟨g_orig, hg_orig, rfl⟩)))
      have h_fresh_bind := h_fresh g_orig.output h_orig_wires pw h_pw h_con
      rcases h_ok.ports g_orig.output h_orig_wires pw h_fresh_bind with h_in | h_out
      · have h_src := h_ok.wf.src g_orig.output h_in
        have h_dr : g_orig.output ∈ sub.gates.map (fun g => g.output) :=
          List.mem_map.mpr ⟨g_orig, hg_orig, rfl⟩
        exact h_src h_dr
      · exact h_nobind g_orig.output h_out pw h_fresh_bind rfl
    have h_rhs := evalGates_preserve (Circuit.inline sub (flattenRemap sub inst)) eF pw h_no_gate
    have h_mid : eH pw = Shoumei.evalGates (sub.inline (flattenRemap sub inst)) eF pw := by
      rw [h_agree pw h_pw, h_rhs]
    exact h_lhs.trans h_mid

/-- Input wires belong to the parent wire universe. -/
theorem input_mem_parentWires (c : Circuit) (w : Wire) (h : w ∈ c.inputs) :
    w ∈ parentWires c := by
  dsimp [parentWires]
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl h)))

/-- Output wires belong to the parent wire universe. -/
theorem output_mem_parentWires (c : Circuit) (w : Wire) (h : w ∈ c.outputs) :
    w ∈ parentWires c := by
  dsimp [parentWires]
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr h)))

/-- Gate outputs belong to the parent wire universe. -/
theorem gate_output_mem_parentWires (c : Circuit) (g : Gate) (h : g ∈ c.gates) :
    g.output ∈ parentWires c := by
  dsimp [parentWires]
  refine List.mem_append.mpr (Or.inr ?_)
  exact List.mem_flatMap.mpr ⟨g, h, List.Mem.head _⟩

/-- Gate inputs belong to the parent wire universe. -/
theorem gate_input_mem_parentWires (c : Circuit) (g : Gate) (h : g ∈ c.gates)
    (w : Wire) (hw : w ∈ g.inputs) : w ∈ parentWires c := by
  dsimp [parentWires]
  refine List.mem_append.mpr (Or.inr ?_)
  exact List.mem_flatMap.mpr ⟨g, h, List.Mem.tail _ hw⟩

/-- Evaluating gates from parent-wires-agreeing environments preserves agreement. -/
theorem evalGates_congr_parent (c : Circuit) (gs : List Gate)
    (h_gs : ∀ g ∈ gs, g ∈ c.gates) (e₁ e₂ : Env)
    (h_agree : AgreeOn (parentWires c) e₁ e₂) :
    AgreeOn (parentWires c) (Shoumei.evalGates gs e₁) (Shoumei.evalGates gs e₂) := by
  induction gs generalizing e₁ e₂ with
  | nil => exact h_agree
  | cons g rest ih =>
    have hg_mem : g ∈ c.gates := h_gs g (List.Mem.head _)
    have h_rest : ∀ g' ∈ rest, g' ∈ c.gates := fun g' hg' => h_gs g' (List.Mem.tail _ hg')
    have h_inputs_agree : ∀ w ∈ g.inputs, e₁ w = e₂ w := by
      intro w hw
      exact h_agree w (gate_input_mem_parentWires c g hg_mem w hw)
    have h_eval : evalGate g e₁ = evalGate g e₂ := evalGate_congr_inputs g e₁ e₂ h_inputs_agree
    have h_step_agree : AgreeOn (parentWires c)
        (updateEnv e₁ g.output (evalGate g e₁))
        (updateEnv e₂ g.output (evalGate g e₂)) := by
      intro w hw
      by_cases h_eq : w = g.output
      · subst h_eq
        simp [updateEnv, wire_beq_self, h_eval]
      · simp [updateEnv, wire_beq_ne w g.output h_eq, h_agree w hw]
    change AgreeOn (parentWires c)
      (Shoumei.evalGates rest (updateEnv e₁ g.output (evalGate g e₁)))
      (Shoumei.evalGates rest (updateEnv e₂ g.output (evalGate g e₂)))
    exact ih h_rest _ _ h_step_agree

/-- Folded instance application preserves agreement on parent wires. -/
theorem foldl_instances_agree (reg : ModuleRegistry) (parent : Circuit)
    (h_wired : WellWired reg parent = true)
    (h_fresh : FlattenFresh reg parent)
    (h_children : ∀ inst ∈ parent.instances, ∀ nm sub,
      reg.find? (fun p => p.1 == inst.moduleName) = some (nm, sub) →
      ChildFlatOK reg parent inst sub)
    (insts : List CircuitInstance) (h_insts : ∀ inst ∈ insts, inst ∈ parent.instances)
    (eH eF : Env) (h_agree : AgreeOn (parentWires parent) eH eF) :
    AgreeOn (parentWires parent)
      (insts.foldl (applyInst reg (evalHier reg 1)) eH)
      (insts.foldl (fun e inst => match reg.find? (fun p => p.1 == inst.moduleName) with
        | some (_, sub) => Shoumei.evalGates (Circuit.inline sub (flattenRemap sub inst)) e
        | none => e) eF) := by
  induction insts generalizing eH eF with
  | nil => exact h_agree
  | cons inst rest ih =>
    have h_mem : inst ∈ parent.instances := h_insts inst (List.Mem.head _)
    have h_rest : ∀ i ∈ rest, i ∈ parent.instances := fun i hi => h_insts i (List.Mem.tail _ hi)
    have h_step : AgreeOn (parentWires parent)
        (applyInst reg (evalHier reg 1) eH inst)
        (match reg.find? (fun p => p.1 == inst.moduleName) with
         | some (_, sub) => Shoumei.evalGates (Circuit.inline sub (flattenRemap sub inst)) eF
         | none => eF) := by
      match h_lookup : reg.find? (fun p => p.1 == inst.moduleName) with
      | some (nm, sub) =>
        have h_ok := h_children inst h_mem nm sub h_lookup
        have h_fr := h_fresh inst h_mem nm sub h_lookup
        have h_agree_inst := applyInst_inline_agree reg parent h_wired inst h_mem nm sub h_lookup h_ok h_fr eH eF h_agree
        have h_fl : (flattenAllFuel reg sub 1).gates = sub.gates := by simp [flattenAllFuel, h_ok.flat]
        have h_inl_eq : Circuit.inline (flattenAllFuel reg sub 1) (flattenRemap sub inst)
            = Circuit.inline sub (flattenRemap sub inst) := by dsimp [Circuit.inline]; rw [h_fl]
        rw [h_lookup]
        dsimp only
        rw [← h_inl_eq]
        exact h_agree_inst
      | none =>
        dsimp [applyInst]
        rw [h_lookup]
        exact h_agree
    dsimp only [List.foldl_cons]
    exact ih h_rest (applyInst reg (evalHier reg 1) eH inst) _ h_step

/-- Main theorem (depth-1 flattener soundness): evaluating a flattened circuit
    agrees with hierarchical evaluation on all parent outputs, for any circuit
    with flat children, well-wired ports, and fresh instance scoping. -/
theorem flatten_sound_depth1 (reg : ModuleRegistry) (parent : Circuit)
    (h_wired : WellWired reg parent = true)
    (h_fresh : FlattenFresh reg parent)
    (h_children : ∀ inst ∈ parent.instances, ∀ nm sub,
      reg.find? (fun p => p.1 == inst.moduleName) = some (nm, sub) →
      ChildFlatOK reg parent inst sub)
    (env : Env) :
    ∀ w ∈ parent.outputs,
      evalHier reg 2 parent env w = evalCircuit (flattenAllFuel reg parent 1) env w := by
  intro w hw
  have hw_parent : w ∈ parentWires parent := output_mem_parentWires parent w hw
  dsimp [evalCircuit]
  have h_flat_gates : (flattenAllFuel reg parent 1).gates
      = preGates reg parent ++
        (parent.instances.flatMap fun inst =>
          match reg.find? (fun p => p.1 == inst.moduleName) with
          | some (_, subCircuit) => Circuit.inline subCircuit (flattenRemap subCircuit inst)
          | none => []) ++
        postGates reg parent := by
    dsimp [flattenAllFuel]
  rw [h_flat_gates]
  rw [evalGates_append]
  rw [evalGates_append]
  change Shoumei.evalGates (postGates reg parent)
      (parent.instances.foldl (applyInst reg (evalHier reg 1))
        (Shoumei.evalGates (preGates reg parent) env)) w
    = Shoumei.evalGates (postGates reg parent)
        (Shoumei.evalGates
          (parent.instances.flatMap fun inst =>
            match reg.find? (fun p => p.1 == inst.moduleName) with
            | some (_, subCircuit) => Circuit.inline subCircuit (flattenRemap subCircuit inst)
            | none => [])
          (Shoumei.evalGates (preGates reg parent) env)) w
  have h_pre_agree : AgreeOn (parentWires parent)
      (Shoumei.evalGates (preGates reg parent) env)
      (Shoumei.evalGates (preGates reg parent) env) := fun _ _ => rfl
  have h_inlined_fold := evalGates_flatMap_foldl (fun inst =>
      match reg.find? (fun p => p.1 == inst.moduleName) with
      | some (_, subCircuit) => Circuit.inline subCircuit (flattenRemap subCircuit inst)
      | none => []) parent.instances (Shoumei.evalGates (preGates reg parent) env)
  have h_mid_agree := foldl_instances_agree reg parent h_wired h_fresh h_children
    parent.instances (fun _ h => h) _ _ h_pre_agree
  rw [h_inlined_fold]
  have h_step_eq : (fun env inst => match reg.find? (fun p => p.1 == inst.moduleName) with
      | some (_, subCircuit) => Shoumei.evalGates (Circuit.inline subCircuit (flattenRemap subCircuit inst)) env
      | none => env)
    = (fun env inst => Shoumei.evalGates (match reg.find? (fun p => p.1 == inst.moduleName) with
      | some (_, subCircuit) => Circuit.inline subCircuit (flattenRemap subCircuit inst)
      | none => []) env) := by
    ext env inst
    match h_find : reg.find? (fun p => p.1 == inst.moduleName) with
    | some (nm, subCircuit) =>
      simp only [h_find]
    | none =>
      simp only [h_find, Shoumei.evalGates, List.foldl_nil]
  rw [← h_step_eq]
  have h_post_sub : ∀ g ∈ postGates reg parent, g ∈ parent.gates := by
    intro g hg
    dsimp [postGates] at hg
    exact List.mem_filter.mp hg |>.1
  have h_final_agree := evalGates_congr_parent parent (postGates reg parent)
    h_post_sub _ _ h_mid_agree
  exact h_final_agree w hw_parent

/-! ## Sequential state correspondence (depth-1 bisimulation) -/

/-- State correspondence between hierarchical state (where sub-instance DFFs
    are scoped under `instScope`) and flattened state (where sub-instance DFFs
    are remapped under `flattenRemap`).
    Depth-1 sequential bisimulation (`flatten_step_sound`) asserts that:
    1. Outputs agree across one clock cycle: `(stepHier ...).2 w = (evalCycleSequential ...).2 w`
    2. `StateCorr` is preserved by the next state: `StateCorr reg parent (stepHier ...).1 (evalCycleSequential ...).1`. -/
def StateCorr (reg : ModuleRegistry) (parent : Circuit) (s_hier s_flat : State) : Prop :=
  (∀ w ∈ getDFFOutputs parent, s_flat w = s_hier w) ∧
  (∀ inst ∈ parent.instances, ∀ nm sub,
    reg.find? (fun p => p.1 == inst.moduleName) = some (nm, sub) →
    ∀ w ∈ getDFFOutputs sub,
      s_flat (flattenRemap sub inst w) = s_hier (instScope inst.instName w))

/-- Default/zero states satisfy the state correspondence relation trivially. -/
theorem StateCorr_default (reg : ModuleRegistry) (parent : Circuit) :
    StateCorr reg parent (fun _ => false) (fun _ => false) :=
  ⟨fun _ _ => rfl, fun _ _ _ _ _ _ _ => rfl⟩

end Shoumei.Reflection
