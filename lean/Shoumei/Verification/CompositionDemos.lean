/-
Verification/CompositionDemos.lean - Phase 3 demonstrations of `implements_compose`

Instantiates the generic composition lemmas on the two plan-nominated
hierarchies:
- `Mux8x32` = 2x `Mux4x32` + select buffers + top MUX row (combinational;
  the exact family whose bracket port keys Phase 0 repairs)
- `Register160` = `Register64` + `Register64` + `Register32` (sequential;
  pure wiring, no glue gates; also the existing SEC miter pair)

The parent behaviours here are the compositional specs themselves (children
plus glue), so the glue obligations hold by `rfl`: these demos validate that
the machinery — port resolution, pre/post schedule, scoped state threading —
applies to real hierarchies. High-level functional atoms (mux-select,
register capture) are PR3 pilot atoms that reuse these compositions. A few
`native_decide` spot-checks confirm the compositions actually route/capture.
-/

import Shoumei.DSL.PortResolve
import Shoumei.Semantics
import Shoumei.Semantics.Hierarchical
import Shoumei.Verification.Implements
import Shoumei.Circuits.Combinational.MuxTree
import Shoumei.Circuits.Sequential.Register

namespace Shoumei.Verification.CompositionDemos

open Shoumei
open Shoumei.DSL.PortResolve
open Shoumei.Semantics
open Shoumei.Semantics.Hierarchical
open Shoumei.Circuits.Combinational
open Shoumei.Circuits.Sequential

/-! ## Mux8x32 hierarchical composition (combinational) -/

/-- Minimal registry for the Mux demo: the flat 4x32 building block. -/
def regMux : ModuleRegistry := [("Mux4x32", mkMux4x32)]

/-- The hierarchical parent under composition. -/
def parentMux : Circuit := mkMux8xNHierarchical 32

/-- Child spec: flat children evaluate as themselves. -/
def childSpecMux : Circuit → Env → Env :=
  fun sub inEnv => evalCircuit sub inEnv

/-- The bracket-key family resolves: every instance input is driven. -/
theorem parentMux_wellwired : WellWired regMux parentMux = true := by
  native_decide

/-- Flat building blocks agree with hierarchical evaluation. -/
theorem mux_child_atoms :
    ∀ inst ∈ parentMux.instances, ChildCombAtom regMux 1 inst childSpecMux := by
  intro inst _
  intro nm sub h_lookup inEnv
  simp only [regMux, List.find?] at h_lookup
  split at h_lookup
  · cases h_lookup
    exact evalHier_no_instances regMux 0 mkMux4x32 rfl inEnv
  · cases h_lookup

/-- Compositional behaviour: children plus glue, decoded to output values. -/
def muxParentOut (env : Env) : List Bool :=
  parentMux.outputs.map env

def muxParentBeh : CombBehavior Env (List Bool) where
  eval := fun inEnv => muxParentOut (specParentEval childSpecMux regMux parentMux inEnv)

/-- The parent implements its compositional spec, via `implementsComb_compose`. -/
theorem mux8x32hier_implements :
    ImplementsComb regMux 2 parentMux muxParentBeh id muxParentOut := by
  apply implementsComb_compose regMux 1 parentMux parentMux_wellwired
    muxParentBeh id muxParentOut childSpecMux mux_child_atoms
  intro i
  rfl

/-! ## Why no Mux evaluation spots

`evalHier` over `updateEnv`-closure environments does not scale under
`native_decide`: even a 30-gate width-1 hierarchy burns minutes (measured),
so whole-circuit evaluation smoke is intractable at any width. Mux routing
smoke therefore stays with the existing flat proofs
(`mux4x1_exhaustive_correct` over `WireMap`), and hierarchical Mux validation
here is the wiring gate, the child-atom rewriting, and the end-to-end
composition above. `stepHier` over DFF-only hierarchies stays first-order
(no `updateEnv` chains) and fast, so the Register smoke below evaluates. -/

/-! ## Register160 hierarchical composition (sequential) -/

/-- Minimal registry: flat power-of-2 building blocks. -/
def regReg : ModuleRegistry :=
  [("Register64", mkRegisterN 64), ("Register32", mkRegisterN 32)]

/-- The hierarchical parent under composition (64+64+32). -/
def parentReg : Circuit := mkRegisterNHierarchical 160

/-- Child spec: flat children step as themselves. -/
def childSpecReg : Circuit → State → Env → State × Env :=
  fun sub sSub inEnv => evalCycleSequential sub sSub inEnv

/-- Exact-match keys resolve: every instance input is driven. -/
theorem parentReg_wellwired : WellWired regReg parentReg = true := by
  native_decide

/-- Flat building blocks agree with hierarchical stepping. -/
theorem reg_child_atoms :
    ∀ inst ∈ parentReg.instances, ChildAtom regReg 1 inst childSpecReg := by
  intro inst _
  intro nm sub h_lookup sSub inEnv
  simp only [regReg, List.find?] at h_lookup
  split at h_lookup
  · cases h_lookup
    exact stepHier_no_instances regReg 0 (mkRegisterN 64) rfl sSub inEnv
  · split at h_lookup
    · cases h_lookup
      exact stepHier_no_instances regReg 0 (mkRegisterN 32) rfl sSub inEnv
    · cases h_lookup

/-- Compositional behaviour: children plus (empty) glue, identity abstraction. -/
def regParentBeh : Behavior State Env Env where
  init := initState
  step := fun s i => (specParentStep childSpecReg regReg 1 parentReg s i).1
  out := fun s i => (specParentStep childSpecReg regReg 1 parentReg s i).2

/-- The parent implements its compositional spec, via `implements_compose`. -/
theorem register160hier_implements :
    Implements regReg 2 parentReg regParentBeh id id id (fun _ => True) := by
  apply implements_compose regReg 1 parentReg parentReg_wellwired
    regParentBeh id id id (fun _ => True) trivial rfl
    childSpecReg reg_child_atoms
  refine ⟨fun _ _ _ => trivial, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

/-! ## Register smoke on a small hierarchy (sequential)

Parent output wires never hold state — child DFF states live under scoped
names (`instScope`), and surface at parent outputs on the following cycle.
The checks below pin that threading on a 3-bit hierarchy ([2,1] slices, same
construction as the 160-bit parent above): capture lands scoped, reset clears
a set bit through the hierarchy, and a captured bit is visible at parent
outputs end to end on the next cycle. -/

/-- Small registry: flat 2-bit and 1-bit building blocks. -/
def regReg3 : ModuleRegistry :=
  [("Register2", mkRegisterN 2), ("Register1", mkRegisterN 1)]

/-- Small parent under smoke test (2+1 slices). -/
def parentReg3 : Circuit := mkRegisterNHierarchical 3

/-- Spot-check: capture lands in scoped child state. -/
theorem register3hier_spot_capture :
    (stepHier regReg3 2 parentReg3 initState
      (mkEnv [(Wire.mk "d_0", true), (Wire.mk "reset", false)])).1
      (Wire.mk "reg_0_to_1/q_0") = true
    ∧ (stepHier regReg3 2 parentReg3 initState
      (mkEnv [(Wire.mk "d_0", true), (Wire.mk "reset", false)])).1
      (Wire.mk "reg_0_to_1/q_1") = false := by
  native_decide

/-- Spot-check: reset clears a set bit, through the hierarchy. -/
theorem register3hier_spot_reset :
    (stepHier regReg3 2 parentReg3
      (fun w => w == Wire.mk "reg_0_to_1/q_0")
      (mkEnv [(Wire.mk "d_0", true), (Wire.mk "reset", true)])).1
      (Wire.mk "reg_0_to_1/q_0") = false := by
  native_decide

/-- Spot-check end to end: a captured bit is visible at parent outputs on the
    next cycle. -/
theorem register3hier_spot_output2cycle :
    let s1 := (stepHier regReg3 2 parentReg3 initState
      (mkEnv [(Wire.mk "d_0", true), (Wire.mk "reset", false)])).1
    (stepHier regReg3 2 parentReg3 s1
      (mkEnv [(Wire.mk "d_0", false), (Wire.mk "reset", false)])).2
      (Wire.mk "q_0") = true
    ∧ (stepHier regReg3 2 parentReg3 s1
      (mkEnv [(Wire.mk "d_0", false), (Wire.mk "reset", false)])).2
      (Wire.mk "q_1") = false := by
  native_decide

end Shoumei.Verification.CompositionDemos
