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
import Shoumei.Circuits.Combinational.MuxTreeProofs
import Shoumei.Circuits.Combinational.Mux8x32HierProofs
import Shoumei.Circuits.Sequential.RegisterWordProofs
import Shoumei.Reflection.BitVecPacking

namespace Shoumei.Verification.CompositionDemos

open Shoumei
open Shoumei.DSL.PortResolve
open Shoumei.Semantics
open Shoumei.Semantics.Hierarchical
open Shoumei.Circuits.Combinational
open Shoumei.Circuits.Sequential
open Shoumei.Reflection

/-! ## Mux8x32 hierarchical composition (combinational) -/

/-- Minimal registry for the Mux demo: the flat 4x32 building block. -/
def regMux : ModuleRegistry := [("Mux4x32", mkMux4x32)]

/-- The hierarchical parent under composition. -/
def parentMux : Circuit := mkMux8xNHierarchical 32

/-- Word-level 8:1 Mux behaviour: route the selected input word to the output. -/
def mux8x32CombBehavior : CombBehavior ((Fin 8 → BitVec 32) × (Bool × Bool × Bool)) (BitVec 32) where
  eval := fun (inputs, (sel0, sel1, sel2)) => mux8x32Spec inputs sel0 sel1 sel2

def mux8x32EncI (i : (Fin 8 → BitVec 32) × (Bool × Bool × Bool)) : Env :=
  let (inputs, (sel0, sel1, sel2)) := i
  (makeMux8x32InitMap inputs sel0 sel1 sel2).lookup

def mux8x32DecO (env : Env) : BitVec 32 :=
  readResultBitVec "out" 32 env

theorem mux8x32_non_vacuous : NonVacuousCombBehavior mux8x32CombBehavior := by
  refine ⟨(fun _ => 0, (false, false, false)), (fun i => if i == 0 then 1 else 0, (false, false, false)), by decide⟩

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

/-- Glue obligation: the spec-assembled hierarchical evaluation of `parentMux`
    decodes to the word-level `mux8x32CombBehavior`. -/
theorem mux8x32hier_glue :
    GlueCombCommutes regMux parentMux mux8x32CombBehavior mux8x32EncI mux8x32DecO childSpecMux := by
  intro ⟨inputs, sel0, sel1, sel2⟩
  rw [← evalHier_eq_specParentEval regMux 1 parentMux childSpecMux mux_child_atoms]
  have h_comp := compileCircuit_correct mkMux8x32HierFlat (makeMux8x32InitMap inputs sel0 sel1 sel2)
    (mux8x32EncI (inputs, sel0, sel1, sel2)) (fun _ => rfl)
  dsimp [mux8x32DecO, readResultBitVec, mux8x32CombBehavior]
  have h_nat := readWiresAsNat_evalHier_mux8x32Hier (makeMux8x32InitMap inputs sel0 sel1 sel2)
    (mux8x32EncI (inputs, sel0, sel1, sel2)) h_comp 32 (Nat.le_refl 32)
  change BitVec.ofNat 32 (readWiresAsNat (evalHier regMux8x32 2 mkMux8x32Hierarchical
    (mux8x32EncI (inputs, sel0, sel1, sel2))) "out" 32) = mux8x32Spec inputs sel0 sel1 sel2
  rw [h_nat]
  exact evalMux8x32HierFlat_correct inputs sel0 sel1 sel2

/-- The hierarchical `Mux8x32` implements the word-level 8:1 routing spec via
    `implementsComb_compose`. -/
theorem mux8x32hier_implements :
    ImplementsComb regMux 2 parentMux mux8x32CombBehavior mux8x32EncI mux8x32DecO :=
  implementsComb_compose regMux 1 parentMux parentMux_wellwired
    mux8x32CombBehavior mux8x32EncI mux8x32DecO childSpecMux mux_child_atoms
    mux8x32hier_glue

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

/-- Glue obligation: the spec-assembled hierarchical cycle of `parentReg`
    commutes with the 160-bit word-level `registerNBehavior 160`. -/
theorem register160hier_glue :
    GlueCommutes regReg 1 parentReg (registerNBehavior 160)
      reg160HierAbsS registerNEncI (regNDecO 160) (fun _ => True) childSpecReg :=
  ⟨fun _ _ _ => trivial,
   fun s i _ => reg160Hier_step_agree s i,
   fun s i _ => reg160Hier_out_agree s i⟩

/-- The hierarchical `Register160` (`64 + 64 + 32`) implements the 160-bit
    word-level synchronous register spec via `implements_compose`. -/
theorem register160hier_implements :
    Implements regReg 2 parentReg (registerNBehavior 160)
      reg160HierAbsS registerNEncI (regNDecO 160) (fun _ => True) :=
  implements_compose regReg 1 parentReg parentReg_wellwired
    (registerNBehavior 160) reg160HierAbsS registerNEncI (regNDecO 160)
    (fun _ => True) trivial reg160Hier_init_agree
    childSpecReg reg_child_atoms register160hier_glue

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
