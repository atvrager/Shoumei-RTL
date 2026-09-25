/-
Verification/ALU32HierBridge.lean - Hierarchical ALU32 Refinement Bridge

Bridges the existing symbolic `mkALU32Flat` correctness proof (`alu32_bridge`)
to the emitted depth-3 hierarchical `mkALU32` circuit evaluated via
`evalHier aluSubCircuitMap 4 mkALU32`, using `flatten_sound_depth1` and
`flatten_sound_step` from `Shoumei.Reflection.FlattenSoundness`.
-/

import Shoumei.Reflection.FlattenSoundness
import Shoumei.Reflection.ALUSymbolic
import Shoumei.Verification.Implements

namespace Shoumei.Verification

open Shoumei
open Shoumei.DSL.PortResolve
open Shoumei.Semantics
open Shoumei.Semantics.Hierarchical
open Shoumei.Reflection
open Shoumei.Reflection.ALUSymbolic
open Shoumei.Circuits.Combinational

/-! ## Flat Submodule Preservation under `flattenAllFuel` -/

theorem flattenAllFuel_gates_of_flat (reg : ModuleRegistry) (c : Circuit) (k : Nat)
    (h_inst : c.instances = []) :
    (flattenAllFuel reg c k).gates = c.gates := by
  cases k with
  | zero => rfl
  | succ k' =>
    dsimp [flattenAllFuel]
    rw [preGates_nil reg c h_inst, postGates_nil reg c h_inst, h_inst]
    rfl

theorem evalHier_eq_flattenAllFuel_of_flat (reg : ModuleRegistry) (k : Nat) (c : Circuit)
    (h_inst : c.instances = []) (inEnv : Env) :
    ∀ w ∈ c.outputs,
      evalHier reg (k + 1) c inEnv w = evalCircuit (flattenAllFuel reg c k) inEnv w := by
  intro w _
  rw [evalHier_no_instances reg k c h_inst inEnv]
  dsimp [evalCircuit]
  rw [flattenAllFuel_gates_of_flat reg c k h_inst]

/-! ## Depth-1 Soundness for `mkSubtractor32` (`k = 0` and `k = 1`) -/

def aluRegFlat1 : ModuleRegistry := flattenRegistry aluSubCircuitMap 1
def aluRegFlat2 : ModuleRegistry := flattenRegistry aluSubCircuitMap 2

theorem sub32_wellwired_0 : WellWired aluSubCircuitMap mkSubtractor32 = true := by
  native_decide

theorem sub32_fresh_0 : flattenFreshCheck aluSubCircuitMap mkSubtractor32 = true := by
  native_decide

theorem sub32_children_0 : childrenOKCheck aluSubCircuitMap mkSubtractor32 = true := by
  native_decide

theorem subtractor32_evalHier_eq_flat1 (inEnv : Env) :
    ∀ w ∈ mkSubtractor32.outputs,
      evalHier aluSubCircuitMap 2 mkSubtractor32 inEnv w =
      evalCircuit (flattenAllFuel aluSubCircuitMap mkSubtractor32 1) inEnv w :=
  flatten_sound_depth1 aluSubCircuitMap mkSubtractor32
    sub32_wellwired_0
    (FlattenFresh_of_check aluSubCircuitMap mkSubtractor32 sub32_fresh_0)
    (ChildrenOK_of_check aluSubCircuitMap mkSubtractor32 sub32_children_0)
    inEnv

theorem sub32_wellwired_1 : WellWired aluRegFlat1 mkSubtractor32 = true := by
  native_decide

theorem sub32_fresh_1 : flattenFreshCheck aluRegFlat1 mkSubtractor32 = true := by
  native_decide

theorem sub32_children_1 : childrenOKCheck aluRegFlat1 mkSubtractor32 = true := by
  native_decide

theorem subtractor32_children_sound_1 :
    ∀ inst ∈ mkSubtractor32.instances, ∀ nm sub,
      aluSubCircuitMap.find? (fun p => p.1 == inst.moduleName) = some (nm, sub) →
      ∀ inEnv, ∀ w ∈ sub.outputs,
        evalHier aluSubCircuitMap 2 sub inEnv w =
        evalCircuit (flattenAllFuel aluSubCircuitMap sub 1) inEnv w := by
  intro inst h_inst nm sub h_lookup inEnv
  have h_mod : inst.moduleName = "KoggeStoneAdder32" := by
    clear h_lookup; revert inst h_inst; native_decide
  rw [h_mod] at h_lookup
  change some ("KoggeStoneAdder32", mkKoggeStoneAdder32) = some (nm, sub) at h_lookup
  injection h_lookup with h_pair
  injection h_pair with _ h_sub
  subst h_sub
  exact evalHier_eq_flattenAllFuel_of_flat aluSubCircuitMap 1 mkKoggeStoneAdder32 rfl inEnv

theorem subtractor32_evalHier_eq_flat2 (inEnv : Env) :
    ∀ w ∈ mkSubtractor32.outputs,
      evalHier aluSubCircuitMap 3 mkSubtractor32 inEnv w =
      evalCircuit (flattenAllFuel aluSubCircuitMap mkSubtractor32 2) inEnv w :=
  flatten_sound_step aluSubCircuitMap 1 mkSubtractor32
    sub32_wellwired_1
    (FlattenFresh_of_check aluRegFlat1 mkSubtractor32 sub32_fresh_1)
    (ChildrenOK_of_check aluRegFlat1 mkSubtractor32 sub32_children_1)
    subtractor32_children_sound_1
    inEnv

/-! ## Depth-2 Soundness for `mkComparator32` (`k = 1`) -/

theorem cmp32_wellwired_1 : WellWired aluRegFlat1 mkComparator32 = true := by
  native_decide

theorem cmp32_fresh_1 : flattenFreshCheck aluRegFlat1 mkComparator32 = true := by
  native_decide

theorem cmp32_children_1 : childrenOKCheck aluRegFlat1 mkComparator32 = true := by
  native_decide

theorem comparator32_children_sound_1 :
    ∀ inst ∈ mkComparator32.instances, ∀ nm sub,
      aluSubCircuitMap.find? (fun p => p.1 == inst.moduleName) = some (nm, sub) →
      ∀ inEnv, ∀ w ∈ sub.outputs,
        evalHier aluSubCircuitMap 2 sub inEnv w =
        evalCircuit (flattenAllFuel aluSubCircuitMap sub 1) inEnv w := by
  intro inst h_inst nm sub h_lookup inEnv
  have h_mod : inst.moduleName = "Subtractor32" := by
    clear h_lookup; revert inst h_inst; native_decide
  rw [h_mod] at h_lookup
  change some ("Subtractor32", mkSubtractor32) = some (nm, sub) at h_lookup
  injection h_lookup with h_pair
  injection h_pair with _ h_sub
  subst h_sub
  exact subtractor32_evalHier_eq_flat1 inEnv

theorem comparator32_evalHier_eq_flat2 (inEnv : Env) :
    ∀ w ∈ mkComparator32.outputs,
      evalHier aluSubCircuitMap 3 mkComparator32 inEnv w =
      evalCircuit (flattenAllFuel aluSubCircuitMap mkComparator32 2) inEnv w :=
  flatten_sound_step aluSubCircuitMap 1 mkComparator32
    cmp32_wellwired_1
    (FlattenFresh_of_check aluRegFlat1 mkComparator32 cmp32_fresh_1)
    (ChildrenOK_of_check aluRegFlat1 mkComparator32 cmp32_children_1)
    comparator32_children_sound_1
    inEnv

/-! ## Depth-3 Soundness for `mkALU32` (`k = 2`) -/

theorem alu32_wellwired_2 : WellWired aluRegFlat2 mkALU32 = true := by
  native_decide

theorem alu32_fresh_2 : flattenFreshCheck aluRegFlat2 mkALU32 = true := by
  native_decide

theorem alu32_children_2 : childrenOKCheck aluRegFlat2 mkALU32 = true := by
  native_decide

theorem alu32_children_sound_2 :
    ∀ inst ∈ mkALU32.instances, ∀ nm sub,
      aluSubCircuitMap.find? (fun p => p.1 == inst.moduleName) = some (nm, sub) →
      ∀ inEnv, ∀ w ∈ sub.outputs,
        evalHier aluSubCircuitMap 3 sub inEnv w =
        evalCircuit (flattenAllFuel aluSubCircuitMap sub 2) inEnv w := by
  intro inst _ nm sub h_lookup inEnv
  dsimp [aluSubCircuitMap, List.find?] at h_lookup
  split at h_lookup
  · injection h_lookup with h_pair; injection h_pair with _ h_sub; subst h_sub
    exact evalHier_eq_flattenAllFuel_of_flat aluSubCircuitMap 2 mkKoggeStoneAdder32NoCin rfl inEnv
  · split at h_lookup
    · injection h_lookup with h_pair; injection h_pair with _ h_sub; subst h_sub
      exact evalHier_eq_flattenAllFuel_of_flat aluSubCircuitMap 2 mkKoggeStoneAdder32 rfl inEnv
    · split at h_lookup
      · injection h_lookup with h_pair; injection h_pair with _ h_sub; subst h_sub
        exact subtractor32_evalHier_eq_flat2 inEnv
      · split at h_lookup
        · injection h_lookup with h_pair; injection h_pair with _ h_sub; subst h_sub
          exact comparator32_evalHier_eq_flat2 inEnv
        · split at h_lookup
          · injection h_lookup with h_pair; injection h_pair with _ h_sub; subst h_sub
            exact evalHier_eq_flattenAllFuel_of_flat aluSubCircuitMap 2 mkLogicUnit32 rfl inEnv
          · split at h_lookup
            · injection h_lookup with h_pair; injection h_pair with _ h_sub; subst h_sub
              exact evalHier_eq_flattenAllFuel_of_flat aluSubCircuitMap 2 mkShifter32 rfl inEnv
            · cases h_lookup

theorem alu32_evalHier_eq_flat (env : Env) :
    ∀ w ∈ mkALU32.outputs,
      evalHier aluSubCircuitMap 4 mkALU32 env w =
      evalCircuit mkALU32Flat env w :=
  flatten_sound_step aluSubCircuitMap 2 mkALU32
    alu32_wellwired_2
    (FlattenFresh_of_check aluRegFlat2 mkALU32 alu32_fresh_2)
    (ChildrenOK_of_check aluRegFlat2 mkALU32 alu32_children_2)
    alu32_children_sound_2
    env

theorem alu32_out_mem_check :
    (List.range 32).all (fun k => mkALU32.outputs.any (· == Wire.mk s!"{"result"}_{k}")) = true := by
  native_decide

theorem alu32_out_mem (k : Nat) (hk : k < 32) :
    Wire.mk s!"{"result"}_{k}" ∈ mkALU32.outputs :=
  mem_of_any_eq_true _ _ ((List.all_eq_true.mp alu32_out_mem_check) k (List.mem_range.mpr hk))

theorem readWiresAsNat_evalHier_alu32 (m : WireMap) (env : Env)
    (h_comp : ∀ w, (compileCircuit mkALU32Flat m).lookup w = evalCircuit mkALU32Flat env w) :
    ∀ k ≤ 32,
      readWiresAsNat (evalHier aluSubCircuitMap 4 mkALU32 env) "result" k =
      readWiresAsNatMap (compileCircuit mkALU32Flat m) "result" k
  | 0, _ => rfl
  | k + 1, hk => by
    dsimp [readWiresAsNat, readWiresAsNatMap]
    have h_out := alu32_evalHier_eq_flat env (Wire.mk s!"{"result"}_{k}")
      (alu32_out_mem k (by omega))
    rw [h_out, ← h_comp (Wire.mk s!"{"result"}_{k}")]
    rw [readWiresAsNat_evalHier_alu32 m env h_comp k (by omega)]

def alu32CombBehavior : CombBehavior (ALUOp × BitVec 32 × BitVec 32) (BitVec 32) where
  eval := fun (op, a, b) => aluSemantics op a b

def alu32EncI (i : ALUOp × BitVec 32 × BitVec 32) : Env :=
  let (op, a, b) := i
  fun w => (mkALUInitMap a b op.toOpcode).lookup w

def alu32DecO (env : Env) : BitVec 32 :=
  readResultBitVec "result" 32 env

theorem alu32_hier_implements :
    ImplementsComb aluSubCircuitMap 4 mkALU32 alu32CombBehavior alu32EncI alu32DecO := by
  intro ⟨op, a, b⟩
  have h_bridge := alu32_bridge op a b
  dsimp [evalALU32] at h_bridge
  dsimp [alu32DecO, alu32EncI, alu32CombBehavior, readResultBitVecMap, readResultBitVec] at h_bridge ⊢
  rw [← h_bridge]
  have h_comp := compileCircuit_correct mkALU32Flat (mkALUInitMap a b op.toOpcode)
    (fun w => (mkALUInitMap a b op.toOpcode).lookup w) (fun _ => rfl)
  rw [readWiresAsNat_evalHier_alu32 (mkALUInitMap a b op.toOpcode)
    (fun w => (mkALUInitMap a b op.toOpcode).lookup w) h_comp 32 (by omega)]

end Shoumei.Verification
