/-
Verification/Refinements.lean - Typed Refinement Atom Registry

Registers proven `Circuit satisfies Behavior` atoms. Constructing a
`RefinementAtom` requires an `Implements` (sequential) or `ImplementsComb`
(combinational) proof term, preventing unproven stubs from being registered.

Collected in `allRefinements` and validated against the emitted circuit
registry by `lake exe generate_all --export-refinements`.
-/

import Shoumei.DSL
import Shoumei.DSL.PortResolve
import Shoumei.Semantics
import Shoumei.Semantics.Hierarchical
import Shoumei.Temporal.Trace
import Shoumei.Verification.Compositional
import Shoumei.Verification.Implements
import Shoumei.Verification.CompositionDemos
import Shoumei.Verification.ALU32HierBridge

-- Pilot atom circuits and proofs
import Shoumei.Examples.Adder
import Shoumei.Examples.AdderProofs
import Shoumei.Circuits.Combinational.LogicUnit
import Shoumei.Circuits.Combinational.LogicUnitProofs
import Shoumei.Circuits.Combinational.MuxTree
import Shoumei.Circuits.Combinational.MuxTreeProofs
import Shoumei.Circuits.Combinational.RippleCarryAdder
import Shoumei.Circuits.Combinational.RippleCarryAdderProofs
import Shoumei.Circuits.Combinational.Comparator
import Shoumei.Circuits.Combinational.ComparatorProofs
import Shoumei.Circuits.Combinational.Popcount
import Shoumei.Circuits.Combinational.PopcountProofs
import Shoumei.Circuits.Combinational.ALU
import Shoumei.Reflection.CompileCircuit
import Shoumei.Reflection.BitVecPacking
import Shoumei.Reflection.ALUSymbolic
import Shoumei.Circuits.Sequential.DFF
import Shoumei.Circuits.Sequential.DFFProofs
import Shoumei.Circuits.Sequential.Register
import Shoumei.Circuits.Sequential.RegisterWordProofs
import Shoumei.Circuits.Sequential.Queue
import Shoumei.Circuits.Sequential.Queue1Bridge

namespace Shoumei.Verification.Refinements

open Shoumei
open Shoumei.DSL.PortResolve
open Shoumei.Semantics
open Shoumei.Semantics.Hierarchical
open Shoumei.Verification
open Shoumei.Verification.CompositionDemos
open Shoumei.Examples
open Shoumei.Reflection
open Shoumei.Circuits.Combinational
open Shoumei.Circuits.Sequential
open Shoumei.Reflection.ALUSymbolic

/-- A registered refinement atom coupling an emitted circuit to a verified
    behavioral specification via an inductive `Implements` proof. -/
inductive RefinementAtom where
  | sequential {σ ι ω : Type}
      (moduleName  : String)
      (specName    : String)
      (circuit     : Circuit)
      (reg         : ModuleRegistry)
      (fuel        : Nat)
      (behavior    : Behavior σ ι ω)
      (absS        : State → σ)
      (encI        : ι → Env)
      (decO        : Env → ω)
      (inv         : State → Prop)
      (non_vacuous : NonVacuousBehavior behavior)
      (proof       : Implements reg fuel circuit behavior absS encI decO inv) : RefinementAtom
  | combinational {ι ω : Type}
      (moduleName  : String)
      (specName    : String)
      (circuit     : Circuit)
      (reg         : ModuleRegistry)
      (fuel        : Nat)
      (behavior    : CombBehavior ι ω)
      (encI        : ι → Env)
      (decO        : Env → ω)
      (non_vacuous : NonVacuousCombBehavior behavior)
      (proof       : ImplementsComb reg fuel circuit behavior encI decO) : RefinementAtom
def RefinementAtom.moduleName : RefinementAtom → String
  | .sequential nm .. => nm
  | .combinational nm .. => nm

def RefinementAtom.specName : RefinementAtom → String
  | .sequential _ sp .. => sp
  | .combinational _ sp .. => sp

def RefinementAtom.circuit : RefinementAtom → Circuit
  | .sequential _ _ c .. => c
  | .combinational _ _ c .. => c

def RefinementAtom.isSequential : RefinementAtom → Bool
  | .sequential .. => true
  | .combinational .. => false

/-! ## Pilot Refinement Atoms -/

-- ── 1. FullAdder (Combinational, 1-bit binary adder with carry) ──

def fullAdderCombBehavior : CombBehavior (Bool × Bool × Bool) (Bool × Bool) where
  eval := fun (a, b, cin) =>
    let sum := xor (xor a b) cin
    let cout := (a && b) || (cin && xor a b)
    (sum, cout)

theorem fullAdder_eval_agree (i : Bool × Bool × Bool) :
    let (a, b, cin) := i
    let env := makeAdderEnv a b cin
    (getSumOutput (evalCircuit fullAdderCircuit env),
     getCoutOutput (evalCircuit fullAdderCircuit env)) =
    fullAdderCombBehavior.eval i := by
  obtain ⟨a, b, cin⟩ := i
  cases a <;> cases b <;> cases cin <;> rfl

theorem fullAdder_non_vacuous : NonVacuousCombBehavior fullAdderCombBehavior := by
  refine ⟨(false, false, false), (true, false, false), by decide⟩

def fullAdder_atom : RefinementAtom :=
  .combinational
    "FullAdder"
    "FullAdderArithSpec"
    fullAdderCircuit
    [] 1
    fullAdderCombBehavior
    (fun (a, b, cin) => makeAdderEnv a b cin)
    (fun env => (getSumOutput env, getCoutOutput env))
    fullAdder_non_vacuous
    (implementsComb_of_flat [] 0 fullAdderCircuit rfl
      fullAdderCombBehavior
      (fun (a, b, cin) => makeAdderEnv a b cin)
      (fun env => (getSumOutput env, getCoutOutput env))
      fullAdder_eval_agree)

-- ── 2. LogicUnit4 (Combinational, 4-bit bitwise logic unit) ──

def logicUnit4CombBehavior :
    CombBehavior (Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool)
                 (Bool × Bool × Bool × Bool) where
  eval := fun (a0, a1, a2, a3, b0, b1, b2, b3, op0, op1) =>
    (logicOp op1 op0 a0 b0,
     logicOp op1 op0 a1 b1,
     logicOp op1 op0 a2 b2,
     logicOp op1 op0 a3 b3)

def logicUnit4EncI (i : Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool) : Env :=
  let (a0, a1, a2, a3, b0, b1, b2, b3, op0, op1) := i
  (makeLu4WireMap a0 a1 a2 a3 b0 b1 b2 b3 op0 op1).lookup

def logicUnit4DecO (env : Env) : Bool × Bool × Bool × Bool :=
  (env (Wire.mk "result_0"),
   env (Wire.mk "result_1"),
   env (Wire.mk "result_2"),
   env (Wire.mk "result_3"))

private def checkLu4Tuple (a0 a1 a2 a3 b0 b1 b2 b3 op0 op1 : Bool) : Bool :=
  let m := makeLu4WireMap a0 a1 a2 a3 b0 b1 b2 b3 op0 op1
  let res := compileCircuit mkLogicUnit4 m
  (res.lookup (Wire.mk "result_0"),
   res.lookup (Wire.mk "result_1"),
   res.lookup (Wire.mk "result_2"),
   res.lookup (Wire.mk "result_3")) == logicUnit4CombBehavior.eval (a0, a1, a2, a3, b0, b1, b2, b3, op0, op1)

private theorem checkLu4Tuple_all :
  ∀ a0 a1 a2 a3 b0 b1 b2 b3 op0 op1 : Bool, checkLu4Tuple a0 a1 a2 a3 b0 b1 b2 b3 op0 op1 = true := by
  native_decide

theorem logicUnit4_eval_agree (i : Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool) :
    logicUnit4DecO (evalCircuit mkLogicUnit4 (logicUnit4EncI i)) = logicUnit4CombBehavior.eval i := by
  obtain ⟨a0, a1, a2, a3, b0, b1, b2, b3, op0, op1⟩ := i
  dsimp [logicUnit4DecO, logicUnit4EncI]
  let m := makeLu4WireMap a0 a1 a2 a3 b0 b1 b2 b3 op0 op1
  have h_comp := compileCircuit_correct mkLogicUnit4 m m.lookup (fun _ => rfl)
  have h_tup := checkLu4Tuple_all a0 a1 a2 a3 b0 b1 b2 b3 op0 op1
  dsimp [checkLu4Tuple] at h_tup
  simp only [beq_iff_eq] at h_tup
  rw [← h_comp (Wire.mk "result_0"),
      ← h_comp (Wire.mk "result_1"),
      ← h_comp (Wire.mk "result_2"),
      ← h_comp (Wire.mk "result_3")]
  exact h_tup

theorem logicUnit4_non_vacuous : NonVacuousCombBehavior logicUnit4CombBehavior := by
  refine ⟨(false, false, false, false, false, false, false, false, false, false),
          (true, true, true, true, true, true, true, true, false, false), by decide⟩

def logicUnit4_atom : RefinementAtom :=
  .combinational
    "LogicUnit4"
    "LogicUnit4BitwiseSpec"
    mkLogicUnit4
    [] 1
    logicUnit4CombBehavior
    logicUnit4EncI
    logicUnit4DecO
    logicUnit4_non_vacuous
    (implementsComb_of_flat [] 0 mkLogicUnit4 rfl
      logicUnit4CombBehavior
      logicUnit4EncI
      logicUnit4DecO
      logicUnit4_eval_agree)

-- ── 3. Mux4x1 (Combinational, 4:1 multiplexer) ──

def mux4x1CombBehavior : CombBehavior (Bool × Bool × Bool × Bool × Bool × Bool) Bool where
  eval := fun (in0, in1, in2, in3, sel0, sel1) => expectedMux4 in0 in1 in2 in3 sel0 sel1

def mux4x1EncI (i : Bool × Bool × Bool × Bool × Bool × Bool) : Env :=
  let (in0, in1, in2, in3, sel0, sel1) := i
  (makeMux4x1WireMap in0 in1 in2 in3 sel0 sel1).lookup

def mux4x1DecO (env : Env) : Bool :=
  env (Wire.mk "out_0")

private def checkMux4x1Tuple (in0 in1 in2 in3 sel0 sel1 : Bool) : Bool :=
  let m := makeMux4x1WireMap in0 in1 in2 in3 sel0 sel1
  let res := compileCircuit mkMux4x1 m
  res.lookup (Wire.mk "out_0") == expectedMux4 in0 in1 in2 in3 sel0 sel1

private theorem checkMux4x1Tuple_all :
  ∀ in0 in1 in2 in3 sel0 sel1 : Bool, checkMux4x1Tuple in0 in1 in2 in3 sel0 sel1 = true := by
  native_decide

theorem mux4x1_eval_agree (i : Bool × Bool × Bool × Bool × Bool × Bool) :
    mux4x1DecO (evalCircuit mkMux4x1 (mux4x1EncI i)) = mux4x1CombBehavior.eval i := by
  obtain ⟨in0, in1, in2, in3, sel0, sel1⟩ := i
  dsimp [mux4x1DecO, mux4x1EncI, mux4x1CombBehavior]
  let m := makeMux4x1WireMap in0 in1 in2 in3 sel0 sel1
  have h_comp := compileCircuit_correct mkMux4x1 m m.lookup (fun _ => rfl) (Wire.mk "out_0")
  have h_tup := checkMux4x1Tuple_all in0 in1 in2 in3 sel0 sel1
  dsimp [checkMux4x1Tuple] at h_tup
  simp only [beq_iff_eq] at h_tup
  rw [← h_comp]
  exact h_tup

theorem mux4x1_non_vacuous : NonVacuousCombBehavior mux4x1CombBehavior := by
  refine ⟨(false, false, false, false, false, false), (true, false, false, false, false, false), by decide⟩

def mux4x1_atom : RefinementAtom :=
  .combinational
    "Mux4x1"
    "Mux4x1RoutingSpec"
    mkMux4x1
    [] 1
    mux4x1CombBehavior
    mux4x1EncI
    mux4x1DecO
    mux4x1_non_vacuous
    (implementsComb_of_flat [] 0 mkMux4x1 rfl
      mux4x1CombBehavior
      mux4x1EncI
      mux4x1DecO
      mux4x1_eval_agree)

-- ── BitVec Result Decoding (Shared between Mux4x32 and ALU32) ──

private theorem readWiresAsNat_agree (c : Circuit) (m : WireMap) (env : Env)
    (h_comp : ∀ w, (compileCircuit c m).lookup w = evalCircuit c env w)
    (name : String) :
    ∀ k : Nat, readWiresAsNat (evalCircuit c env) name k = readWiresAsNatMap (compileCircuit c m) name k
  | 0 => rfl
  | k + 1 => by
    dsimp [readWiresAsNat, readWiresAsNatMap]
    rw [← h_comp (Wire.mk s!"{name}_{k}")]
    rw [readWiresAsNat_agree c m env h_comp name k]

-- ── 4. Mux4x32 (Combinational, 4:1 32-bit multiplexer building block) ──

def mux4x32CombBehavior : CombBehavior (BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × Bool × Bool) (BitVec 32) where
  eval := fun (in0, in1, in2, in3, sel0, sel1) => mux4x32Spec in0 in1 in2 in3 sel0 sel1

def mux4x32EncI (i : BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × Bool × Bool) : Env :=
  let (in0, in1, in2, in3, sel0, sel1) := i
  (makeMux4x32InitMap in0 in1 in2 in3 sel0 sel1).lookup

def mux4x32DecO (env : Env) : BitVec 32 :=
  readResultBitVec "out" 32 env

theorem mux4x32_eval_agree (i : BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × Bool × Bool) :
    mux4x32DecO (evalCircuit mkMux4x32 (mux4x32EncI i)) = mux4x32CombBehavior.eval i := by
  obtain ⟨in0, in1, in2, in3, sel0, sel1⟩ := i
  have h_comp := compileCircuit_correct mkMux4x32 (makeMux4x32InitMap in0 in1 in2 in3 sel0 sel1)
    (mux4x32EncI (in0, in1, in2, in3, sel0, sel1)) (fun _ => rfl)
  dsimp [mux4x32DecO, readResultBitVec, mux4x32CombBehavior]
  have h_nat := readWiresAsNat_agree mkMux4x32 (makeMux4x32InitMap in0 in1 in2 in3 sel0 sel1)
    (mux4x32EncI (in0, in1, in2, in3, sel0, sel1)) h_comp "out" 32
  rw [h_nat]
  exact evalMux4x32_correct in0 in1 in2 in3 sel0 sel1

theorem mux4x32_non_vacuous : NonVacuousCombBehavior mux4x32CombBehavior := by
  refine ⟨(0, 0, 0, 0, false, false), (1, 0, 0, 0, false, false), by decide⟩

def mux4x32_atom : RefinementAtom :=
  .combinational
    "Mux4x32"
    "Mux4x32SliceSpec"
    mkMux4x32
    [] 1
    mux4x32CombBehavior
    mux4x32EncI
    mux4x32DecO
    mux4x32_non_vacuous
    (implementsComb_of_flat [] 0 mkMux4x32 rfl
      mux4x32CombBehavior
      mux4x32EncI
      mux4x32DecO
      mux4x32_eval_agree)

-- ── 5. Mux8x32 (Combinational, Hierarchical 8:1 MUX with word-level routing spec) ──

theorem mux8x32_eval_agree (i : (Fin 8 → BitVec 32) × (Bool × Bool × Bool)) :
    mux8x32DecO (evalCircuit mkMux8x32 (mux8x32EncI i)) = mux8x32CombBehavior.eval i := by
  obtain ⟨inputs, sel0, sel1, sel2⟩ := i
  have h_comp := compileCircuit_correct mkMux8x32 (makeMux8x32InitMap inputs sel0 sel1 sel2)
    (mux8x32EncI (inputs, sel0, sel1, sel2)) (fun _ => rfl)
  dsimp [mux8x32DecO, readResultBitVec, mux8x32CombBehavior]
  have h_nat := readWiresAsNat_agree mkMux8x32 (makeMux8x32InitMap inputs sel0 sel1 sel2)
    (mux8x32EncI (inputs, sel0, sel1, sel2)) h_comp "out" 32
  rw [h_nat]
  exact evalMux8x32_correct inputs sel0 sel1 sel2

def mux8x32_atom : RefinementAtom :=
  .combinational
    "Mux8x32"
    "Mux8x32Spec"
    parentMux
    regMux 2
    mux8x32CombBehavior
    mux8x32EncI
    mux8x32DecO
    mux8x32_non_vacuous
    mux8x32hier_implements

-- ── 6. RippleCarryAdder4 (Combinational, 4-bit addition with carry) ──

def rca4CombBehavior :
    CombBehavior (Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool)
                 (Bool × Bool × Bool × Bool × Bool) where
  eval := fun (a0, a1, a2, a3, b0, b1, b2, b3, cin) =>
    let sumNat := bits4ToNat a0 a1 a2 a3 + bits4ToNat b0 b1 b2 b3 + (if cin then 1 else 0)
    (sumNat % 2 == 1,
     (sumNat / 2) % 2 == 1,
     (sumNat / 4) % 2 == 1,
     (sumNat / 8) % 2 == 1,
     (sumNat / 16) % 2 == 1)

def rca4EncI (i : Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool) : Env :=
  let (a0, a1, a2, a3, b0, b1, b2, b3, cin) := i
  (makeRca4WireMap a0 a1 a2 a3 b0 b1 b2 b3 cin).lookup

def rca4DecO (env : Env) : Bool × Bool × Bool × Bool × Bool :=
  (env (Wire.mk "sum_0"),
   env (Wire.mk "sum_1"),
   env (Wire.mk "sum_2"),
   env (Wire.mk "sum_3"),
   env (Wire.mk "cout"))

private def checkRca4Tuple (a0 a1 a2 a3 b0 b1 b2 b3 cin : Bool) : Bool :=
  let m := makeRca4WireMap a0 a1 a2 a3 b0 b1 b2 b3 cin
  let res := compileCircuit mkRippleCarryAdder4 m
  (res.lookup (Wire.mk "sum_0"),
   res.lookup (Wire.mk "sum_1"),
   res.lookup (Wire.mk "sum_2"),
   res.lookup (Wire.mk "sum_3"),
   res.lookup (Wire.mk "cout")) == rca4CombBehavior.eval (a0, a1, a2, a3, b0, b1, b2, b3, cin)

private theorem checkRca4Tuple_all :
  ∀ a0 a1 a2 a3 b0 b1 b2 b3 cin : Bool, checkRca4Tuple a0 a1 a2 a3 b0 b1 b2 b3 cin = true := by
  native_decide

theorem rca4_eval_agree (i : Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool) :
    rca4DecO (evalCircuit mkRippleCarryAdder4 (rca4EncI i)) = rca4CombBehavior.eval i := by
  obtain ⟨a0, a1, a2, a3, b0, b1, b2, b3, cin⟩ := i
  dsimp [rca4DecO, rca4EncI]
  let m := makeRca4WireMap a0 a1 a2 a3 b0 b1 b2 b3 cin
  have h_comp := compileCircuit_correct mkRippleCarryAdder4 m m.lookup (fun _ => rfl)
  have h_tup := checkRca4Tuple_all a0 a1 a2 a3 b0 b1 b2 b3 cin
  dsimp [checkRca4Tuple] at h_tup
  simp only [beq_iff_eq] at h_tup
  rw [← h_comp (Wire.mk "sum_0"),
      ← h_comp (Wire.mk "sum_1"),
      ← h_comp (Wire.mk "sum_2"),
      ← h_comp (Wire.mk "sum_3"),
      ← h_comp (Wire.mk "cout")]
  exact h_tup

theorem rca4_non_vacuous : NonVacuousCombBehavior rca4CombBehavior := by
  refine ⟨(false, false, false, false, false, false, false, false, false),
          (true, false, false, false, false, false, false, false, false), by decide⟩

def rca4_atom : RefinementAtom :=
  .combinational
    "RippleCarryAdder4"
    "RCA4ArithmeticSpec"
    mkRippleCarryAdder4
    [] 1
    rca4CombBehavior
    rca4EncI
    rca4DecO
    rca4_non_vacuous
    (implementsComb_of_flat [] 0 mkRippleCarryAdder4 rfl
      rca4CombBehavior
      rca4EncI
      rca4DecO
      rca4_eval_agree)

-- ── 7. Comparator4 (Combinational, 4-bit unsigned/signed comparison) ──

def cmp4CombBehavior :
    CombBehavior (Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool)
                 (Bool × Bool × Bool × Bool × Bool) where
  eval := fun (a0, a1, a2, a3, b0, b1, b2, b3) =>
    let uA := cmpBits4ToNat a0 a1 a2 a3
    let uB := cmpBits4ToNat b0 b1 b2 b3
    let sA := cmpBits4ToInt a0 a1 a2 a3
    let sB := cmpBits4ToInt b0 b1 b2 b3
    (uA == uB, uA < uB, uA > uB, sA < sB, sA > sB)

def cmp4EncI (i : Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool) : Env :=
  let (a0, a1, a2, a3, b0, b1, b2, b3) := i
  (makeCmp4WireMap a0 a1 a2 a3 b0 b1 b2 b3).lookup

def cmp4DecO (env : Env) : Bool × Bool × Bool × Bool × Bool :=
  (env (Wire.mk "eq"),
   env (Wire.mk "ltu"),
   env (Wire.mk "gtu"),
   env (Wire.mk "lt"),
   env (Wire.mk "gt"))

private def checkCmp4Tuple (a0 a1 a2 a3 b0 b1 b2 b3 : Bool) : Bool :=
  let m := makeCmp4WireMap a0 a1 a2 a3 b0 b1 b2 b3
  let res := compileCircuit mkComparator4 m
  (res.lookup (Wire.mk "eq"),
   res.lookup (Wire.mk "ltu"),
   res.lookup (Wire.mk "gtu"),
   res.lookup (Wire.mk "lt"),
   res.lookup (Wire.mk "gt")) == cmp4CombBehavior.eval (a0, a1, a2, a3, b0, b1, b2, b3)

private theorem checkCmp4Tuple_all :
  ∀ a0 a1 a2 a3 b0 b1 b2 b3 : Bool, checkCmp4Tuple a0 a1 a2 a3 b0 b1 b2 b3 = true := by
  native_decide

theorem cmp4_eval_agree (i : Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool) :
    cmp4DecO (evalCircuit mkComparator4 (cmp4EncI i)) = cmp4CombBehavior.eval i := by
  obtain ⟨a0, a1, a2, a3, b0, b1, b2, b3⟩ := i
  dsimp [cmp4DecO, cmp4EncI]
  let m := makeCmp4WireMap a0 a1 a2 a3 b0 b1 b2 b3
  have h_comp := compileCircuit_correct mkComparator4 m m.lookup (fun _ => rfl)
  have h_tup := checkCmp4Tuple_all a0 a1 a2 a3 b0 b1 b2 b3
  dsimp [checkCmp4Tuple] at h_tup
  simp only [beq_iff_eq] at h_tup
  rw [← h_comp (Wire.mk "eq"),
      ← h_comp (Wire.mk "ltu"),
      ← h_comp (Wire.mk "gtu"),
      ← h_comp (Wire.mk "lt"),
      ← h_comp (Wire.mk "gt")]
  exact h_tup

theorem comparator4_non_vacuous : NonVacuousCombBehavior cmp4CombBehavior := by
  refine ⟨(false, false, false, false, false, false, false, false),
          (true, false, false, false, false, false, false, false), by decide⟩

def comparator4_atom : RefinementAtom :=
  .combinational
    "Comparator4"
    "Comparator4PredicateSpec"
    mkComparator4
    [] 1
    cmp4CombBehavior
    cmp4EncI
    cmp4DecO
    comparator4_non_vacuous
    (implementsComb_of_flat [] 0 mkComparator4 rfl
      cmp4CombBehavior
      cmp4EncI
      cmp4DecO
      cmp4_eval_agree)

-- ── 8. Popcount8 (Combinational, 8-bit population count) ──

def popcount8CombBehavior :
    CombBehavior (Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool) Nat where
  eval := fun (b0, b1, b2, b3, b4, b5, b6, b7) =>
    popcount8Spec b0 b1 b2 b3 b4 b5 b6 b7

def popcount8EncI (i : Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool) : Env :=
  let (b0, b1, b2, b3, b4, b5, b6, b7) := i
  (makePopcount8WireMap b0 b1 b2 b3 b4 b5 b6 b7).lookup

def popcount8DecO (env : Env) : Nat :=
  reconstructCount
    (env (Wire.mk "count_0"))
    (env (Wire.mk "count_1"))
    (env (Wire.mk "count_2"))
    (env (Wire.mk "count_3"))

private def checkPop8Tuple (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) : Bool :=
  let m := makePopcount8WireMap b0 b1 b2 b3 b4 b5 b6 b7
  let res := compileCircuit mkPopcount8 m
  reconstructCount
    (res.lookup (Wire.mk "count_0"))
    (res.lookup (Wire.mk "count_1"))
    (res.lookup (Wire.mk "count_2"))
    (res.lookup (Wire.mk "count_3")) == popcount8CombBehavior.eval (b0, b1, b2, b3, b4, b5, b6, b7)

private theorem checkPop8Tuple_all :
  ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool, checkPop8Tuple b0 b1 b2 b3 b4 b5 b6 b7 = true := by
  native_decide

theorem popcount8_eval_agree (i : Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool) :
    popcount8DecO (evalCircuit mkPopcount8 (popcount8EncI i)) = popcount8CombBehavior.eval i := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := i
  dsimp [popcount8DecO, popcount8EncI]
  let m := makePopcount8WireMap b0 b1 b2 b3 b4 b5 b6 b7
  have h_comp := compileCircuit_correct mkPopcount8 m m.lookup (fun _ => rfl)
  have h_tup := checkPop8Tuple_all b0 b1 b2 b3 b4 b5 b6 b7
  dsimp [checkPop8Tuple] at h_tup
  simp only [beq_iff_eq] at h_tup
  rw [← h_comp (Wire.mk "count_0"),
      ← h_comp (Wire.mk "count_1"),
      ← h_comp (Wire.mk "count_2"),
      ← h_comp (Wire.mk "count_3")]
  exact h_tup

theorem popcount8_non_vacuous : NonVacuousCombBehavior popcount8CombBehavior := by
  refine ⟨(false, false, false, false, false, false, false, false),
          (true, false, false, false, false, false, false, false), by decide⟩

def popcount8_atom : RefinementAtom :=
  .combinational
    "Popcount8"
    "Popcount8HammingWeightSpec"
    mkPopcount8
    [] 1
    popcount8CombBehavior
    popcount8EncI
    popcount8DecO
    popcount8_non_vacuous
    (implementsComb_of_flat [] 0 mkPopcount8 rfl
      popcount8CombBehavior
      popcount8EncI
      popcount8DecO
      popcount8_eval_agree)

-- ── 9. ALU32 (Combinational, Hierarchical 32-bit ALU with 10 RV32I arithmetic & logic opcodes) ──

theorem alu32_eval_agree (i : ALUOp × BitVec 32 × BitVec 32) :
    alu32DecO (evalCircuit mkALU32Flat (alu32EncI i)) = alu32CombBehavior.eval i := by
  obtain ⟨op, a, b⟩ := i
  have h_bridge := alu32_bridge op a b
  dsimp [evalALU32] at h_bridge
  dsimp [alu32DecO, alu32EncI, alu32CombBehavior]
  rw [← h_bridge]
  have h_comp := compileCircuit_correct mkALU32Flat (mkALUInitMap a b op.toOpcode)
    (fun w => (mkALUInitMap a b op.toOpcode).lookup w) (fun _ => rfl)
  dsimp [readResultBitVecMap, readResultBitVec]
  have h_nat := readWiresAsNat_agree mkALU32Flat (mkALUInitMap a b op.toOpcode)
    (fun w => (mkALUInitMap a b op.toOpcode).lookup w) h_comp "result" 32
  rw [h_nat]

theorem alu32_non_vacuous : NonVacuousCombBehavior alu32CombBehavior := by
  refine ⟨(.ADD, 0, 0), (.ADD, 1, 0), by decide⟩

def alu32_atom : RefinementAtom :=
  .combinational
    "ALU32"
    "ALU32CompleteRV32ISpec"
    mkALU32
    aluSubCircuitMap 4
    alu32CombBehavior
    alu32EncI
    alu32DecO
    alu32_non_vacuous
    alu32_hier_implements

-- ── 10. DFlipFlop (Sequential, synchronous single-bit D flip-flop) ──

def dffBehavior : Behavior Bool (Bool × Bool) Bool where
  init := false
  step := fun _ (d, rst) => if rst then false else d
  out  := fun s _ => s

def dffEncI (i : Bool × Bool) : Env :=
  let (d, rst) := i
  makeDFFEnv d rst

def dffAbsS (state : State) : Bool :=
  state (Wire.mk "q")

def dffDecO (env : Env) : Bool :=
  env (Wire.mk "q")

theorem dff_step_agree (s : State) (i : Bool × Bool) :
    dffAbsS (evalCycleSequential mkDFlipFlop s (dffEncI i)).1 = dffBehavior.step (dffAbsS s) i := rfl

theorem dff_out_agree (s : State) (i : Bool × Bool) :
    dffDecO (evalCycleSequential mkDFlipFlop s (dffEncI i)).2 = dffBehavior.out (dffAbsS s) i := rfl

theorem dff_non_vacuous : NonVacuousBehavior dffBehavior := by
  refine ⟨false, true, (false, false), (false, false), by decide⟩

def dff_atom : RefinementAtom :=
  .sequential
    "DFlipFlop"
    "DFFSynchronousSpec"
    mkDFlipFlop
    [] 1
    dffBehavior
    dffAbsS
    dffEncI
    dffDecO
    (fun _ => True)
    dff_non_vacuous
    (implements_of_flat_trivial [] 0 mkDFlipFlop rfl
      dffBehavior
      dffAbsS
      dffEncI
      dffDecO
      rfl
      dff_step_agree
      dff_out_agree)

-- ── 11. Register8 (Sequential, 8-bit synchronous register) ──

def register8_atom : RefinementAtom :=
  .sequential
    "Register8"
    "Register8WordSpec"
    mkRegister8
    [] 1
    (registerNBehavior 8)
    (regNAbsS 8)
    registerNEncI
    (regNDecO 8)
    (fun _ => True)
    (registerN_non_vacuous 8 (by decide))
    register8_implements

-- ── 12. Register160 (Sequential, Hierarchical 160-bit register composed of 64+64+32) ──

def register160_atom : RefinementAtom :=
  .sequential
    "Register160"
    "Register160ComposedSpec"
    parentReg
    regReg 2
    (registerNBehavior 160)
    reg160HierAbsS
    registerNEncI
    (regNDecO 160)
    (fun _ => True)
    (registerN_non_vacuous 160 (by decide))
    register160hier_implements

-- ── 13. Queue1 (Width=1, Sequential FIFO queue) ──

def queue1W1Behavior : Behavior (QueueState Bool) (Bool × Bool × Bool) (Bool × Bool) where
  init := QueueState.empty 1
  step := fun q (enq_valid, enq_data, deq_ready) =>
    queue1StepBool q enq_valid deq_ready enq_data
  out  := fun q _ => (!q.isFull, !q.isEmpty)

def queue1W1EncI (i : Bool × Bool × Bool) : Env :=
  let (enq_valid, enq_data, deq_ready) := i
  fun w =>
    if w == Wire.mk "enq_valid" then enq_valid
    else if w == Wire.mk "enq_data_0" then enq_data
    else if w == Wire.mk "deq_ready" then deq_ready
    else if w == Wire.mk "clock" then true
    else if w == Wire.mk "reset" then false
    else false

def queue1W1DecO (env : Env) : Bool × Bool :=
  (env (Wire.mk "enq_ready"), env (Wire.mk "valid"))

theorem queue1W1_init_agree : circuitToQueue1 initState = queue1W1Behavior.init := rfl

theorem queue1W1_step_agree (s : State) (i : Bool × Bool × Bool) :
    circuitToQueue1 (evalCycleSequential q1w1 s (queue1W1EncI i)).1 =
    queue1W1Behavior.step (circuitToQueue1 s) i := by
  obtain ⟨enq_v, enq_d, deq_r⟩ := i
  have h_trans := queue1_w1_transition_correct (s (Wire.mk "valid")) (s (Wire.mk "data_reg_0")) enq_v enq_d deq_r
  exact h_trans

theorem queue1W1_decO_eval (s : State) (enq_v enq_d deq_r : Bool) :
    queue1W1DecO (evalCycleSequential q1w1 s (queue1W1EncI (enq_v, enq_d, deq_r))).2 =
    (!s (Wire.mk "valid"), s (Wire.mk "valid")) := by
  dsimp [queue1W1DecO, evalCycleSequential, q1w1, mkQueue1StructuralComplete, mkQueue1Structural]
  rfl

theorem queue1W1_out_agree (s : State) (i : Bool × Bool × Bool) :
    queue1W1DecO (evalCycleSequential q1w1 s (queue1W1EncI i)).2 =
    queue1W1Behavior.out (circuitToQueue1 s) i := by
  obtain ⟨enq_v, enq_d, deq_r⟩ := i
  rw [queue1W1_decO_eval]
  dsimp [queue1W1Behavior, circuitToQueue1, circuitValid, QueueState.isFull, QueueState.isEmpty]
  cases s (Wire.mk "valid") <;> rfl

theorem queue1W1_non_vacuous : NonVacuousBehavior queue1W1Behavior := by
  refine ⟨QueueState.empty 1, ⟨[true], 1⟩, (false, false, false), (false, false, false), by decide⟩
def queue1W1_atom : RefinementAtom :=
  .sequential
    "Queue1_1"
    "Queue1BitFIFOSpec"
    q1w1
    [] 1
    queue1W1Behavior
    circuitToQueue1
    queue1W1EncI
    queue1W1DecO
    (fun _ => True)
    queue1W1_non_vacuous
    (implements_of_flat_trivial [] 0 q1w1 rfl
      queue1W1Behavior
      circuitToQueue1
      queue1W1EncI
      queue1W1DecO
      queue1W1_init_agree
      queue1W1_step_agree
      queue1W1_out_agree)

/-- The comprehensive registry of all 13 verified refinement atoms. -/
def allRefinements : List RefinementAtom := [
  fullAdder_atom,
  logicUnit4_atom,
  mux4x1_atom,
  mux4x32_atom,
  mux8x32_atom,
  rca4_atom,
  comparator4_atom,
  popcount8_atom,
  alu32_atom,
  dff_atom,
  register8_atom,
  register160_atom,
  queue1W1_atom
]

end Shoumei.Verification.Refinements
