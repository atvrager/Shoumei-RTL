import Shoumei.Circuits.Combinational.Comparator
import Shoumei.Reflection.CompileCircuit

namespace Shoumei.Circuits.Combinational

open Shoumei
open Shoumei.Reflection

-- Comparator4 structural properties
theorem comparator4_structure :
  mkComparator4.gates.length = 44 ∧  -- Detailed breakdown:
                                      -- 4 NOT (b_inv) + 20 RCA + 3 OR tree
                                      -- + 1 NOT (eq_raw) + 1 BUF (eq)
                                      -- + 1 BUF (ltu_raw) + 1 BUF (ltu)
                                      -- + 6 signed lt + 1 BUF (lt)
                                      -- + 3 gtu + 2 gt + 1 eq_inv (shared)
  mkComparator4.inputs.length = 9 ∧
  mkComparator4.outputs.length = 5 := by native_decide

-- Comparator8 structural properties
theorem comparator8_structure :
  mkComparator8.gates.length = 72 ∧
  mkComparator8.inputs.length = 17 ∧
  mkComparator8.outputs.length = 5 := by native_decide

-- Comparator32 structural properties (KSA-based via Subtractor32 instance)
theorem comparator32_structure :
  mkComparator32.gates.length = 50 ∧
  mkComparator32.inputs.length = 65 ∧
  mkComparator32.outputs.length = 5 ∧
  mkComparator32.instances.length = 1 := by native_decide

-- Comparator64 structural properties (KSA-based via Subtractor64 instance)
theorem comparator64_structure :
  mkComparator64.gates.length = 82 ∧
  mkComparator64.inputs.length = 129 ∧
  mkComparator64.outputs.length = 5 ∧
  mkComparator64.instances.length = 1 := by native_decide

-- EqualityComparator32 structural properties (XOR + OR-tree, no subtraction)
theorem equalityComparator32_structure :
  mkEqualityComparator32.gates.length = 65 ∧
  mkEqualityComparator32.inputs.length = 64 ∧
  mkEqualityComparator32.outputs.length = 1 ∧
  mkEqualityComparator32.instances.length = 0 := by native_decide

/-! ## L1 Functional Correctness Proofs -/

/-- Helper: Construct input WireMap for 4-bit Comparator. -/
def makeCmp4WireMap (a0 a1 a2 a3 b0 b1 b2 b3 : Bool) : WireMap :=
  [
    (Wire.mk "a_0", a0), (Wire.mk "a_1", a1), (Wire.mk "a_2", a2), (Wire.mk "a_3", a3),
    (Wire.mk "b_0", b0), (Wire.mk "b_1", b1), (Wire.mk "b_2", b2), (Wire.mk "b_3", b3),
    (Wire.mk "one", true)
  ]

/-- Helper: Decode 4 bits to unsigned Nat. -/
def cmpBits4ToNat (b0 b1 b2 b3 : Bool) : Nat :=
  (if b0 then 1 else 0) +
  (if b1 then 2 else 0) +
  (if b2 then 4 else 0) +
  (if b3 then 8 else 0)

/-- Helper: Decode 4 bits to two's-complement signed Int. -/
def cmpBits4ToInt (b0 b1 b2 b3 : Bool) : Int :=
  let u := cmpBits4ToNat b0 b1 b2 b3
  if u >= 8 then (u : Int) - 16 else (u : Int)

/-- Functional verification of all 5 comparator outputs for a single input pair. -/
def checkCmp4 (a0 a1 a2 a3 b0 b1 b2 b3 : Bool) : Bool :=
  let m := makeCmp4WireMap a0 a1 a2 a3 b0 b1 b2 b3
  let res := compileCircuit mkComparator4 m
  let eq := res.lookup (Wire.mk "eq")
  let ltu := res.lookup (Wire.mk "ltu")
  let gtu := res.lookup (Wire.mk "gtu")
  let lt := res.lookup (Wire.mk "lt")
  let gt := res.lookup (Wire.mk "gt")
  let uA := cmpBits4ToNat a0 a1 a2 a3
  let uB := cmpBits4ToNat b0 b1 b2 b3
  let sA := cmpBits4ToInt a0 a1 a2 a3
  let sB := cmpBits4ToInt b0 b1 b2 b3
  (eq == (uA == uB)) &&
  (ltu == (uA < uB)) &&
  (gtu == (uA > uB)) &&
  (lt == (sA < sB)) &&
  (gt == (sA > sB))

/-- Exhaustive check across all 256 input combinations. -/
def checkCmp4All : Bool :=
  let bools := [false, true]
  bools.all fun a0 =>
  bools.all fun a1 =>
  bools.all fun a2 =>
  bools.all fun a3 =>
  bools.all fun b0 =>
  bools.all fun b1 =>
  bools.all fun b2 =>
  bools.all fun b3 =>
    checkCmp4 a0 a1 a2 a3 b0 b1 b2 b3

/-- Theorem: 4-bit Comparator correctly evaluates eq, ltu, gtu, lt, gt across all 256 inputs (L1 Functional Truth). -/
theorem comparator4_functional_correct : checkCmp4All = true := by
  native_decide

end Shoumei.Circuits.Combinational
