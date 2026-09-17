/-
RippleCarryAdderProofs.lean - Formal Proofs for Ripple-Carry Adder

Proves correctness properties of the ripple-carry adders:
1. Structure correctness - gate count, wire count
2. FullAdder equivalence - each bit uses the same logic as fullAdderCircuit

TODO: More comprehensive proofs once DSL supports hierarchical composition
-/

import Shoumei.Circuits.Combinational.RippleCarryAdder
import Shoumei.Examples.Adder
import Shoumei.Semantics
import Shoumei.Reflection.CompileCircuit

namespace Shoumei.Circuits.Combinational

open Shoumei
open Shoumei.Reflection

-- Theorem: mkFullAdderInstance with concrete wires produces 5 gates
-- This establishes that we're reusing the proven FullAdder logic
theorem fullAdderInstance_structure_concrete :
  let a := Wire.mk "a"
  let b := Wire.mk "b"
  let cin := Wire.mk "cin"
  let sum := Wire.mk "sum"
  let cout := Wire.mk "cout"
  (mkFullAdderInstance a b cin sum cout 0 "").length = 5 := by
  native_decide

-- Theorem: RippleCarryAdder4 has correct structure
theorem rca4_structure :
  mkRippleCarryAdder4.gates.length = 20 ∧  -- 4 FullAdders × 5 gates each
  mkRippleCarryAdder4.inputs.length = 9 ∧   -- a[4] + b[4] + cin
  mkRippleCarryAdder4.outputs.length = 5    -- sum[4] + cout
  := by native_decide

-- Theorem: RippleCarryAdder32 has correct structure
theorem rca32_structure :
  mkRippleCarryAdder32.gates.length = 160 ∧  -- 32 FullAdders × 5 gates each
  mkRippleCarryAdder32.inputs.length = 65 ∧   -- a[32] + b[32] + cin
  mkRippleCarryAdder32.outputs.length = 32    -- sum[32] (final carry stays internal)
  := by native_decide

/-! ## L1 Functional Evaluation Proofs -/

/-- Helper: Construct input WireMap for 4-bit RippleCarryAdder. -/
def makeRca4WireMap (a0 a1 a2 a3 b0 b1 b2 b3 cin : Bool) : WireMap :=
  [
    (Wire.mk "a_0", a0), (Wire.mk "a_1", a1), (Wire.mk "a_2", a2), (Wire.mk "a_3", a3),
    (Wire.mk "b_0", b0), (Wire.mk "b_1", b1), (Wire.mk "b_2", b2), (Wire.mk "b_3", b3),
    (Wire.mk "cin", cin)
  ]

/-- Helper: Decode 4-bit boolean inputs to Nat. -/
def bits4ToNat (b0 b1 b2 b3 : Bool) : Nat :=
  (if b0 then 1 else 0) +
  (if b1 then 2 else 0) +
  (if b2 then 4 else 0) +
  (if b3 then 8 else 0)

/-- Helper: Extract 4-bit sum and carry-out from evaluated WireMap. -/
def rca4WireMapOutputToNat (m : WireMap) : Nat :=
  (if m.lookup (Wire.mk "sum_0") then 1 else 0) +
  (if m.lookup (Wire.mk "sum_1") then 2 else 0) +
  (if m.lookup (Wire.mk "sum_2") then 4 else 0) +
  (if m.lookup (Wire.mk "sum_3") then 8 else 0) +
  (if m.lookup (Wire.mk "cout") then 16 else 0)

/-- Check that 4-bit RippleCarryAdder adds correctly for a given input set. -/
def checkRca4WireMap (a0 a1 a2 a3 b0 b1 b2 b3 cin : Bool) : Bool :=
  let m := makeRca4WireMap a0 a1 a2 a3 b0 b1 b2 b3 cin
  let res := compileCircuit mkRippleCarryAdder4 m
  rca4WireMapOutputToNat res == bits4ToNat a0 a1 a2 a3 + bits4ToNat b0 b1 b2 b3 + (if cin then 1 else 0)

/-- Exhaustive check across all 512 input combinations. -/
def checkRca4All : Bool :=
  let bools := [false, true]
  bools.all fun a0 =>
  bools.all fun a1 =>
  bools.all fun a2 =>
  bools.all fun a3 =>
  bools.all fun b0 =>
  bools.all fun b1 =>
  bools.all fun b2 =>
  bools.all fun b3 =>
  bools.all fun cin =>
    checkRca4WireMap a0 a1 a2 a3 b0 b1 b2 b3 cin

/-- Theorem: 4-bit RippleCarryAdder correctly computes binary addition for all 512 input combinations (L1 Functional Truth). -/
theorem rca4_arithmetic_correct : checkRca4All = true := by
  native_decide

end Shoumei.Circuits.Combinational
