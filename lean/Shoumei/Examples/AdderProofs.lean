/-
AdderProofs.lean - Formal Proofs for Full Adder Circuit

Proves correctness properties of the full adder:
1. Truth table correctness - all 8 input combinations produce correct outputs
2. Commutativity - swapping a and b doesn't change the result
3. Arithmetic correctness - outputs represent binary addition
-/

import Shoumei.Examples.Adder
import Shoumei.Semantics

namespace Shoumei.Examples

open Shoumei

-- Helper: Create environment from specific input values
def makeAdderEnv (a_val b_val cin_val : Bool) : Env :=
  mkEnv [
    (Wire.mk "a", a_val),
    (Wire.mk "b", b_val),
    (Wire.mk "cin", cin_val)
  ]

-- Helper: Extract sum output from evaluation
def getSumOutput (env : Env) : Bool :=
  env (Wire.mk "sum")

-- Helper: Extract cout output from evaluation
def getCoutOutput (env : Env) : Bool :=
  env (Wire.mk "cout")

-- Theorem: FullAdder produces correct outputs for all 8 input combinations
-- This exhaustively proves the truth table

theorem fullAdder_case_000 :
  let env := makeAdderEnv false false false
  let result := evalCircuit fullAdderCircuit env
  getSumOutput result = false ∧ getCoutOutput result = false := by
  native_decide

theorem fullAdder_case_001 :
  let env := makeAdderEnv false false true
  let result := evalCircuit fullAdderCircuit env
  getSumOutput result = true ∧ getCoutOutput result = false := by
  native_decide

theorem fullAdder_case_010 :
  let env := makeAdderEnv false true false
  let result := evalCircuit fullAdderCircuit env
  getSumOutput result = true ∧ getCoutOutput result = false := by
  native_decide

theorem fullAdder_case_011 :
  let env := makeAdderEnv false true true
  let result := evalCircuit fullAdderCircuit env
  getSumOutput result = false ∧ getCoutOutput result = true := by
  native_decide

theorem fullAdder_case_100 :
  let env := makeAdderEnv true false false
  let result := evalCircuit fullAdderCircuit env
  getSumOutput result = true ∧ getCoutOutput result = false := by
  native_decide

theorem fullAdder_case_101 :
  let env := makeAdderEnv true false true
  let result := evalCircuit fullAdderCircuit env
  getSumOutput result = false ∧ getCoutOutput result = true := by
  native_decide

theorem fullAdder_case_110 :
  let env := makeAdderEnv true true false
  let result := evalCircuit fullAdderCircuit env
  getSumOutput result = false ∧ getCoutOutput result = true := by
  native_decide

theorem fullAdder_case_111 :
  let env := makeAdderEnv true true true
  let result := evalCircuit fullAdderCircuit env
  getSumOutput result = true ∧ getCoutOutput result = true := by
  native_decide

-- Theorem: FullAdder is commutative in a and b
-- Swapping a and b doesn't change sum or cout
theorem fullAdder_commutative (a_val b_val cin_val : Bool) :
  let env1 := makeAdderEnv a_val b_val cin_val
  let env2 := makeAdderEnv b_val a_val cin_val
  let result1 := evalCircuit fullAdderCircuit env1
  let result2 := evalCircuit fullAdderCircuit env2
  getSumOutput result1 = getSumOutput result2 ∧
  getCoutOutput result1 = getCoutOutput result2 := by
  -- Proof by case analysis on all possible values
  cases a_val <;> cases b_val <;> cases cin_val <;> native_decide

-- Helper: Convert Bool to Nat for arithmetic
def boolToNat (b : Bool) : Nat :=
  if b then 1 else 0

-- Theorem: FullAdder correctly represents binary addition
-- sum = (a + b + cin) mod 2
-- cout = (a + b + cin) / 2
theorem fullAdder_arithmetic (a_val b_val cin_val : Bool) :
  let env := makeAdderEnv a_val b_val cin_val
  let result := evalCircuit fullAdderCircuit env
  let sum_nat := boolToNat (getSumOutput result)
  let cout_nat := boolToNat (getCoutOutput result)
  let total := boolToNat a_val + boolToNat b_val + boolToNat cin_val
  sum_nat = total % 2 ∧ cout_nat = total / 2 := by
  -- Proof by case analysis
  cases a_val <;> cases b_val <;> cases cin_val <;> native_decide

-- Main correctness theorem: combines all the above
-- The FullAdder is a correct implementation of 1-bit binary addition
theorem fullAdder_correct :
  ∀ (a b cin : Bool),
    let env := makeAdderEnv a b cin
    let result := evalCircuit fullAdderCircuit env
    let sum := getSumOutput result
    let cout := getCoutOutput result
    -- Truth table matches
    (a = false ∧ b = false ∧ cin = false → sum = false ∧ cout = false) ∧
    (a = false ∧ b = false ∧ cin = true → sum = true ∧ cout = false) ∧
    (a = false ∧ b = true ∧ cin = false → sum = true ∧ cout = false) ∧
    (a = false ∧ b = true ∧ cin = true → sum = false ∧ cout = true) ∧
    (a = true ∧ b = false ∧ cin = false → sum = true ∧ cout = false) ∧
    (a = true ∧ b = false ∧ cin = true → sum = false ∧ cout = true) ∧
    (a = true ∧ b = true ∧ cin = false → sum = false ∧ cout = true) ∧
    (a = true ∧ b = true ∧ cin = true → sum = true ∧ cout = true) := by
  intro a b cin
  cases a <;> cases b <;> cases cin <;> native_decide

end Shoumei.Examples
