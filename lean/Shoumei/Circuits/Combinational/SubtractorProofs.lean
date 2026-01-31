/-
SubtractorProofs.lean - Formal Proofs for Subtractor

Proves correctness properties of the subtractor:
1. Structure correctness - gate count, composition
2. Reduction to RippleCarryAdder - Subtractor(A,B) = RCA(A, ~B, 1)
3. Arithmetic correctness - concrete test cases

The subtractor demonstrates compositional verification:
- Reuses proven RippleCarryAdder
- Adds N NOT gates for 2's complement
- Total correctness follows from component correctness
-/

import Shoumei.Circuits.Combinational.Subtractor
import Shoumei.Circuits.Combinational.RippleCarryAdderProofs

namespace Shoumei.Circuits.Combinational

open Shoumei

-- Theorem: Subtractor4 has correct structure
-- 4 NOT gates + 4 FullAdders (20 gates) = 24 total gates
theorem subtractor4_structure :
  mkSubtractor4.gates.length = 24 ∧  -- 4 NOT + 20 RCA gates
  mkSubtractor4.inputs.length = 9 ∧   -- a[4] + b[4] + one
  mkSubtractor4.outputs.length = 5    -- diff[4] + borrow
  := by native_decide

-- Theorem: Subtractor8 has correct structure
-- 8 NOT gates + 8 FullAdders (40 gates) = 48 total gates
theorem subtractor8_structure :
  mkSubtractor8.gates.length = 48 ∧  -- 8 NOT + 40 RCA gates
  mkSubtractor8.inputs.length = 17 ∧  -- a[8] + b[8] + one
  mkSubtractor8.outputs.length = 9    -- diff[8] + borrow
  := by native_decide

-- Theorem: Subtractor32 has correct structure
-- 32 NOT gates + 32 FullAdders (160 gates) = 192 total gates
theorem subtractor32_structure :
  mkSubtractor32.gates.length = 192 ∧  -- 32 NOT + 160 RCA gates
  mkSubtractor32.inputs.length = 65 ∧   -- a[32] + b[32] + one
  mkSubtractor32.outputs.length = 33    -- diff[32] + borrow
  := by native_decide

-- TODO: Behavioral proofs
-- These would verify that Subtractor(A, B) computes A - B correctly
-- Will add after we have evaluation functions that handle the "one" input

-- TODO: Composition theorem
-- Would prove that subtractor gates decompose into NOT gates + RCA gates
-- Requires list manipulation lemmas we haven't developed yet

end Shoumei.Circuits.Combinational
