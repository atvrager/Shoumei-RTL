/-
HDL/Examples/EqualityComparator.lean - Equality Comparator in High-Level HDL

Demonstrates an N-bit equality comparator in the high-level HDL frontend:
- Inputs: a (n bits), b (n bits)
- Output: eq (1 bit, 1 when a equals b)
- Lowers to bitwise XOR gates and a balanced OR-tree reduction
-/

import Shoumei.HDL.Types
import Shoumei.HDL.Expr
import Shoumei.HDL.Module
import Shoumei.HDL.Lower

namespace Shoumei.HDL.Examples

open Shoumei
open Shoumei.HDL

/-- Construct an N-bit equality comparator in the high-level HDL frontend. -/
def equalityComparatorHDL (n : Nat) : HDLModule :=
  let a : Signal n := .input "a" n
  let b : Signal n := .input "b" n
  let eq : Signal 1 := .eq a b
  let m : HDLModule := HDLModule.empty s!"EqualityComparator{n}"
  let m := m.addInput "a" n
  let m := m.addInput "b" n
  let m := m.addOutput "eq" 1 eq
  m

/-- Lowered Circuit representation of the N-bit equality comparator. -/
def equalityComparatorCircuit (n : Nat) : Circuit :=
  lowerModule (equalityComparatorHDL n)

/-- 20-bit equality comparator for cache tag checks. -/
def equalityComparator20Circuit : Circuit :=
  equalityComparatorCircuit 20

/-- 32-bit equality comparator. -/
def equalityComparator32Circuit : Circuit :=
  equalityComparatorCircuit 32

/-- 64-bit equality comparator. -/
def equalityComparator64Circuit : Circuit :=
  equalityComparatorCircuit 64

end Shoumei.HDL.Examples
