/-
Reflection/BitVecPacking.lean - BitVec ↔ wire bindings conversion

Generalized infrastructure for packing/unpacking BitVec values to/from
wire bindings in a WireMap. Used by the ALU bridge and future circuit proofs.
-/

import Shoumei.Reflection.CompileCircuit

namespace Shoumei.Reflection

open Shoumei

/-- Create wire bindings from a BitVec (LSB = wire index 0).
    Produces a `WireMap` with entries `(name_0, bit0), (name_1, bit1), ...`. -/
def bitVecToBindings (name : String) (n : Nat) (bv : BitVec n) : WireMap :=
  (List.range n).map fun i => (Wire.mk s!"{name}_{i}", bv.getLsbD i)

/-- Create wire bindings from a BitVec using `WireMap.insert` (for proofs). -/
def bitVecToWireMap (name : String) (n : Nat) (bv : BitVec n) : WireMap :=
  (List.range n).reverse.foldl
    (fun m i => m.insert (Wire.mk s!"{name}_{i}") (bv.getLsbD i))
    []

/-- Read N indexed wires from a WireMap as a Nat (MSB-first recursion). -/
def readWiresAsNatMap (m : WireMap) (name : String) : Nat → Nat
  | 0 => 0
  | n + 1 =>
    let bit := if m.lookup (Wire.mk s!"{name}_{n}") then 1 else 0
    bit * (2 ^ n) + readWiresAsNatMap m name n

/-- Read N indexed wires as a BitVec. -/
def readResultBitVecMap (m : WireMap) (name : String) (width : Nat) : BitVec width :=
  BitVec.ofNat width (readWiresAsNatMap m name width)

end Shoumei.Reflection
