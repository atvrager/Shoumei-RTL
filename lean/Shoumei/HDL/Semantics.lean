/-
HDL/Semantics.lean - Operational Semantics for High-Level RTL Signals

Defines the mathematical semantics of `Signal w` over an environment:
- Maps `Signal w` to `BitVec w`
- Provides evaluation for all combinational expressions and registers
- Establishes the formal semantic bridge for refinement proofs
-/

import Shoumei.DSL
import Shoumei.Semantics
import Shoumei.HDL.Types
import Shoumei.HDL.Expr

namespace Shoumei.HDL

open Shoumei

/-- Convert a list of boolean values (little-endian: LSB at head) to a BitVec. -/
def bitVecOfBools (w : Nat) (bits : List Bool) : BitVec w :=
  let rec loop (bs : List Bool) (idx : Nat) (acc : BitVec w) : BitVec w :=
    match bs with
    | [] => acc
    | b :: rest =>
        let bitVal : BitVec w := if b then (1 : BitVec w) <<< idx else 0
        loop rest (idx + 1) (acc ||| bitVal)
  loop bits 0 0

/-- Evaluate a high-level signal to a BitVec in a given wire environment. -/
def evalSignal (env : Env) : {w : Nat} → Signal w → BitVec w
  | _, .const val => val
  | w, .input name _ =>
      let bits := (List.range w).map fun i =>
        env (if w == 1 then Wire.mk name else Wire.mk s!"{name}_{i}")
      bitVecOfBools w bits
  | w, .wire name _ =>
      let bits := (List.range w).map fun i =>
        env (if w == 1 then Wire.mk name else Wire.mk s!"{name}_{i}")
      bitVecOfBools w bits
  | w, .reg name _ _ _ _ _ =>
      let bits := (List.range w).map fun i =>
        env (if w == 1 then Wire.mk name else Wire.mk s!"{name}_{i}")
      bitVecOfBools w bits
  | _, .extract src hi lo =>
      let val := evalSignal env src
      val.extractLsb' lo (hi - lo + 1)
  | _, .concat a b =>
      let valA := evalSignal env a
      let valB := evalSignal env b
      valA ++ valB
  | _, .not a =>
      ~~~(evalSignal env a)
  | _, .and a b =>
      evalSignal env a &&& evalSignal env b
  | _, .or a b =>
      evalSignal env a ||| evalSignal env b
  | _, .xor a b =>
      evalSignal env a ^^^ evalSignal env b
  | _, .add a b =>
      evalSignal env a + evalSignal env b
  | _, .sub a b =>
      evalSignal env a - evalSignal env b
  | _, .mul a b =>
      let valA := BitVec.zeroExtend _ (evalSignal env a)
      let valB := BitVec.zeroExtend _ (evalSignal env b)
      valA * valB
  | _, .mux sel thenSig elseSig =>
      let selVal := (evalSignal env sel).getLsbD 0
      if selVal then evalSignal env thenSig else evalSignal env elseSig
  | _, .eq a b =>
      if evalSignal env a == evalSignal env b then
        BitVec.ofNat 1 1
      else
        BitVec.ofNat 1 0
  | _, .ult a b =>
      if evalSignal env a < evalSignal env b then
        BitVec.ofNat 1 1
      else
        BitVec.ofNat 1 0
  | w, .instOut instName portName _ =>
      let bits := (List.range w).map fun i =>
        env (if w == 1 then Wire.mk s!"{instName}_{portName}"
             else Wire.mk s!"{instName}_{portName}_{i}")
      bitVecOfBools w bits
  | _, .dshr s amt =>
      let sVal := evalSignal env s
      let amtVal := evalSignal env amt
      sVal >>> amtVal.toNat
  | _, .dshl s amt =>
      let sVal := evalSignal env s
      let amtVal := evalSignal env amt
      sVal <<< amtVal.toNat

end Shoumei.HDL
