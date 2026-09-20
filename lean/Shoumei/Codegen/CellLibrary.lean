/-
Codegen/CellLibrary.lean - PDK standard-cell library model

A `StandardCell` is one library cell: its Boolean function, its SystemVerilog
name, its pin lists (in model order), its drive strength and its area.  The
function's meaning lives in `CellFunction.model`, defined once and shared by
every PDK, so a cell's behaviour is never inferred from its pin names.

Cell data is read from the PDK Liberty typical (TT) tables:
  ASAP7 7.5T RVT   third_party/orfs/flow/platforms/asap7/lib/NLDM/
  GF180MCU 9T 5V   third_party/orfs/flow/platforms/gf180/lib/
-/

import Shoumei.DSL
import Shoumei.Components.Spec

namespace Shoumei.Codegen

open Shoumei
open Shoumei.Components

/-- Boolean functions the mapper can realize as a single library cell. -/
inductive CellFunction where
  | inv | buf | and2 | or2 | xor2 | nand2 | nor2 | mux2
  | ao21 | ao22 | aoi21 | aoi22 | oai21 | fa | ha
  deriving Repr, BEq, DecidableEq, Inhabited, Hashable

/-- Output pin values, given input pin values aligned with `StandardCell.inputs`.
    Single-output cells return one value; `fa`/`ha` return `[sum, carry]`. -/
def CellFunction.model : CellFunction → List Bool → List Bool
  | .inv,   [a]          => [!a]
  | .buf,   [a]          => [a]
  | .and2,  [a, b]       => [a && b]
  | .or2,   [a, b]       => [a || b]
  | .xor2,  [a, b]       => [xor a b]
  | .nand2, [a, b]       => [!(a && b)]
  | .nor2,  [a, b]       => [!(a || b)]
  | .mux2,  [i0, i1, s]  => [if s then i1 else i0]
  | .ao21,  [a1, a2, b]  => [b || (a1 && a2)]
  | .ao22,  [a1, a2, b1, b2] => [(a1 && a2) || (b1 && b2)]
  | .aoi21, [a1, a2, b]  => [!(b || (a1 && a2))]
  | .aoi22, [a1, a2, b1, b2] => [!((a1 && a2) || (b1 && b2))]
  | .oai21, [a1, a2, b]  => [!((a1 || a2) && b)]
  | .fa,    [a, b, ci]   => [xor (xor a b) ci, (a && b) || (ci && xor a b)]
  | .ha,    [a, b]       => [xor a b, a && b]
  | _,      _            => []

/-- One standard cell. -/
structure StandardCell where
  function : CellFunction
  svName   : String
  outputs  : List String   -- output pins, aligned with `model`'s output order
  inputs   : List String   -- input pins, aligned with `model`'s input order
  drive    : Nat
  areaUm2  : Float
  deriving Repr, Inhabited

/-- A PDK's cell library. -/
structure CellLibrary where
  pdk       : PDK
  cells     : List StandardCell
  /-- Net-fanout ceiling to drive strength, descending. -/
  maxFanout : List (Nat × Nat)

namespace CellLibrary

/-- Pick a cell for a function at (at least) the requested drive: the smallest
    available drive not below it, else the largest available.  `none` only when
    the library has no cell for the function at all. -/
def find (lib : CellLibrary) (fn : CellFunction) (drive : Nat) : Option StandardCell :=
  let cands := lib.cells.filter (fun c => c.function == fn)
  match cands.find? (fun c => c.drive ≥ drive) with
  | some c => some c
  | none =>
      cands.foldl (fun best c => match best with
        | none => some c
        | some b => if c.drive > b.drive then some c else b) none

/-- Drive strength for a net of the given fanout, from `maxFanout`. -/
def driveFor (lib : CellLibrary) (fanout : Nat) : Nat :=
  match lib.maxFanout.find? (fun p => fanout ≤ p.1) with
  | some p => p.2
  | none => match lib.maxFanout.getLast? with
            | some p => p.2
            | none => 1

end CellLibrary

end Shoumei.Codegen