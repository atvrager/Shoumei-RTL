/-
Circuits/Combinational/PrefixAdder.lean - Parallel-prefix adder family

One builder for the whole parallel-prefix family.  A `PrefixTree` names a
network; `prefixLevels` lists its merge cells level by level; `mkPrefixAdd`
turns that network into gates.  Kogge-Stone has its own long-standing
builders (`KoggeStoneAdder.lean`) which stay verbatim so today's emitted SV
does not change -- this file exists so the other four trees can be built and
so one correctness proof covers them all.

Prefix-cell semantics, cell (hi, lo) with hi > lo:
    g_hi <- g_hi                             -- high bit generate
    p_hi <- p_hi AND p_lo                    -- propagate
    g_hi <- g_hi OR (p_hi AND g_lo)          -- generate merge
-/

import Shoumei.DSL
import Shoumei.Circuits.Combinational.RippleCarryAdder
import Shoumei.Components.Spec

namespace Shoumei.Circuits.Combinational

open Shoumei
open Shoumei.Components

/-- Parallel-prefix network families. -/
inductive PrefixTree where
  | rippleCarry
  | brentKung
  | sklansky
  | hanCarlson
  | koggeStone
  deriving Repr, BEq, DecidableEq, Inhabited, Hashable

/-- Powers of two strictly below `bound`: 1,2,4,... -/
private def pow2Less (bound : Nat) : List Nat :=
  (List.range 32).filterMap fun k =>
    let s : Nat := 1 <<< k
    if s < bound then some s else none

/-- Powers of two at most `bound`: 1,2,4,... -/
private def pow2Upto (bound : Nat) : List Nat :=
  (List.range 32).filterMap fun k =>
    let s : Nat := 1 <<< k
    if s ≤ bound then some s else none

/-- Smallest `k` with `2^k ≥ n` (0 for `n ≤ 1`). -/
private def ceilLog2 (n : Nat) : Nat :=
  ((List.range 32).find? (fun k => (1 : Nat) <<< k ≥ n)).getD 32

/-- Merge cells per level for a network family.

    A cell is `(hi, lo)`; the levels are applied in order.  Cells within one
    level are independent (each reads the previous level's spans). -/
def prefixLevels (tree : PrefixTree) (width : Nat) : List (List (Nat × Nat)) :=
  match tree with
  | .rippleCarry =>
      -- One cell per level: bit i merges the running prefix from bit i-1.
      (List.range (width - 1)).map fun i => [(i + 1, i)]
  | .koggeStone =>
      (pow2Less width).map fun s =>
        (List.range (width - s)).map fun k => (k + s, k)
  | .sklansky =>
      (pow2Less width).map fun s =>
        (List.range width).filterMap fun i =>
          if i ≥ s && i % (2 * s) ≥ s then
            some (i, (i / (2 * s)) * (2 * s) + s - 1)
          else none
  | .brentKung =>
      let up := (pow2Upto (width / 2)).map fun d =>
        (List.range width).filterMap fun i =>
          if i ≥ d && (i + 1) % (2 * d) = 0 then some (i, i - d) else none
      -- Down-sweep: bit i merges the block `[i-d, i-1]` whose top is `3d-1`.
      let down := (pow2Upto (width / 4)).reverse.map fun d =>
        (List.range width).filterMap fun i =>
          if i ≥ 3 * d - 1 && (i - (3 * d - 1)) % (2 * d) = 0 then some (i, i - d) else none
      up ++ down
  | .hanCarlson =>
      -- Brent-Kung first level on odd bits; Kogge-Stone strides of 2^(s-1)
      -- on odd bits; a final Brent-Kung level fills the even bits.
      let bkFirst := (List.range width).filterMap fun i =>
        if i ≥ 1 && i % 2 = 1 then some (i, i - 1) else none
      let ksStages := (List.range 30).filterMap fun s =>
        if s ≥ 2 && s ≤ ceilLog2 width then
          let off : Nat := 1 <<< (s - 1)
          some ((List.range width).filterMap fun i =>
            if i ≥ off + 1 && i % 2 = 1 then some (i, i - off) else none)
        else none
      let bkLast := (List.range width).filterMap fun i =>
        if i ≥ 2 && i % 2 = 0 then some (i, i - 1) else none
      bkFirst :: (ksStages ++ [bkLast])

/-- Initial spans: bit i owns prefix `[i, i]`, stored as `(start, end)`. -/
def initSpans : Nat → Nat × Nat := fun i => (i, i)

/-- Cell `(hi, lo)` is legal iff it joins two adjacent spans:
    bit hi's prefix starts exactly one above bit lo's end. -/
def cellLegal (spans : Nat → Nat × Nat) (hi lo : Nat) : Bool :=
  lo < hi && (spans hi).1 = (spans lo).2 + 1

/-- Apply one level's cells atomically: each cell reads the previous level's
    spans and writes bit hi's new start.  `none` if any cell is illegal. -/
def applyLevel (spans : Nat → Nat × Nat) (cells : List (Nat × Nat))
    : Option (Nat → Nat × Nat) :=
  if cells.any (fun c => !cellLegal spans c.1 c.2) then none
  else
    some (fun j =>
      match cells.find? (fun c => c.1 == j) with
      | some c => ((spans c.2).1, j)
      | none => spans j)

/-- Fold the span map through every level, starting from `s0`. -/
def spanFoldFrom (s0 : Nat → Nat × Nat) (levels : List (List (Nat × Nat))) : Option (Nat → Nat × Nat) :=
  levels.foldl (fun acc lvl => acc.bind (fun s => applyLevel s lvl)) (some s0)

/-- Fold the span map through every level from the initial singleton spans. -/
def spanFold (levels : List (List (Nat × Nat))) : Option (Nat → Nat × Nat) :=
  spanFoldFrom initSpans levels

/-- A network is valid iff, after all levels, every bit owns the full prefix
    `[0, i]`.  Computable, so the selector can filter on it directly. -/
def validPrefixNetwork (levels : List (List (Nat × Nat))) (width : Nat) : Bool :=
  match spanFold levels with
  | some s => (List.range width).all (fun i => decide (s i = (0, i)))
  | none => false

/-- One prefix level: for each merge cell `(hi, lo)` emit the standard three
    gates; for every other bit emit pass-through buffers.  Returns the level's
    gates and the fresh g/p wire lists. -/
def mkPrefixLevel (pfx : String) (li n : Nat) (lvl : List (Nat × Nat))
    (gPrev pPrev : List Wire) : List Gate × List Wire × List Wire :=
  let lt := pfx ++ "_l" ++ toString li
  let gNew := makeIndexedWires (lt ++ "_g") n
  let pNew := makeIndexedWires (lt ++ "_p") n
  let hiSet := lvl.map (·.1)
  let cellGates := lvl.flatMap fun (hi, lo) =>
    let pg := Wire.mk (lt ++ "_pg_" ++ toString hi)
    [ Gate.mkAND (pPrev[hi]!) (gPrev[lo]!) pg,
      Gate.mkOR (gPrev[hi]!) pg (gNew[hi]!),
      Gate.mkAND (pPrev[hi]!) (pPrev[lo]!) (pNew[hi]!) ]
  let passGates := (List.range n).filterMap fun i =>
    if hiSet.contains i then none
    else some [Gate.mkBUF (gPrev[i]!) (gNew[i]!), Gate.mkBUF (pPrev[i]!) (pNew[i]!)]
  (cellGates ++ passGates.flatten, gNew, pNew)

/-- Build a prefix adder's gate list.  `cin = none` absorbs a zero carry-in,
    `some w` merges carry-in wire `w` into bit 0.  Returns `(gates, carry_out)`. -/
def mkPrefixAdd (tree : PrefixTree) (a b : List Wire) (cin : Option Wire)
    (sum : List Wire) (pfx : String) : List Gate × Wire :=
  let n := a.length
  let coutWire := Wire.mk (pfx ++ "_cout")
  if n == 0 then ([], coutWire)
  else
  let g0 := makeIndexedWires (pfx ++ "_g0") n
  let p0 := makeIndexedWires (pfx ++ "_p0") n
  let initGates := List.flatten <| (List.range n).map fun i =>
    [ Gate.mkAND (a[i]!) (b[i]!) (g0[i]!),
      Gate.mkXOR (a[i]!) (b[i]!) (p0[i]!) ]

  -- Carry-in merge into bit 0's generate: g0' = g0[0] OR (p0[0] AND cin)
  let (cinGates, gInit) :=
    match cin with
    | some c =>
        let p0c := Wire.mk (pfx ++ "_p0cin")
        let gm := Wire.mk (pfx ++ "_g0m")
        ([Gate.mkAND (p0[0]!) c p0c, Gate.mkOR (g0[0]!) p0c gm],
         [gm] ++ (List.range (n - 1)).map (fun i => g0[i + 1]!))
    | none => ([], (List.range n).map (fun i => g0[i]!))

  -- Apply each level: fresh g/p wires, merge cells plus pass-through buffers.
  let (prefixGates, finalG, _finalP) :=
    (List.enum (prefixLevels tree n)).foldl
      (fun (acc, gPrev, pPrev) (li, lvl) =>
        let (gs, gNew, pNew) := mkPrefixLevel pfx li n lvl gPrev pPrev
        (acc ++ gs, gNew, pNew))
      ([], gInit, p0)

  -- sum[0] = p0[0] XOR cin (or p0[0] when cin is absent);
  -- sum[i] = p0[i] XOR carry_{i-1}.
  let sum0 := match cin with
    | some c => Gate.mkXOR (p0[0]!) c (sum[0]!)
    | none   => Gate.mkBUF (p0[0]!) (sum[0]!)
  let sumRest := (List.range (n - 1)).map fun i =>
    Gate.mkXOR (p0[i + 1]!) (finalG[i]!) (sum[i + 1]!)

  let coutGate := Gate.mkBUF (finalG[n - 1]!) coutWire
  (initGates ++ cinGates ++ prefixGates ++ [sum0] ++ sumRest ++ [coutGate], coutWire)

/-- Family name used in module names. -/
def PrefixTree.label : PrefixTree → String
  | .rippleCarry => "RippleCarry"
  | .brentKung   => "BrentKung"
  | .sklansky    => "Sklansky"
  | .hanCarlson  => "HanCarlson"
  | .koggeStone  => "KoggeStone"

/-- Module name for a prefix adder of the given width and carry-in mode.
    `.input` carries no suffix, matching the repo's existing flat-name style. -/
def prefixAdderName (tree : PrefixTree) (width : Nat) (cin : CinMode) : String :=
  match cin with
  | .none  => s!"{tree.label}Adder{width}NoCin"
  | .input => s!"{tree.label}Adder{width}"
  | .one   => s!"{tree.label}Adder{width}WithCin1"

/-- Build a whole prefix-adder module. -/
def mkPrefixAdderCircuit (tree : PrefixTree) (width : Nat) (cin : CinMode) : Circuit :=
  let a := makeIndexedWires "a" width
  let b := makeIndexedWires "b" width
  let sum := makeIndexedWires "sum" width
  let cinWire : Option Wire :=
    match cin with
    | .none  => none
    | .input => some (Wire.mk "cin")
    | .one   => some (Wire.mk "one")
  let (gates, _cout) := mkPrefixAdd tree a b cinWire sum "pxa"
  let inputs := a ++ b ++ (match cin with | .input => [Wire.mk "cin"] | _ => [])
  let groups := [
    { name := "a", width := width, wires := a },
    { name := "b", width := width, wires := b },
    { name := "sum", width := width, wires := sum }
  ] ++ (match cin with
        | .input => [{ name := "cin", width := 1, wires := [Wire.mk "cin"] }]
        | _ => [])
  { name := prefixAdderName tree width cin
    inputs := inputs
    outputs := sum
    gates := gates
    instances := []
    signalGroups := groups
    keepHierarchy := true
  }

end Shoumei.Circuits.Combinational