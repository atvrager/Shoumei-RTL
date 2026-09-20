/-
Components/Select.lean - Requirement-driven component selection

`selectAdder spec` turns a requirement into a structure: filter to legal
structures, drop those that miss the timing target (or, if none meet it, keep
the fastest), then pick the cheapest by the spec's aim, breaking ties by
`AdderImpl.precedence`.  At the default target the tie-break reproduces the
a-priori choice -- Kogge-Stone on every timing-critical site.
-/

import Shoumei.Components.Spec
import Shoumei.Components.Cost
import Shoumei.Components.AdderLibrary

namespace Shoumei.Components

open Shoumei
open Shoumei.Circuits.Combinational

/-- A structure is legal for a spec when its width is workable and its prefix
    network (if any) actually forms a valid full-prefix network at that width. -/
def legal (impl : AdderImpl) (spec : AdderSpec) : Bool :=
  if spec.width < 2 then false
  else
    match impl with
    | .carrySelect => spec.width ≥ 8
    | .rippleCarry => true
    | _ =>
        let t := impl.tree
        validPrefixNetwork (prefixLevels t spec.width) spec.width

/-- Analytic cost used for ranking: delay or area per the spec's aim. -/
def costOf (spec : AdderSpec) (impl : AdderImpl) : Float :=
  match spec.aim with
  | .minDelay => estDelay spec.pdk (adderCircuit impl spec)
  | .minArea  => estArea spec.pdk (adderCircuit impl spec)

/-- One candidate with both cost figures, so each circuit is built once. -/
structure AdderCost where
  impl  : AdderImpl
  area  : Float
  delay : Float
  deriving Repr, Inhabited

/-- Measure a candidate: area and delay of its circuit at this spec. -/
def AdderCost.measure (spec : AdderSpec) (impl : AdderImpl) : AdderCost :=
  let c := adderCircuit impl spec
  { impl, area := estArea spec.pdk c, delay := estDelay spec.pdk c }

/-- Prefer `a` over `b`: cheaper cost for the aim, ties broken by precedence. -/
def prefers (spec : AdderSpec) (a b : AdderCost) : Bool :=
  let ca := match spec.aim with | .minDelay => a.delay | .minArea => a.area
  let cb := match spec.aim with | .minDelay => b.delay | .minArea => b.area
  if ca < cb then true
  else if ca > cb then false
  else a.impl.precedence < b.impl.precedence

/-- Resolve a requirement to a concrete adder structure.

    Each candidate circuit is built and measured exactly once; the timing
    filter and the area/delay ranking then work off that table. -/
def selectAdder (spec : AdderSpec) : AdderImpl :=
  match spec.pinned with
  | some i => i
  | none =>
    let cands := AdderImpl.all.filter (legal · spec)
    -- The width is ≥ 2 for any real spec; fall back to ripple-carry so the
    -- candidate set is never empty.
    let cands := if cands.isEmpty then [.rippleCarry] else cands
    let measured := cands.map (AdderCost.measure spec)
    let meeting := measured.filter fun c => c.delay ≤ Float.ofNat spec.periodPs
    let pool := if meeting.isEmpty then measured else meeting
    (pool.foldl (fun best c => if prefers spec c best then c else best) pool.head!).impl

/-- Module name a spec's selected structure emits. -/
def adderModule (spec : AdderSpec) : String :=
  adderImplName (selectAdder spec) spec

/-- Circuit a spec's selected structure emits. -/
def selectedAdderCircuit (spec : AdderSpec) : Circuit :=
  adderCircuit (selectAdder spec) spec

/-- Every spec the build wires an adder for.  The codegen registry emits every
    legal structure at each of these, so re-selection never misses a module. -/
def adderSpecsInUse : List AdderSpec :=
  [ AdderSpec.minDelay 32 .none, AdderSpec.minDelay 32 .input, AdderSpec.minDelay 32 .one,
    AdderSpec.minDelay 64 .none, AdderSpec.minDelay 64 .input, AdderSpec.minDelay 64 .one,
    AdderSpec.minDelay 106 .none, AdderSpec.minDelay 106 .input ]

/-- Every adder circuit the registry must emit, deduplicated by module name. -/
def allAdderCircuits : List Circuit :=
  let all := adderSpecsInUse.flatMap fun s =>
    (AdderImpl.all.filter (legal · s)).map (adderCircuit · s)
  all.foldl (fun acc c =>
    if acc.any (fun x => x.name == c.name) then acc else acc ++ [c]) []

/-- Inline an adder of the selected structure into a gate list.  Kogge-Stone
    reuses the existing inline generator; the others go through the generic
    prefix builder.  Carry-select has no flat inline form, so it falls back to
    its prefix tree (Kogge-Stone), which is always correct. -/
def mkAddFor (spec : AdderSpec) (a b : List Wire) (cin : Wire)
    (sum : List Wire) (pfx : String) : List Gate × Wire :=
  match selectAdder spec with
  | .koggeStone => mkKoggeStoneAdd a b cin sum pfx
  | impl        => mkPrefixAdd impl.tree a b (some cin) sum pfx

/-- Inline a subtractor of the selected structure: `a - b` = `a + ~b + 1`.
    Inverts `b`, adds with carry-in `one`, and complements the carry for the
    borrow. -/
def mkSubFor (spec : AdderSpec) (a b : List Wire) (sum : List Wire) (pfx : String)
    (one : Wire) : List Gate × Wire :=
  let inv_b := (List.range b.length).map fun i => Wire.mk s!"{pfx}_invb_{i}"
  let invGates := (List.range b.length).map fun i => Gate.mkNOT (b[i]!) (inv_b[i]!)
  let (addGates, carry) := mkAddFor spec a inv_b one sum (pfx ++ "_add")
  let borrow := Wire.mk (pfx ++ "_borrow")
  (invGates ++ addGates ++ [Gate.mkNOT carry borrow], borrow)

end Shoumei.Components