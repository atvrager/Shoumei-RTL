/-
Components/Spec.lean - Component selection requirements

A `DesignTarget` carries the PDK, clock period and optimization aim for a
build.  `AdderSpec` specializes that requirement to one adder instance, so a
use site names *what it needs*, not *which structure* it wants.

Today the adder structure is hardcoded at every site (`moduleName :=
"KoggeStoneAdder32NoCin"`).  These types carry the requirement instead, and
`Shoumei.Components.Select` maps it to a concrete structure.
-/

import Shoumei.DSL

namespace Shoumei.Components

/-- Process design kit a circuit is targeted at. -/
inductive PDK where
  | asap7
  | gf180mcu
  deriving Repr, BEq, DecidableEq, Inhabited, Hashable

/-- Optimization aim: smallest area or shortest delay. -/
inductive Aim where
  | minArea
  | minDelay
  deriving Repr, BEq, DecidableEq, Inhabited, Hashable

/-- Build-level requirement shared by every selectable component. -/
structure DesignTarget where
  pdk      : PDK  := .asap7
  periodPs : Nat  := 1000  -- 1.0 GHz ASAP7 canonical target
  aim      : Aim  := .minArea
  deriving Repr, BEq, DecidableEq, Inhabited

/-- How the adder's carry-in is supplied. -/
inductive CinMode where
  | none   -- no cin port
  | input  -- cin is a port
  | one    -- cin tied to 1 internally
  deriving Repr, BEq, DecidableEq, Inhabited, Hashable

/-- Adder structures the selector may choose between. -/
inductive AdderImpl where
  | rippleCarry
  | carrySelect
  | brentKung
  | sklansky
  | hanCarlson
  | koggeStone
  deriving Repr, BEq, DecidableEq, Inhabited, Hashable

/-- All structures, in deterministic order. -/
def AdderImpl.all : List AdderImpl :=
  [.koggeStone, .hanCarlson, .sklansky, .brentKung, .carrySelect, .rippleCarry]

/-- Tie-break order: lower wins.  Kogge-Stone is the a-priori default at the
    timing-critical sites, so it holds precedence 0. -/
def AdderImpl.precedence : AdderImpl → Nat
  | .koggeStone  => 0
  | .hanCarlson  => 1
  | .sklansky    => 2
  | .brentKung   => 3
  | .carrySelect => 4
  | .rippleCarry => 5

/-- A concrete adder requirement: width, carry-in mode, and the design target
    it must meet.  `pinned` overrides the heuristic when a site's structure has
    been audited; it is `none` everywhere in the default build. -/
structure AdderSpec where
  width    : Nat
  cin      : CinMode  := .input
  aim      : Aim      := .minArea
  periodPs : Nat      := 1000
  pdk      : PDK      := .asap7
  pinned   : Option AdderImpl := none
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Site builds from the shared default target. -/
def defaultTarget : DesignTarget := {}

/-- A spec whose aim is shortest delay. -/
def AdderSpec.minDelay (width : Nat) (cin : CinMode) : AdderSpec :=
  { width, cin, aim := .minDelay, periodPs := defaultTarget.periodPs, pdk := defaultTarget.pdk }

/-- A spec whose aim is smallest area. -/
def AdderSpec.minArea (width : Nat) (cin : CinMode) : AdderSpec :=
  { width, cin, aim := .minArea, periodPs := defaultTarget.periodPs, pdk := defaultTarget.pdk }

end Shoumei.Components