/-
Components/AdderLibrary.lean - Concrete circuits behind each adder structure

`adderCircuit impl spec` returns the circuit for one concrete (structure,
width, carry-in) triple.  Kogge-Stone delegates to the long-standing
`KoggeStoneAdder*.lean` definitions so today's emitted SV is byte-identical;
the other structures are built by the generic prefix/carry-select builders.
-/

import Shoumei.Circuits.Combinational.KoggeStoneAdder
import Shoumei.Circuits.Combinational.PrefixAdder
import Shoumei.Circuits.Combinational.CarrySelectAdder
import Shoumei.Components.Spec

namespace Shoumei.Components

open Shoumei
open Shoumei.Circuits.Combinational

/-- The prefix network a structure uses. -/
def AdderImpl.tree : AdderImpl → PrefixTree
  | .rippleCarry => .rippleCarry
  | .brentKung   => .brentKung
  | .sklansky    => .sklansky
  | .hanCarlson  => .hanCarlson
  | .koggeStone  => .koggeStone
  | .carrySelect => .koggeStone  -- unused; carry-select has its own builder

/-- Kogge-Stone circuit: the audited widths reuse the existing definitions
    verbatim, everything else goes through the generic prefix builder. -/
def koggeStoneCircuit (width : Nat) (cin : CinMode) : Circuit :=
  match width, cin with
  | 32, .none  => mkKoggeStoneAdder32NoCin
  | 32, .input => mkKoggeStoneAdder32
  | 64, .none  => mkKoggeStoneAdder64NoCin
  | 64, .input => mkKoggeStoneAdder64
  | 64, .one   => mkKoggeStoneAdder64WithCin1
  | 106, .none => koggeStoneAdder106NoCin
  | 106, .input => koggeStoneAdder106
  | _, _       => mkPrefixAdderCircuit .koggeStone width cin

/-- Circuit emitted for one structure at a given spec. -/
def adderCircuit (impl : AdderImpl) (spec : AdderSpec) : Circuit :=
  match impl with
  | .koggeStone  => koggeStoneCircuit spec.width spec.cin
  | .carrySelect => mkCarrySelectAdderCircuit spec.width spec.cin
  | .rippleCarry => mkPrefixAdderCircuit .rippleCarry spec.width spec.cin
  | .brentKung   => mkPrefixAdderCircuit .brentKung spec.width spec.cin
  | .sklansky    => mkPrefixAdderCircuit .sklansky spec.width spec.cin
  | .hanCarlson  => mkPrefixAdderCircuit .hanCarlson spec.width spec.cin

/-- Module name emitted for one structure at a given spec. -/
def adderImplName (impl : AdderImpl) (spec : AdderSpec) : String :=
  match impl with
  | .carrySelect => carrySelectName spec.width spec.cin
  | _            => prefixAdderName impl.tree spec.width spec.cin

end Shoumei.Components