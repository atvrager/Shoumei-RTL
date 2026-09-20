/-
Components/AdderLibraryProofs.lean - Selection acceptance proofs

The hard constraint of the component-selection change: at the default target
the selector must reproduce the a-priori choices -- Kogge-Stone on every
timing-critical site, emitting the same module name as before.
-/

import Shoumei.Components.Select

namespace Shoumei.Components

open Shoumei

/-- Each site's (width, carry mode, module name chosen a priori). -/
def siteChoices : List (Nat × CinMode × String) :=
  [(32, .none,  "KoggeStoneAdder32NoCin"),
   (32, .input, "KoggeStoneAdder32"),
   (32, .one,   "KoggeStoneAdder32WithCin1"),
   (64, .none,  "KoggeStoneAdder64NoCin"),
   (64, .input, "KoggeStoneAdder64"),
   (64, .one,   "KoggeStoneAdder64WithCin1"),
   (106, .none, "KoggeStoneAdder106NoCin"),
   (106, .input, "KoggeStoneAdder106")]

/-- **Acceptance.**  `minDelay` at every site in use selects Kogge-Stone and
    emits exactly the module name the site used to hardcode. -/
theorem default_target_picks_koggeStone :
    siteChoices.all (fun t =>
      selectAdder (AdderSpec.minDelay t.1 t.2.1) == AdderImpl.koggeStone &&
      adderModule (AdderSpec.minDelay t.1 t.2.1) == t.2.2) = true := by
  native_decide

/-- Every spec the build uses resolves to a legal structure. -/
theorem selectAdder_total :
    adderSpecsInUse.all (fun s => legal (selectAdder s) s) = true := by
  native_decide

/-- A `minArea` spec at the GF180 period does not fall back to ripple-carry:
    the timing filter is live. -/
theorem gf180_minArea_is_prefix :
    selectAdder { AdderSpec.minArea 64 .none with pdk := .gf180mcu, periodPs := 15625 }
      ≠ AdderImpl.rippleCarry := by
  native_decide

end Shoumei.Components