/-
Circuits/Combinational/CarrySelectAdderProofs.lean - Carry-select adder proofs

Structural claims (ports, mux count) plus the exhaustive arithmetic check,
which lives in `PrefixAdderProofs` (`checkCarrySelect`) because it shares the
evaluation harness with the prefix trees.
-/

import Shoumei.Circuits.Combinational.CarrySelectAdder
import Shoumei.Circuits.Combinational.PrefixAdderProofs

namespace Shoumei.Circuits.Combinational

open Shoumei
open Shoumei.Components

/-- Width 8 is a single block: no select muxes, no internal carry-out output. -/
theorem carrySelect8_structure :
    (mkCarrySelectAdderCircuit 8 .none).inputs.length = 16 ∧
    (mkCarrySelectAdderCircuit 8 .none).outputs.length = 8 ∧
    (mkCarrySelectAdderCircuit 8 .none).gates.any (fun g => g.gateType == GateType.MUX) = false := by
  native_decide

/-- Width 16 has one upper block: eight sum muxes plus one carry mux, and the
    `.input` variant exposes the `cin` port. -/
theorem carrySelect16_structure :
    (mkCarrySelectAdderCircuit 16 .input).inputs.length = 33 ∧
    (mkCarrySelectAdderCircuit 16 .input).outputs.length = 16 ∧
    (mkCarrySelectAdderCircuit 16 .input).gates.countP (fun g => g.gateType == GateType.MUX) = 9 := by
  native_decide

/-- The width-8 circuit computes `a + b + cin` for every input. -/
theorem carrySelect8_correct :
    checkCarrySelect 8 .none && checkCarrySelect 8 .input && checkCarrySelect 8 .one = true := by
  native_decide

end Shoumei.Circuits.Combinational