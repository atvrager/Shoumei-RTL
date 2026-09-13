/-
FPDoubleMiscProofs.lean - Structural proofs for FPDoubleMisc
-/

import Shoumei.Circuits.Combinational.FPDoubleMisc

namespace Shoumei.Circuits.Combinational

theorem fpDoubleMisc_inputs : fpDoubleMiscCircuit.inputs.length = 139 := by native_decide

theorem fpDoubleMisc_outputs : fpDoubleMiscCircuit.outputs.length = 70 := by native_decide

theorem fpDoubleMisc_name : fpDoubleMiscCircuit.name = "FPDoubleMisc" := by rfl

end Shoumei.Circuits.Combinational
