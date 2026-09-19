/-
Interconnect/TileLink/TLXbarProofs.lean - Structural proofs for TLXbar8
-/

import Shoumei.Interconnect.TileLink.TLXbar

namespace Shoumei.Interconnect.TileLink

open Shoumei

theorem tlXbar8_name : tlXbar8Circuit.name = "TLXbar8" := by rfl

theorem tlXbar8_leaf : tlXbar8Circuit.instances.isEmpty := by native_decide

theorem tlXbar8_inputs_positive : tlXbar8Circuit.inputs.length > 0 := by native_decide

theorem tlXbar8_outputs_positive : tlXbar8Circuit.outputs.length > 0 := by native_decide

theorem tlXbar8_gates_positive : tlXbar8Circuit.gates.length > 0 := by native_decide

end Shoumei.Interconnect.TileLink
