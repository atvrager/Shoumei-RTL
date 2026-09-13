/-
FPFMADProofs.lean - Structural proofs for FPFMAD
-/

import Shoumei.Circuits.Sequential.FPFMAD

namespace Shoumei.Circuits.Sequential

theorem fpFMAD_name : fpFMADCircuit.name = "FPFMAD" := by rfl

theorem fpFMAD_inputs : fpFMADCircuit.inputs.length = 207 := by native_decide

theorem fpFMAD_outputs : fpFMADCircuit.outputs.length = 76 := by native_decide

theorem fpFMAD_instances : fpFMADCircuit.instances.length = 2 := by native_decide

end Shoumei.Circuits.Sequential
