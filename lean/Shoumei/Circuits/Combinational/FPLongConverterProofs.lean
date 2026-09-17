/-
Circuits/Combinational/FPLongConverterProofs.lean - Structural Proofs for 64-Bit FP/Integer Converter
-/

import Shoumei.Circuits.Combinational.FPLongConverter

namespace Shoumei.Circuits.Combinational

open Shoumei

/-- Port count: 72 inputs (src1[64], op[3], rm[3], zero, one). -/
theorem fpLongConverterCircuit_inputs :
    fpLongConverterCircuit.inputs.length = 72 := by native_decide

/-- Port count: 70 outputs (result[64], exc[5], result_is_int). -/
theorem fpLongConverterCircuit_outputs :
    fpLongConverterCircuit.outputs.length = 70 := by native_decide

/-- Submodules: Int64ToFP and FPToInt64. -/
theorem fpLongConverterCircuit_instances :
    fpLongConverterCircuit.instances.length = 2 := by native_decide

end Shoumei.Circuits.Combinational
