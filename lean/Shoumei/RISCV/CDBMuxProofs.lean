import Shoumei.RISCV.CDBMux

namespace Shoumei.RISCV.CDBMuxProofs

-- Structural proofs for CDBMuxW2 (W=2, no F extension)
theorem cdbmuxw2_name : cdbMuxW2.name = "CDBMux_W2" := by native_decide
theorem cdbmuxw2_input_count : cdbMuxW2.inputs.length = 307 := by native_decide
theorem cdbmuxw2_output_count : cdbMuxW2.outputs.length = 151 := by native_decide
theorem cdbmuxw2_gate_count : cdbMuxW2.gates.length = 241 := by native_decide
theorem cdbmuxw2_no_instances : cdbMuxW2.instances.length = 0 := by native_decide

-- Structural proofs for CDBMuxFW2 (W=2, with F extension)
theorem cdbmuxfw2_name : cdbMuxFW2.name = "CDBMux_F_W2" := by native_decide
theorem cdbmuxfw2_input_count : cdbMuxFW2.inputs.length = 307 := by native_decide
theorem cdbmuxfw2_output_count : cdbMuxFW2.outputs.length = 151 := by native_decide
theorem cdbmuxfw2_gate_count : cdbMuxFW2.gates.length = 243 := by native_decide

end Shoumei.RISCV.CDBMuxProofs
