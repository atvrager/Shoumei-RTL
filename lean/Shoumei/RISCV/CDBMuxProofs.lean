import Shoumei.RISCV.CDBMux

namespace Shoumei.RISCV.CDBMuxProofs

-- Structural proofs for CDBMux (no F extension)
theorem cdbmux_name : cdbMux.name = "CDBMux" := by native_decide
theorem cdbmux_input_count : cdbMux.inputs.length = 273 := by native_decide
theorem cdbmux_output_count : cdbMux.outputs.length = 77 := by native_decide
theorem cdbmux_gate_count : cdbMux.gates.length = 253 := by native_decide
theorem cdbmux_no_instances : cdbMux.instances.length = 0 := by native_decide

-- Structural proofs for CDBMux_F (with F extension)
theorem cdbmuxf_name : cdbMuxF.name = "CDBMux_F" := by native_decide
theorem cdbmuxf_input_count : cdbMuxF.inputs.length = 273 := by native_decide
theorem cdbmuxf_output_count : cdbMuxF.outputs.length = 77 := by native_decide
theorem cdbmuxf_gate_count : cdbMuxF.gates.length = 257 := by native_decide

end Shoumei.RISCV.CDBMuxProofs
