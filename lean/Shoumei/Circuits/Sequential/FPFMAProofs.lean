/-
FPFMAProofs.lean - Structural proofs for FPFMA

The fused datapath is a flat gate list: the CSA tree, the alignment shifters and
the rounding all build gates, so the circuit instantiates nothing.  The
behavioural argument is the reference model in verification/fma_reference.py,
which the directed test and the RISC-V corpus exercise against Spike.
-/

import Shoumei.Circuits.Sequential.FPFMA

namespace Shoumei.Circuits.Sequential

theorem fpFMA_name : fpFMACircuit.name = "FPFMA" := by rfl

theorem fpFMA_inputs : fpFMACircuit.inputs.length = 111 := by native_decide

theorem fpFMA_outputs : fpFMACircuit.outputs.length = 44 := by native_decide

theorem fpFMA_instances : fpFMACircuit.instances.length = 0 := by native_decide

end Shoumei.Circuits.Sequential
