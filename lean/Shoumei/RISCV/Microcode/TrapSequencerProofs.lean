/-
Microcode/TrapSequencerProofs.lean - Structural proofs for TrapSequencer
-/

import Shoumei.RISCV.Microcode.TrapSequencer

namespace Shoumei.RISCV.Microcode

open Shoumei

theorem trapSequencer_inputs : trapSequencerCircuit.inputs.length = 72 := by native_decide

theorem trapSequencer_outputs : trapSequencerCircuit.outputs.length = 71 := by native_decide

theorem trapSequencer_instances : trapSequencerCircuit.instances.length = 4 := by native_decide

theorem trapSequencer_gates : trapSequencerCircuit.gates.length = 326 := by native_decide

theorem trapSequencer_name : trapSequencerCircuit.name = "TrapSequencer" := by native_decide

end Shoumei.RISCV.Microcode
