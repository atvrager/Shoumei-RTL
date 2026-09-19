/-
Microcode/FallbackSequencerProofs.lean - Structural proofs for FallbackSequencer
-/

import Shoumei.RISCV.Microcode.FallbackSequencer

namespace Shoumei.RISCV.Microcode

open Shoumei

theorem fallbackSequencer_name : fallbackSequencerCircuit.name = "FallbackSequencer" := by native_decide

theorem fallbackSequencer_inputs : fallbackSequencerCircuit.inputs.length = 279 := by native_decide

theorem fallbackSequencer_outputs : fallbackSequencerCircuit.outputs.length = 267 := by native_decide

theorem fallbackSequencer_instances : fallbackSequencerCircuit.instances.length = 5 := by native_decide

theorem fallbackSequencer_gates : fallbackSequencerCircuit.gates.length = 9056 := by native_decide

end Shoumei.RISCV.Microcode
