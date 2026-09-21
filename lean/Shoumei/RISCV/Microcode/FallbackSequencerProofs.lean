/-
Microcode/FallbackSequencerProofs.lean - Structural proofs for FallbackSequencer

The gate count is dominated by the control store: 32 field bits, each a
512-entry mux tree (511 muxes), plus the three carry-less multiply datapaths.
It is pinned here so an accidental change to the micro-ALU or the store shows
up as a failed build rather than as a silent area regression.
-/

import Shoumei.RISCV.Microcode.FallbackSequencer

namespace Shoumei.RISCV.Microcode

open Shoumei

theorem fallbackSequencer_name : fallbackSequencerCircuit.name = "FallbackSequencer" := by native_decide

theorem fallbackSequencer_inputs : fallbackSequencerCircuit.inputs.length = 236 := by native_decide

theorem fallbackSequencer_outputs : fallbackSequencerCircuit.outputs.length = 266 := by native_decide

theorem fallbackSequencer_instances : fallbackSequencerCircuit.instances.length = 5 := by native_decide

theorem fallbackSequencer_gates : fallbackSequencerCircuit.gates.length = 43240 := by native_decide

end Shoumei.RISCV.Microcode
