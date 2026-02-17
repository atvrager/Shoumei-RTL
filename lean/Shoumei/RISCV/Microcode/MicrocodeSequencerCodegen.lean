/-
Microcode Sequencer Codegen - Circuit definitions for code generation

Exports the MicrocodeDecoder and MicrocodeSequencer circuits for inclusion
in GenerateAll.lean.
-/

import Shoumei.RISCV.Microcode.MicrocodeDecoder
import Shoumei.RISCV.Microcode.MicrocodeSequencer

namespace Shoumei.RISCV.Microcode

/-- Microcode decoder circuit for codegen -/
def microcodeDecoderCircuit : Circuit := mkMicrocodeDecoder

/-- Microcode sequencer circuit for codegen -/
def microcodeSequencerCircuit : Circuit := mkMicrocodeSequencer

end Shoumei.RISCV.Microcode
