/-
Microcode/FallbackSequencerCodegen.lean - Exports FallbackSequencer circuit for code generation
-/

import Shoumei.RISCV.Microcode.FallbackSequencer

namespace Shoumei.RISCV.Microcode

/-- FallbackSequencer circuit for codegen -/
def fallbackSequencerCircuitExport : Circuit := fallbackSequencerCircuit

end Shoumei.RISCV.Microcode
