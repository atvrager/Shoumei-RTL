/-
Microcode/TrapSequencerCodegen.lean - Exports TrapSequencer circuit for code generation
-/

import Shoumei.RISCV.Microcode.TrapSequencer

namespace Shoumei.RISCV.Microcode

/-- TrapSequencer circuit for codegen -/
def trapSequencerCircuitExport : Circuit := trapSequencerCircuit

end Shoumei.RISCV.Microcode
