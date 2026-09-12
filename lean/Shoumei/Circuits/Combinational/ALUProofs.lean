/-
Proofs for ALU32 - 32-bit Arithmetic Logic Unit

Structural verification that ALU32 correctly integrates all RV32I operations.
-/

import Shoumei.Circuits.Combinational.ALU

namespace Shoumei.Circuits.Combinational

open Shoumei

-- ALU32 structural properties
theorem alu32_structure :
  mkALU32.inputs.length = 70 ∧  -- 32 a + 32 b + 4 opcode + 1 zero + 1 one = 70
  mkALU32.outputs.length = 32 ∧
  mkALU32.name = "ALU32" := by
  native_decide

-- Verify total gate count is reasonable
-- mkALU32 is hierarchical: the arithmetic/logic/shift units are CircuitInstances,
-- so `.gates` holds only the glue logic (comparison zero-extension + MUX trees).
-- 256 = 2 × 32 zero-extension BUFs + 6 × 32 selection MUXes.
theorem alu32_gate_count_reasonable :
  mkALU32.gates.length = 256 := by
  native_decide

end Shoumei.Circuits.Combinational
