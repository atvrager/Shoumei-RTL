/-
Circuits/Sequential/FPFMAD.lean - Double-Precision Fused Multiply-Add

Computes src1 * src2 ± src3 with one rounding, like FPFMA: the exact product
from a CSA tree, a 110-bit alignment window, one rounding, and the flags of
the rounded result.  Geometry and corrections are checked in
verification/fma_reference.py against exact arithmetic at 53-bit precision.

Interface:
- Inputs: src1[63:0], src2[63:0], src3[63:0], rm[2:0], dest_tag[5:0],
          negate_product, subtract_addend, valid_in, clock, reset, zero
- Outputs: result[63:0], tag_out[5:0], exc[4:0], valid_out
-/

import Shoumei.DSL
import Shoumei.Circuits.Sequential.FPFMA

namespace Shoumei.Circuits.Sequential

open Shoumei

/-- The double-precision fused multiply-add.  Same builder as the
    single-precision unit with the format's three constants. -/
def mkFPFMAD : Circuit := mkFPFMAFusedP "FPFMAD" 53 1023 11

def fpFMADCircuit : Circuit := mkFPFMAD

end Shoumei.Circuits.Sequential
