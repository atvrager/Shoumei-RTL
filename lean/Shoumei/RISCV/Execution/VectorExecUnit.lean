/-
RISCV/Execution/VectorExecUnit.lean - Vector Execution Unit (Zve32x)

Thin wrapper that packages scalar decoder outputs into the RVVInstruction
format expected by the external RvvCore (coralnpu). The RvvCore handles
its own internal decode, execution, and vector register file.

The scalar CPU treats vector instructions as opaque: they are dispatched
to the vector unit and do not produce scalar CDB results (except vsetvl
variants which write vl to a scalar rd via the async_rd port).

RVVInstruction format (from rvv_backend.svh):
  { pc[31:0], opcode[1:0], bits[24:0] }
  opcode: LOAD=0, STORE=1, RVV=2

Architecture:
- Vector instructions bypass Reservation Stations entirely
- Backpressure via inst_ready / queue_capacity from RvvCore
- Scalar register values (rs1/rs2) forwarded to RvvCore reg_read_data
- Scalar writebacks (vmv.x.s, vsetvl) via async_rd muxed into PhysRegFile
- Traps from RvvCore trigger pipeline flush
-/

import Shoumei.RISCV.ISA
import Shoumei.RISCV.Config

namespace Shoumei.RISCV.Execution

open Shoumei.RISCV

/-- Map vector OpType to RVVOpCode encoding.
    LOAD=0, STORE=1, RVV=2 (arithmetic/config) -/
def vectorOpToRvvOpcode (op : OpType) : Nat :=
  match op with
  | .VECTOR_LOAD  => 0  -- LOAD
  | .VECTOR_STORE => 1  -- STORE
  | .VECTOR_ARITH => 2  -- RVV (arithmetic, vsetvl, etc.)
  | _             => 2  -- default (shouldn't reach vector unit)

/-- Check if a vector instruction produces a scalar writeback.
    vsetvl/vsetvli/vsetivli write vl to scalar rd. These are encoded
    as VECTOR_ARITH with specific funct3/funct6 patterns, but the
    RvvCore handles detection internally and signals via reg_write_valid
    (synchronous, for config ops) or async_rd_valid (for vmv.x.s etc). -/
def isVectorScalarWriteback (_op : OpType) : Bool :=
  -- RvvCore signals scalar writebacks dynamically; the scalar side
  -- doesn't need to predict this at dispatch time.
  false

end Shoumei.RISCV.Execution
