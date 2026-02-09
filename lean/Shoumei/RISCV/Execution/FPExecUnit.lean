/-
RISCV/Execution/FPExecUnit.lean - Floating-Point Execution Unit for RV32F

Wraps the IEEE 754 SP behavioral model to create an execution unit that:
1. Receives dispatched FP instructions from the FP Reservation Station
2. Executes all F-extension operations (arithmetic, fused, compare, convert, etc.)
3. Broadcasts results on the FP CDB (or integer CDB for compare/classify/convert)

Supported operations:
- Arithmetic: FADD.S, FSUB.S, FMUL.S, FDIV.S, FSQRT.S (variable latency)
- Fused: FMADD.S, FMSUB.S, FNMADD.S, FNMSUB.S (3 sources)
- Compare: FEQ.S, FLT.S, FLE.S (→ integer rd)
- Convert: FCVT.W.S, FCVT.WU.S, FCVT.S.W, FCVT.S.WU
- Move: FMV.X.W, FMV.W.X (bit-preserving)
- Classify: FCLASS.S (→ integer rd)
- Min/Max: FMIN.S, FMAX.S
- Sign inject: FSGNJ.S, FSGNJN.S, FSGNJX.S

Architecture:
- **Single-cycle** for compare, convert, move, classify, sign-inject, min/max
- **Multi-cycle** for FDIV.S (~20 cycles) and FSQRT.S (~20 cycles)
- **Pipelined** for FADD.S, FSUB.S, FMUL.S, FMADD.S etc. (future; currently 1-cycle behavioral)
- Takes (opcode, src1, src2, src3, rm, dest_tag) from FP RS
- Returns (dest_tag, result, exceptions) for CDB broadcast
-/

import Shoumei.DSL
import Shoumei.RISCV.ISA
import Shoumei.RISCV.Execution.Dispatch
import Shoumei.Circuits.Combinational.FPU
import Shoumei.Circuits.Combinational.RippleCarryAdder

namespace Shoumei.RISCV.Execution

open Shoumei
open Shoumei.RISCV
open Shoumei.Circuits.Combinational
open Shoumei.Circuits.Combinational.FPU

/-! ## Operation Encoding -/

/-- Map RISC-V FP OpType to internal FPU opcode (5 bits).
    Used by the structural circuit to select the operation. -/
def opTypeToFPUOpcode (op : OpType) : Nat :=
  match op with
  | .FADD_S   => 0
  | .FSUB_S   => 1
  | .FMUL_S   => 2
  | .FDIV_S   => 3
  | .FSQRT_S  => 4
  | .FMADD_S  => 5
  | .FMSUB_S  => 6
  | .FNMADD_S => 7
  | .FNMSUB_S => 8
  | .FEQ_S    => 9
  | .FLT_S    => 10
  | .FLE_S    => 11
  | .FCVT_W_S  => 12
  | .FCVT_WU_S => 13
  | .FCVT_S_W  => 14
  | .FCVT_S_WU => 15
  | .FMV_X_W  => 16
  | .FMV_W_X  => 17
  | .FCLASS_S => 18
  | .FMIN_S   => 19
  | .FMAX_S   => 20
  | .FSGNJ_S  => 21
  | .FSGNJN_S => 22
  | .FSGNJX_S => 23
  | _ => 0  -- Non-FP op (shouldn't reach FPExecUnit)

/-- Check if an FP operation is single-cycle (combinational) -/
def isSingleCycleFPOp (op : OpType) : Bool :=
  match op with
  | .FEQ_S | .FLT_S | .FLE_S
  | .FCVT_W_S | .FCVT_WU_S | .FCVT_S_W | .FCVT_S_WU
  | .FMV_X_W | .FMV_W_X | .FCLASS_S
  | .FMIN_S | .FMAX_S
  | .FSGNJ_S | .FSGNJN_S | .FSGNJX_S => true
  | _ => false

/-- Estimated cycle latency for pipelined FP operations -/
def fpOpLatency (op : OpType) : Nat :=
  match op with
  | .FADD_S | .FSUB_S => 4      -- FP adder pipeline
  | .FMUL_S => 3                 -- FP multiplier pipeline
  | .FMADD_S | .FMSUB_S
  | .FNMADD_S | .FNMSUB_S => 5  -- Fused: mul + add
  | .FDIV_S => 20                -- Iterative divider
  | .FSQRT_S => 20               -- Iterative square root
  | _ => 1                       -- Single-cycle ops

/-! ## Behavioral Model -/

/-- FPU execution state.
    Tracks in-flight multi-cycle operations (div/sqrt). -/
structure FPExecState where
  /-- Is a multi-cycle operation in progress? -/
  busy : Bool := false
  /-- Cycles remaining for current operation -/
  cyclesRemaining : Nat := 0
  /-- Pending result (computed at start, held until cycles expire) -/
  pendingResult : Option (Fin 64 × UInt32 × FPExceptions) := none
  deriving Repr

/-- Initial (reset) state for FP execution unit -/
def FPExecState.init : FPExecState := {}

/-- Execute an FP operation (behavioral model).

    **Inputs:**
    - opcode: RISC-V FP operation type
    - src1, src2, src3: Operand values (src3 only for fused ops)
    - rm: Rounding mode (from instruction or frm CSR)
    - dest_tag: Physical register tag for result

    **Output:**
    - (dest_tag, result, exceptions): For CDB broadcast

    **Notes:**
    - Behavioral model computes result immediately (combinational)
    - Structural circuit will pipeline; latency tracked by fpOpLatency
-/
def executeFPOp
    (opcode : OpType)
    (src1 : UInt32)
    (src2 : UInt32)
    (src3 : UInt32)
    (rm : RoundingMode)
    (dest_tag : Fin 64)
    : (Fin 64 × UInt32 × FPExceptions) :=
  let result := executeFP opcode src1 src2 src3 rm
  (dest_tag, result.value, result.exceptions)

/-- Step the FPU by one clock cycle.

    For single-cycle ops, result is available immediately.
    For multi-cycle ops (div/sqrt), the operation is started and
    the result becomes available after the appropriate number of cycles.

    Returns: (newState, optionalResult) -/
def fpExecStep
    (state : FPExecState)
    (opcode : OpType)
    (src1 src2 src3 : UInt32)
    (rm : RoundingMode)
    (dest_tag : Fin 64)
    (valid : Bool)
    : FPExecState × Option (Fin 64 × UInt32 × FPExceptions) :=

  -- Check if a pending multi-cycle op completes this cycle
  if state.busy then
    if state.cyclesRemaining <= 1 then
      -- Multi-cycle op completes
      ({ busy := false, cyclesRemaining := 0, pendingResult := none },
       state.pendingResult)
    else
      -- Still in progress
      ({ state with cyclesRemaining := state.cyclesRemaining - 1 }, none)
  else if valid then
    let result := executeFPOp opcode src1 src2 src3 rm dest_tag
    let latency := fpOpLatency opcode
    if latency <= 1 then
      -- Single-cycle: return immediately
      (state, some result)
    else
      -- Multi-cycle: start and hold result
      ({ busy := true, cyclesRemaining := latency - 1, pendingResult := some result },
       none)
  else
    (state, none)

/-- Whether the FPU is busy (cannot accept new operations) -/
def FPExecState.isBusy (state : FPExecState) : Bool :=
  state.busy

/-! ## CDB Integration -/

/-- FP CDB broadcast message (extends CDBBroadcast with exception flags) -/
structure FPCDBBroadcast where
  /-- Physical register tag being written -/
  tag : Fin 64
  /-- Computed data value -/
  data : UInt32
  /-- Exception flags to accumulate in fflags -/
  exceptions : FPExceptions := {}
  deriving Repr

/-- Execute FP op and create CDB broadcast -/
def fpExecuteToCDB
    (opcode : OpType)
    (src1 src2 src3 : UInt32)
    (rm : RoundingMode)
    (dest_tag : Fin 64)
    : FPCDBBroadcast :=
  let (tag, result, exc) := executeFPOp opcode src1 src2 src3 rm dest_tag
  { tag := tag, data := result, exceptions := exc }

/-! ## Structural Circuit -/

/-- Build FP Execution Unit structural circuit.

    **Architecture:**
    - Behavioral model is used for simulation/cosim
    - Structural implementation wraps sub-units:
      * FP Adder (for FADD, FSUB)
      * FP Multiplier (for FMUL)
      * FP FMA unit (for FMADD, FMSUB, FNMADD, FNMSUB)
      * FP Divider/Sqrt (iterative, shared unit for FDIV, FSQRT)
      * Combinational logic for compare, convert, classify, move, sign-inject

    **Inputs (110):**
    - src1[31:0]: First FP operand
    - src2[31:0]: Second FP operand
    - src3[31:0]: Third FP operand (fused ops only)
    - op[4:0]: FPU operation encoding
    - rm[2:0]: Rounding mode
    - dest_tag[5:0]: Physical register tag for CDB broadcast
    - valid_in: New operation request
    - clock, reset: Sequential control
    - zero, one: Constant inputs

    **Outputs (45):**
    - result[31:0]: Computation result
    - tag_out[5:0]: Pass-through destination tag
    - exceptions[4:0]: Exception flags (NV, DZ, OF, UF, NX)
    - valid_out: Result ready for CDB broadcast
    - busy: Cannot accept new multi-cycle operation
-/
def mkFPExecUnit : Circuit :=
  -- Inputs
  let src1 := makeIndexedWires "src1" 32
  let src2 := makeIndexedWires "src2" 32
  let src3 := makeIndexedWires "src3" 32
  let op := makeIndexedWires "op" 5
  let rm := makeIndexedWires "rm" 3
  let dest_tag := makeIndexedWires "dest_tag" 6
  let valid_in := Wire.mk "valid_in"
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let zero := Wire.mk "zero"
  let one := Wire.mk "one"

  -- Outputs
  let result := makeIndexedWires "result" 32
  let tag_out := makeIndexedWires "tag_out" 6
  let exceptions := makeIndexedWires "exceptions" 5
  let valid_out := Wire.mk "valid_out"
  let busy := Wire.mk "busy"

  -- Tag pass-through (BUF gates)
  let tag_passthrough := List.zipWith (fun src dst =>
    Gate.mkBUF src dst
  ) dest_tag tag_out

  -- For now, valid_out = valid_in (single-cycle behavioral model)
  -- Multi-cycle support requires FSM (added when structural sub-units exist)
  let valid_gate := [Gate.mkBUF valid_in valid_out]

  -- Busy = 0 (placeholder until iterative divider/sqrt is instantiated)
  let busy_gate := [Gate.mkBUF zero busy]

  -- Result and exception outputs are placeholder BUF from zero
  -- (real implementation will come from sub-unit instances)
  let result_placeholder := result.map (fun w => Gate.mkBUF zero w)
  let exc_placeholder := exceptions.map (fun w => Gate.mkBUF zero w)

  { name := "FPExecUnit"
    inputs := src1 ++ src2 ++ src3 ++ op ++ rm ++ dest_tag ++
              [valid_in, clock, reset, zero, one]
    outputs := result ++ tag_out ++ exceptions ++ [valid_out, busy]
    gates := tag_passthrough ++ valid_gate ++ busy_gate ++
             result_placeholder ++ exc_placeholder
    instances := []
    signalGroups := [
      { name := "src1", width := 32, wires := src1 },
      { name := "src2", width := 32, wires := src2 },
      { name := "src3", width := 32, wires := src3 },
      { name := "op", width := 5, wires := op },
      { name := "rm", width := 3, wires := rm },
      { name := "dest_tag", width := 6, wires := dest_tag },
      { name := "result", width := 32, wires := result },
      { name := "tag_out", width := 6, wires := tag_out },
      { name := "exceptions", width := 5, wires := exceptions }
    ]
  }

/-- Convenience alias -/
def fpExecUnit : Circuit := mkFPExecUnit

end Shoumei.RISCV.Execution
