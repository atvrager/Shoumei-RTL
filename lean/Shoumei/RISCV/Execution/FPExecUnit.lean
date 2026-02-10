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
import Shoumei.Circuits.Combinational.FPUnpack
import Shoumei.Circuits.Combinational.FPPack
import Shoumei.Circuits.Combinational.FPMisc
import Shoumei.Circuits.Combinational.RippleCarryAdder
import Shoumei.Circuits.Sequential.FPAdder
import Shoumei.Circuits.Sequential.FPMultiplier
import Shoumei.Circuits.Sequential.FPFMA
import Shoumei.Circuits.Sequential.FPDivider
import Shoumei.Circuits.Sequential.FPSqrt

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
  let result_is_int := Wire.mk "result_is_int"  -- high when result targets INT PRF

  -- ══════════════════════════════════════════════
  -- Sub-unit output wires
  -- ══════════════════════════════════════════════

  -- FPMisc (single-cycle: FSGNJ, FMV, FCLASS, etc.)
  let misc_result := makeIndexedWires "misc_result" 32
  let misc_exc := makeIndexedWires "misc_exc" 5

  -- FPAdder (4-cycle pipeline: FADD, FSUB)
  let add_result := makeIndexedWires "add_result" 32
  let add_tag := makeIndexedWires "add_tag" 6
  let add_exc := makeIndexedWires "add_exc" 5
  let add_valid := Wire.mk "add_valid"

  -- FPMultiplier (3-cycle pipeline: FMUL)
  let mul_result := makeIndexedWires "mul_result" 32
  let mul_tag := makeIndexedWires "mul_tag" 6
  let mul_exc := makeIndexedWires "mul_exc" 5
  let mul_valid := Wire.mk "mul_valid"

  -- FPFMA (5-cycle pipeline: FMADD, FMSUB, FNMADD, FNMSUB)
  let fma_result := makeIndexedWires "fma_result" 32
  let fma_tag := makeIndexedWires "fma_tag" 6
  let fma_exc := makeIndexedWires "fma_exc" 5
  let fma_valid := Wire.mk "fma_valid"

  -- FPDivider (24-cycle iterative: FDIV)
  let div_result := makeIndexedWires "div_result" 32
  let div_tag := makeIndexedWires "div_tag" 6
  let div_exc := makeIndexedWires "div_exc" 5
  let div_valid := Wire.mk "div_valid"
  let div_busy := Wire.mk "div_busy"

  -- FPSqrt (24-cycle iterative: FSQRT)
  let sqrt_result := makeIndexedWires "sqrt_result" 32
  let sqrt_tag := makeIndexedWires "sqrt_tag" 6
  let sqrt_exc := makeIndexedWires "sqrt_exc" 5
  let sqrt_valid := Wire.mk "sqrt_valid"
  let sqrt_busy := Wire.mk "sqrt_busy"

  -- ══════════════════════════════════════════════
  -- Operation decoding: detect which sub-unit should fire
  -- op encodings: FADD=0, FSUB=1, FMUL=2, FDIV=3, FSQRT=4,
  -- FMADD=5, FMSUB=6, FNMADD=7, FNMSUB=8,
  -- FEQ=9..FSGNJX=23 (single-cycle, handled by FPMisc)
  -- ══════════════════════════════════════════════

  -- Decode op_sub for FPAdder: op==0 → sub=0, op==1 → sub=1
  -- FADD (00000): op[0]=0, FSUB (00001): op[0]=1
  -- Both have op[4:1]=0000
  let op_is_add_sub := Wire.mk "op_is_add_sub"  -- op[4:1] == 0000
  let not_op1 := Wire.mk "not_op1"
  let not_op3 := Wire.mk "not_op3"
  let not_op4 := Wire.mk "not_op4"
  let op_hi_zero_01 := Wire.mk "op_hi_zero_01"
  let op_hi_zero_23 := Wire.mk "op_hi_zero_23"

  -- op==2 (FMUL): 00010
  let op_is_mul := Wire.mk "op_is_mul"
  let op1_only := Wire.mk "op1_only"  -- op[1]=1, op[0]=0

  -- op==3 (FDIV): 00011
  let op_is_div := Wire.mk "op_is_div"
  let op01_both := Wire.mk "op01_both"  -- op[1]=1, op[0]=1

  -- op==4 (FSQRT): 00100
  let op_is_sqrt := Wire.mk "op_is_sqrt"
  let op2_only := Wire.mk "op2_only"
  let not_op0 := Wire.mk "not_op0"

  -- op in {5,6,7,8} (FMA variants): op[4:3]=00, op[2]=1, or op==5..8
  -- 5=00101, 6=00110, 7=00111, 8=01000
  -- Simpler: op >= 5 && op <= 8
  -- We detect: (op[2]=1 && op[3]=0 && op[4]=0) || (op[3]=1 && op[2:0]=000 && op[4]=0)
  let op_is_fma := Wire.mk "op_is_fma"
  let op2_and_not3 := Wire.mk "op2_and_not3"
  let op2_and_not34 := Wire.mk "op2_and_not34"
  let op3_and_not24 := Wire.mk "op3_and_not24"
  let not_op2_w := Wire.mk "not_op2_w"  -- for op==8 detect

  -- op >= 9 (single-cycle misc ops)
  let op_is_misc := Wire.mk "op_is_misc"

  -- Start signals for iterative units
  let div_start := Wire.mk "div_start"
  let sqrt_start := Wire.mk "sqrt_start"

  -- Valid signals routed to pipelined units
  let add_valid_in := Wire.mk "add_valid_in"
  let mul_valid_in := Wire.mk "mul_valid_in"
  let fma_valid_in := Wire.mk "fma_valid_in"

  let decode_gates := [
    -- NOT of each op bit
    Gate.mkNOT (op[0]!) not_op0,
    Gate.mkNOT (op[1]!) not_op1,
    Gate.mkNOT (op[2]!) not_op2_w,
    Gate.mkNOT (op[3]!) not_op3,
    Gate.mkNOT (op[4]!) not_op4,

    -- op[4:1] == 0000 → FADD or FSUB
    Gate.mkAND not_op1 not_op2_w op_hi_zero_01,
    Gate.mkAND not_op3 not_op4 op_hi_zero_23,
    Gate.mkAND op_hi_zero_01 op_hi_zero_23 op_is_add_sub,

    -- op == 00010 → FMUL: op[1]=1, rest 0
    Gate.mkAND (op[1]!) not_op0 op1_only,
    Gate.mkAND op1_only not_op2_w (Wire.mk "mul_t1"),
    Gate.mkAND (Wire.mk "mul_t1") op_hi_zero_23 op_is_mul,

    -- op == 00011 → FDIV: op[1:0]=11, rest 0
    Gate.mkAND (op[0]!) (op[1]!) op01_both,
    Gate.mkAND op01_both not_op2_w (Wire.mk "div_t1"),
    Gate.mkAND (Wire.mk "div_t1") op_hi_zero_23 op_is_div,

    -- op == 00100 → FSQRT: op[2]=1, rest 0
    Gate.mkAND (op[2]!) not_op0 op2_only,
    Gate.mkAND op2_only not_op1 (Wire.mk "sqrt_t1"),
    Gate.mkAND (Wire.mk "sqrt_t1") op_hi_zero_23 op_is_sqrt,

    -- op in {5,6,7,8} → FMA: (op[2]=1 && !op[3] && !op[4]) || (op[3]=1 && !op[2] && !op[1] && !op[0] && !op[4])
    Gate.mkAND (op[2]!) not_op3 op2_and_not3,
    Gate.mkAND op2_and_not3 not_op4 op2_and_not34,
    -- For op=8 (01000): op[3]=1, op[2:0]=000
    Gate.mkAND (op[3]!) not_op2_w (Wire.mk "fma8_t1"),
    Gate.mkAND (Wire.mk "fma8_t1") not_op1 (Wire.mk "fma8_t2"),
    Gate.mkAND (Wire.mk "fma8_t2") not_op0 (Wire.mk "fma8_t3"),
    Gate.mkAND (Wire.mk "fma8_t3") not_op4 op3_and_not24,
    Gate.mkOR op2_and_not34 op3_and_not24 op_is_fma,

    -- op >= 9: anything not matched above is misc
    -- op_is_misc = NOT(add_sub OR mul OR div OR sqrt OR fma)
    Gate.mkOR op_is_add_sub op_is_mul (Wire.mk "misc_t1"),
    Gate.mkOR op_is_div op_is_sqrt (Wire.mk "misc_t2"),
    Gate.mkOR (Wire.mk "misc_t1") (Wire.mk "misc_t2") (Wire.mk "misc_t3"),
    Gate.mkOR (Wire.mk "misc_t3") op_is_fma (Wire.mk "misc_t4"),
    Gate.mkNOT (Wire.mk "misc_t4") op_is_misc,

    -- Gate valid_in to each sub-unit
    Gate.mkAND valid_in op_is_add_sub add_valid_in,
    Gate.mkAND valid_in op_is_mul mul_valid_in,
    Gate.mkAND valid_in op_is_fma fma_valid_in,
    Gate.mkAND valid_in op_is_div div_start,
    Gate.mkAND valid_in op_is_sqrt sqrt_start,

    -- FMA variant control: decode negate_product and subtract_addend from op
    -- FMADD(5)=00101: neg=0,sub=0  FMSUB(6)=00110: neg=0,sub=1
    -- FNMADD(7)=00111: neg=1,sub=0  FNMSUB(8)=01000: neg=1,sub=1
    -- For ops 5-7 (op2_and_not34): sub = op[1] AND NOT op[0] (only 6=110)
    --                               neg = op[1] AND op[0] (only 7=111)
    -- For op 8 (op3_and_not24): both sub=1 and neg=1
    Gate.mkAND (op[1]!) not_op0 (Wire.mk "fma_sub_57"),
    Gate.mkAND op2_and_not34 (Wire.mk "fma_sub_57") (Wire.mk "fma_sub_a"),
    Gate.mkOR (Wire.mk "fma_sub_a") op3_and_not24 (Wire.mk "fma_subtract_addend"),
    Gate.mkAND (op[1]!) (op[0]!) (Wire.mk "fma_neg_57"),
    Gate.mkAND op2_and_not34 (Wire.mk "fma_neg_57") (Wire.mk "fma_neg_a"),
    Gate.mkOR (Wire.mk "fma_neg_a") op3_and_not24 (Wire.mk "fma_negate_product")
  ]

  -- ══════════════════════════════════════════════
  -- Sub-unit instances
  -- ══════════════════════════════════════════════

  let misc_inst : CircuitInstance :=
    { moduleName := "FPMisc"
      instName := "u_misc"
      portMap :=
        (List.range 32 |>.flatMap fun i =>
          [ (s!"src1_{i}", src1[i]!), (s!"src2_{i}", src2[i]!) ]) ++
        (List.range 5 |>.map fun i => (s!"op_{i}", op[i]!)) ++
        [("zero", zero), ("one", one)] ++
        (List.range 32 |>.map fun i => (s!"result_{i}", misc_result[i]!)) ++
        (List.range 5 |>.map fun i => (s!"exc_{i}", misc_exc[i]!))
    }

  let adder_inst : CircuitInstance :=
    { moduleName := "FPAdder"
      instName := "u_adder"
      portMap :=
        (List.range 32 |>.flatMap fun i =>
          [ (s!"src1_{i}", src1[i]!), (s!"src2_{i}", src2[i]!) ]) ++
        [("op_sub", op[0]!)] ++  -- op[0] distinguishes FADD(0) from FSUB(1)
        (List.range 3 |>.map fun i => (s!"rm_{i}", rm[i]!)) ++
        (List.range 6 |>.map fun i => (s!"dest_tag_{i}", dest_tag[i]!)) ++
        [("valid_in", add_valid_in), ("clock", clock), ("reset", reset), ("zero", zero)] ++
        (List.range 32 |>.map fun i => (s!"result_{i}", add_result[i]!)) ++
        (List.range 6 |>.map fun i => (s!"tag_out_{i}", add_tag[i]!)) ++
        (List.range 5 |>.map fun i => (s!"exc_{i}", add_exc[i]!)) ++
        [("valid_out", add_valid)]
    }

  let mul_inst : CircuitInstance :=
    { moduleName := "FPMultiplier"
      instName := "u_mul"
      portMap :=
        (List.range 32 |>.flatMap fun i =>
          [ (s!"src1_{i}", src1[i]!), (s!"src2_{i}", src2[i]!) ]) ++
        (List.range 3 |>.map fun i => (s!"rm_{i}", rm[i]!)) ++
        (List.range 6 |>.map fun i => (s!"dest_tag_{i}", dest_tag[i]!)) ++
        [("valid_in", mul_valid_in), ("clock", clock), ("reset", reset), ("zero", zero)] ++
        (List.range 32 |>.map fun i => (s!"result_{i}", mul_result[i]!)) ++
        (List.range 6 |>.map fun i => (s!"tag_out_{i}", mul_tag[i]!)) ++
        (List.range 5 |>.map fun i => (s!"exc_{i}", mul_exc[i]!)) ++
        [("valid_out", mul_valid)]
    }

  let fma_inst : CircuitInstance :=
    { moduleName := "FPFMA"
      instName := "u_fma"
      portMap :=
        (List.range 32 |>.flatMap fun i =>
          [ (s!"src1_{i}", src1[i]!), (s!"src2_{i}", src2[i]!), (s!"src3_{i}", src3[i]!) ]) ++
        (List.range 3 |>.map fun i => (s!"rm_{i}", rm[i]!)) ++
        (List.range 6 |>.map fun i => (s!"dest_tag_{i}", dest_tag[i]!)) ++
        [("negate_product", Wire.mk "fma_negate_product"),
         ("subtract_addend", Wire.mk "fma_subtract_addend"),
         ("valid_in", fma_valid_in), ("clock", clock), ("reset", reset), ("zero", zero)] ++
        (List.range 32 |>.map fun i => (s!"result_{i}", fma_result[i]!)) ++
        (List.range 6 |>.map fun i => (s!"tag_out_{i}", fma_tag[i]!)) ++
        (List.range 5 |>.map fun i => (s!"exc_{i}", fma_exc[i]!)) ++
        [("valid_out", fma_valid)]
    }

  let div_inst : CircuitInstance :=
    { moduleName := "FPDivider"
      instName := "u_div"
      portMap :=
        (List.range 32 |>.flatMap fun i =>
          [ (s!"src1_{i}", src1[i]!), (s!"src2_{i}", src2[i]!) ]) ++
        (List.range 3 |>.map fun i => (s!"rm_{i}", rm[i]!)) ++
        (List.range 6 |>.map fun i => (s!"dest_tag_{i}", dest_tag[i]!)) ++
        [("start", div_start), ("clock", clock), ("reset", reset),
         ("zero", zero), ("one", one)] ++
        (List.range 32 |>.map fun i => (s!"result_{i}", div_result[i]!)) ++
        (List.range 6 |>.map fun i => (s!"tag_out_{i}", div_tag[i]!)) ++
        (List.range 5 |>.map fun i => (s!"exc_{i}", div_exc[i]!)) ++
        [("valid_out", div_valid), ("busy", div_busy)]
    }

  let sqrt_inst : CircuitInstance :=
    { moduleName := "FPSqrt"
      instName := "u_sqrt"
      portMap :=
        (List.range 32 |>.map fun i => (s!"src1_{i}", src1[i]!)) ++
        (List.range 3 |>.map fun i => (s!"rm_{i}", rm[i]!)) ++
        (List.range 6 |>.map fun i => (s!"dest_tag_{i}", dest_tag[i]!)) ++
        [("start", sqrt_start), ("clock", clock), ("reset", reset),
         ("zero", zero), ("one", one)] ++
        (List.range 32 |>.map fun i => (s!"result_{i}", sqrt_result[i]!)) ++
        (List.range 6 |>.map fun i => (s!"tag_out_{i}", sqrt_tag[i]!)) ++
        (List.range 5 |>.map fun i => (s!"exc_{i}", sqrt_exc[i]!)) ++
        [("valid_out", sqrt_valid), ("busy", sqrt_busy)]
    }

  -- ══════════════════════════════════════════════
  -- Output MUX: select result from completing sub-unit
  -- Priority: div_valid > sqrt_valid > fma_valid > add_valid > mul_valid > misc (valid_in && op_is_misc)
  -- ══════════════════════════════════════════════

  let misc_valid := Wire.mk "misc_valid"
  let misc_valid_gate := [Gate.mkAND valid_in op_is_misc misc_valid]

  -- Result MUX chain (priority select): start from misc, then layer higher-priority on top
  -- Level 1: MUX(misc, mul, mul_valid) → t1
  let t1_result := makeIndexedWires "t1_result" 32
  let t1_tag := makeIndexedWires "t1_tag" 6
  let t1_exc := makeIndexedWires "t1_exc" 5
  let t1_valid := Wire.mk "t1_valid"

  let mux1_gates :=
    (List.range 32 |>.map fun i =>
      Gate.mkMUX (misc_result[i]!) (mul_result[i]!) mul_valid (t1_result[i]!)) ++
    (List.range 6 |>.map fun i =>
      Gate.mkMUX (dest_tag[i]!) (mul_tag[i]!) mul_valid (t1_tag[i]!)) ++
    (List.range 5 |>.map fun i =>
      Gate.mkMUX (misc_exc[i]!) (mul_exc[i]!) mul_valid (t1_exc[i]!)) ++
    [Gate.mkOR misc_valid mul_valid t1_valid]

  -- Level 2: MUX(t1, add, add_valid) → t2
  let t2_result := makeIndexedWires "t2_result" 32
  let t2_tag := makeIndexedWires "t2_tag" 6
  let t2_exc := makeIndexedWires "t2_exc" 5
  let t2_valid := Wire.mk "t2_valid"

  let mux2_gates :=
    (List.range 32 |>.map fun i =>
      Gate.mkMUX (t1_result[i]!) (add_result[i]!) add_valid (t2_result[i]!)) ++
    (List.range 6 |>.map fun i =>
      Gate.mkMUX (t1_tag[i]!) (add_tag[i]!) add_valid (t2_tag[i]!)) ++
    (List.range 5 |>.map fun i =>
      Gate.mkMUX (t1_exc[i]!) (add_exc[i]!) add_valid (t2_exc[i]!)) ++
    [Gate.mkOR t1_valid add_valid t2_valid]

  -- Level 3: MUX(t2, fma, fma_valid) → t3
  let t3_result := makeIndexedWires "t3_result" 32
  let t3_tag := makeIndexedWires "t3_tag" 6
  let t3_exc := makeIndexedWires "t3_exc" 5
  let t3_valid := Wire.mk "t3_valid"

  let mux3_gates :=
    (List.range 32 |>.map fun i =>
      Gate.mkMUX (t2_result[i]!) (fma_result[i]!) fma_valid (t3_result[i]!)) ++
    (List.range 6 |>.map fun i =>
      Gate.mkMUX (t2_tag[i]!) (fma_tag[i]!) fma_valid (t3_tag[i]!)) ++
    (List.range 5 |>.map fun i =>
      Gate.mkMUX (t2_exc[i]!) (fma_exc[i]!) fma_valid (t3_exc[i]!)) ++
    [Gate.mkOR t2_valid fma_valid t3_valid]

  -- Level 4: MUX(t3, sqrt, sqrt_valid) → t4
  let t4_result := makeIndexedWires "t4_result" 32
  let t4_tag := makeIndexedWires "t4_tag" 6
  let t4_exc := makeIndexedWires "t4_exc" 5
  let t4_valid := Wire.mk "t4_valid"

  let mux4_gates :=
    (List.range 32 |>.map fun i =>
      Gate.mkMUX (t3_result[i]!) (sqrt_result[i]!) sqrt_valid (t4_result[i]!)) ++
    (List.range 6 |>.map fun i =>
      Gate.mkMUX (t3_tag[i]!) (sqrt_tag[i]!) sqrt_valid (t4_tag[i]!)) ++
    (List.range 5 |>.map fun i =>
      Gate.mkMUX (t3_exc[i]!) (sqrt_exc[i]!) sqrt_valid (t4_exc[i]!)) ++
    [Gate.mkOR t3_valid sqrt_valid t4_valid]

  -- Level 5: MUX(t4, div, div_valid) → output
  let mux5_gates :=
    (List.range 32 |>.map fun i =>
      Gate.mkMUX (t4_result[i]!) (div_result[i]!) div_valid (result[i]!)) ++
    (List.range 6 |>.map fun i =>
      Gate.mkMUX (t4_tag[i]!) (div_tag[i]!) div_valid (tag_out[i]!)) ++
    (List.range 5 |>.map fun i =>
      Gate.mkMUX (t4_exc[i]!) (div_exc[i]!) div_valid (exceptions[i]!)) ++
    [Gate.mkOR t4_valid div_valid valid_out]

  -- Pipeline collision prevention: after dispatching to a pipelined sub-unit (adder, mul, FMA),
  -- set busy for 1 cycle to prevent back-to-back dispatches to different pipelines.
  -- Without this, e.g., FADD(4-cycle) then FMUL(3-cycle) on consecutive cycles collide.
  let pipe_dispatched := Wire.mk "pipe_dispatched"
  let pipe_was_active := Wire.mk "pipe_was_active"
  let _pipe_any := Wire.mk "pipe_any"
  let pipe_collision_gates := [
    Gate.mkOR add_valid_in mul_valid_in (Wire.mk "pipe_am"),
    Gate.mkOR (Wire.mk "pipe_am") fma_valid_in pipe_dispatched
  ]
  let pipe_collision_inst : CircuitInstance := {
    moduleName := "DFlipFlop"
    instName := "u_pipe_active_reg"
    portMap := [("d", pipe_dispatched), ("q", pipe_was_active),
                ("clock", clock), ("reset", reset)]
  }

  -- Busy = div_busy OR sqrt_busy OR pipe_was_active OR any_pipe_output
  -- any_pipe_output prevents misc from dispatching on the same cycle as a pipeline result,
  -- which would cause the misc result to be dropped by the priority MUX.
  let busy_gate := [
    Gate.mkOR div_busy sqrt_busy (Wire.mk "busy_ds"),
    Gate.mkOR (Wire.mk "busy_ds") pipe_was_active (Wire.mk "busy_core"),
    -- Detect any pipeline output active
    Gate.mkOR add_valid mul_valid (Wire.mk "pout_am"),
    Gate.mkOR fma_valid sqrt_valid (Wire.mk "pout_fs"),
    Gate.mkOR (Wire.mk "pout_am") (Wire.mk "pout_fs") (Wire.mk "pout_amfs"),
    Gate.mkOR (Wire.mk "pout_amfs") div_valid (Wire.mk "any_pipe_output"),
    Gate.mkOR (Wire.mk "busy_core") (Wire.mk "any_pipe_output") busy
  ]

  -- result_is_int: detect when the FP result targets INT register file
  -- INT-writing FP ops (by FPU opcode): 9=FEQ, 10=FLT, 11=FLE, 12=FCVT_W_S,
  -- 13=FCVT_WU_S, 16=FMV_X_W, 18=FCLASS
  -- These are all misc ops (single-cycle), so result_is_int = misc_valid AND NOT overridden AND opcode_is_int
  -- Since misc has lowest priority in the output MUX, if any pipelined unit is valid,
  -- misc_valid is irrelevant. We use: result_is_int = misc_valid AND NOT (mul_valid OR add_valid OR fma_valid OR div_valid OR sqrt_valid) AND op_writes_int
  -- Simplified: if output is from misc path (no higher-priority), check opcode.
  -- Detect op_writes_int: op in {9..13, 16, 18}
  -- 9=01001, 10=01010, 11=01011, 12=01100, 13=01101 → op[3]=1, op[4]=0, op[2:0] in {001,010,011,100,101}
  -- 16=10000, 18=10010 → op[4]=1
  -- So: op_writes_int = (op[3] AND NOT op[4]) OR (op[4] AND NOT op[3] AND NOT op[2] AND (NOT op[0] OR NOT op[1]))
  -- Actually simpler: just check op[3]=1 XOR op[4]=1 (one of them set, not both), excluding op=8 (01000) and 14,15 (01110,01111) and 17 (10001) and 19+ (10011+)
  -- Easiest: enumerate and OR
  let op_writes_int := Wire.mk "op_writes_int"
  -- op[3]=1 AND op[4]=0: covers 8-15. Exclude 8 (op[2:0]=000) and 14 (op[2:1]=11,op[0]=0) and 15 (op[2:0]=111)
  -- So: op[3] AND NOT op[4] AND NOT(op[2] AND op[1]) AND (op[0] OR op[1] OR op[2])
  let grp_8_15 := Wire.mk "grp_8_15"
  let not_both_21 := Wire.mk "not_both_21"
  let any_210 := Wire.mk "any_210"
  let grp_8_15_filt := Wire.mk "grp_8_15_filt"
  -- op[4]=1: covers 16-23. INT-writing: 16 (10000), 18 (10010). NOT: 17,19,20,21,22,23
  -- 16: op[3:0]=0000, 18: op[3:0]=0010
  -- Both have op[3]=0, op[0]=0. 16: op[2:1]=00, 18: op[2]=0,op[1]=1
  -- So: op[4] AND NOT op[3] AND NOT op[0] AND NOT op[2]
  let grp_16_18 := Wire.mk "grp_16_18"
  let int_result_gates := [
    -- Group 9-13: op[3]=1, op[4]=0, not (op[2] AND op[1]), and (op[0] OR op[1] OR op[2])
    Gate.mkAND (op[3]!) not_op4 grp_8_15,
    Gate.mkAND (op[2]!) (op[1]!) (Wire.mk "both_21"),
    Gate.mkNOT (Wire.mk "both_21") not_both_21,
    Gate.mkOR (op[0]!) (op[1]!) (Wire.mk "any_01"),
    Gate.mkOR (Wire.mk "any_01") (op[2]!) any_210,
    Gate.mkAND grp_8_15 not_both_21 (Wire.mk "grp_filt1"),
    Gate.mkAND (Wire.mk "grp_filt1") any_210 grp_8_15_filt,
    -- Group 16,18: op[4]=1, op[3]=0, op[0]=0, op[2]=0
    Gate.mkAND (op[4]!) not_op3 (Wire.mk "g16_t1"),
    Gate.mkAND not_op0 not_op2_w (Wire.mk "g16_t2"),
    Gate.mkAND (Wire.mk "g16_t1") (Wire.mk "g16_t2") grp_16_18,
    -- Combine
    Gate.mkOR grp_8_15_filt grp_16_18 op_writes_int,
    -- result_is_int = misc_valid AND no higher-priority AND op_writes_int
    -- Since misc is lowest priority: if any other valid, misc result is overridden
    Gate.mkOR mul_valid add_valid (Wire.mk "rint_t1"),
    Gate.mkOR fma_valid div_valid (Wire.mk "rint_t2"),
    Gate.mkOR sqrt_valid (Wire.mk "rint_t1") (Wire.mk "rint_t3"),
    Gate.mkOR (Wire.mk "rint_t2") (Wire.mk "rint_t3") (Wire.mk "rint_t4"),
    Gate.mkNOT (Wire.mk "rint_t4") (Wire.mk "no_override"),
    Gate.mkAND misc_valid (Wire.mk "no_override") (Wire.mk "rint_t5"),
    Gate.mkAND (Wire.mk "rint_t5") op_writes_int result_is_int
  ]

  { name := "FPExecUnit"
    inputs := src1 ++ src2 ++ src3 ++ op ++ rm ++ dest_tag ++
              [valid_in, clock, reset, zero, one]
    outputs := result ++ tag_out ++ exceptions ++ [valid_out, busy, result_is_int]
    gates := decode_gates ++ misc_valid_gate ++
             mux1_gates ++ mux2_gates ++ mux3_gates ++ mux4_gates ++ mux5_gates ++
             pipe_collision_gates ++ busy_gate ++ int_result_gates
    instances := [misc_inst, adder_inst, mul_inst, fma_inst, div_inst, sqrt_inst,
                  pipe_collision_inst]
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
    keepHierarchy := true
  }

/-- Convenience alias -/
def fpExecUnit : Circuit := mkFPExecUnit

end Shoumei.RISCV.Execution
