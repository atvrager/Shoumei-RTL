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
import Shoumei.Circuits.Combinational.FPUDouble
import Shoumei.Circuits.Combinational.FPDoubleMisc
import Shoumei.Circuits.Combinational.FPDoubleConverter
import Shoumei.Circuits.Combinational.FPLongConverter
import Shoumei.Circuits.Sequential.FPAdderD
import Shoumei.Circuits.Sequential.FPMultiplierD
import Shoumei.Circuits.Sequential.FPFMAD
import Shoumei.Circuits.Sequential.FPDividerD
import Shoumei.Circuits.Sequential.FPSqrtD

namespace Shoumei.RISCV.Execution

open Shoumei
open Shoumei.RISCV
open Shoumei.Circuits.Combinational
open Shoumei.Circuits.Combinational.FPU

/-! ## Operation Encoding -/

/-- Map RISC-V FP OpType to internal FPU opcode (6 bits).
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
  | .FCVT_L_S  => 24
  | .FCVT_LU_S => 25
  | .FCVT_S_L  => 26
  | .FCVT_S_LU => 27
  | .FADD_D   => 32
  | .FSUB_D   => 33
  | .FMUL_D   => 34
  | .FDIV_D   => 35
  | .FSQRT_D  => 36
  | .FMADD_D  => 37
  | .FMSUB_D  => 38
  | .FNMADD_D => 39
  | .FNMSUB_D => 40
  | .FEQ_D    => 41
  | .FLT_D    => 42
  | .FLE_D    => 43
  | .FCVT_W_D  => 44
  | .FCVT_WU_D => 45
  | .FCVT_D_W  => 46
  | .FCVT_D_WU => 47
  | .FCVT_S_D  => 48
  | .FCVT_D_S  => 49
  | .FCLASS_D => 50
  | .FMIN_D   => 51
  | .FMAX_D   => 52
  | .FSGNJ_D  => 53
  | .FSGNJN_D => 54
  | .FSGNJX_D => 55
  | .FMV_X_D  => 56
  | .FMV_D_X  => 57
  | .FCVT_L_D  => 58
  | .FCVT_LU_D => 59
  | .FCVT_D_L  => 60
  | .FCVT_D_LU => 61
  | _ => 0  -- Non-FP op (shouldn't reach FPExecUnit)

/-- Check if an FP operation is single-cycle (combinational) -/
def isSingleCycleFPOp (op : OpType) : Bool :=
  match op with
  | .FEQ_S | .FLT_S | .FLE_S
  | .FCVT_W_S | .FCVT_WU_S | .FCVT_S_W | .FCVT_S_WU
  | .FMV_X_W | .FMV_W_X | .FCLASS_S
  | .FMIN_S | .FMAX_S
  | .FSGNJ_S | .FSGNJN_S | .FSGNJX_S
  | .FCVT_L_S | .FCVT_LU_S | .FCVT_S_L | .FCVT_S_LU
  | .FEQ_D | .FLT_D | .FLE_D
  | .FCVT_W_D | .FCVT_WU_D | .FCVT_D_W | .FCVT_D_WU
  | .FCVT_S_D | .FCVT_D_S | .FCLASS_D
  | .FMIN_D | .FMAX_D
  | .FSGNJ_D | .FSGNJN_D | .FSGNJX_D
  | .FCVT_L_D | .FCVT_LU_D | .FCVT_D_L | .FCVT_D_LU
  | .FMV_X_D | .FMV_D_X => true
  | _ => false

/-- Estimated cycle latency for pipelined FP operations -/
def fpOpLatency (op : OpType) : Nat :=
  match op with
  | .FADD_S | .FSUB_S | .FADD_D | .FSUB_D => 4      -- FP adder pipeline
  | .FMUL_S | .FMUL_D => 3                           -- FP multiplier pipeline
  | .FMADD_S | .FMSUB_S | .FNMADD_S | .FNMSUB_S
  | .FMADD_D | .FMSUB_D | .FNMADD_D | .FNMSUB_D => 5 -- Fused: mul + add
  | .FDIV_S => 20                                    -- Iterative divider SP
  | .FSQRT_S => 20                                   -- Iterative square root SP
  | .FDIV_D => 54                                    -- Iterative divider DP
  | .FSQRT_D => 54                                   -- Iterative square root DP
  | _ => 1                                           -- Single-cycle ops

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
  -- Reset buffer tree: fan out reset to 6 sub-units via BUF gates
  -- Prevents Yosys from merging these into a single high-fanout net
  -- ══════════════════════════════════════════════
  let reset_add := Wire.mk "reset_buf_add"
  let reset_mul := Wire.mk "reset_buf_mul"
  let reset_fma := Wire.mk "reset_buf_fma"
  let reset_div := Wire.mk "reset_buf_div"
  let reset_sqrt := Wire.mk "reset_buf_sqrt"
  let reset_misc := Wire.mk "reset_buf_misc"
  let reset_buf_gates := [
    Gate.mkBUF reset reset_add,
    Gate.mkBUF reset reset_mul,
    Gate.mkBUF reset reset_fma,
    Gate.mkBUF reset reset_div,
    Gate.mkBUF reset reset_sqrt,
    Gate.mkBUF reset reset_misc]

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
  -- FMADD=5, FMSUB=6, FNMSUB=7, FNMADD=8,
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

    -- op in {5,6,7,8} → FMA: (op[2]=1 && (op[0]||op[1]) && !op[3] && !op[4]) || (op[3]=1 && !op[2] && !op[1] && !op[0] && !op[4])
    -- Note: must require (op[0]||op[1]) to exclude op=4 (FSQRT=00100)
    Gate.mkOR (op[0]!) (op[1]!) (Wire.mk "op01_any"),
    Gate.mkAND (op[2]!) (Wire.mk "op01_any") op2_and_not3,
    Gate.mkAND op2_and_not3 not_op3 (Wire.mk "op2_and_not3_real"),
    Gate.mkAND (Wire.mk "op2_and_not3_real") not_op4 op2_and_not34,
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
    -- FNMADD(7)=00111: neg=1,sub=1  FNMSUB(8)=01000: neg=1,sub=0
    -- For ops 5-7 (op2_and_not34): sub = op[1] (matches 6=110 and 7=111)
    --                               neg = op[1] AND op[0] (only 7=111)
    -- For op 8 (op3_and_not24): neg=1 only (sub=0)
    Gate.mkAND op2_and_not34 (op[1]!) (Wire.mk "fma_sub_a"),
    Gate.mkBUF (Wire.mk "fma_sub_a") (Wire.mk "fma_subtract_addend"),
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
        (List.range 3 |>.map fun i => (s!"rm_{i}", rm[i]!)) ++
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
        [("valid_in", add_valid_in), ("clock", clock), ("reset", reset_add), ("zero", zero)] ++
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
        [("valid_in", mul_valid_in), ("clock", clock), ("reset", reset_mul), ("zero", zero)] ++
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
         ("valid_in", fma_valid_in), ("clock", clock), ("reset", reset_fma), ("zero", zero)] ++
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
        [("start", div_start), ("clock", clock), ("reset", reset_div),
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
        [("start", sqrt_start), ("clock", clock), ("reset", reset_sqrt),
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

  -- Level 4: MUX(t3, div, div_valid) → t4
  let t4_result := makeIndexedWires "t4_result" 32
  let t4_tag := makeIndexedWires "t4_tag" 6
  let t4_exc := makeIndexedWires "t4_exc" 5
  let t4_valid := Wire.mk "t4_valid"

  let mux4_gates :=
    (List.range 32 |>.map fun i =>
      Gate.mkMUX (t3_result[i]!) (div_result[i]!) div_valid (t4_result[i]!)) ++
    (List.range 6 |>.map fun i =>
      Gate.mkMUX (t3_tag[i]!) (div_tag[i]!) div_valid (t4_tag[i]!)) ++
    (List.range 5 |>.map fun i =>
      Gate.mkMUX (t3_exc[i]!) (div_exc[i]!) div_valid (t4_exc[i]!)) ++
    [Gate.mkOR t3_valid div_valid t4_valid]

  -- Level 5: MUX(t4, sqrt, sqrt_valid) → output (sqrt gets higher priority)
  let mux5_gates :=
    (List.range 32 |>.map fun i =>
      Gate.mkMUX (t4_result[i]!) (sqrt_result[i]!) sqrt_valid (result[i]!)) ++
    (List.range 6 |>.map fun i =>
      Gate.mkMUX (t4_tag[i]!) (sqrt_tag[i]!) sqrt_valid (tag_out[i]!)) ++
    (List.range 5 |>.map fun i =>
      Gate.mkMUX (t4_exc[i]!) (sqrt_exc[i]!) sqrt_valid (exceptions[i]!)) ++
    [Gate.mkOR t4_valid sqrt_valid valid_out]

  -- Pipeline collision prevention: after dispatching to a pipelined sub-unit (adder, mul, FMA),
  -- keep busy for 2 cycles to prevent output collisions from different pipelines.
  -- With latencies ADD=3, MUL=3, FMA=5, a 2-cycle gap (1 DFF) allows FMA@t0 and ADD@t2
  -- to both complete at t+5=t+2+3, dropping one result. A 3-cycle gap (2 DFFs) prevents
  -- all collisions: min gap=3 means completion times differ by at least |L_A - L_B - 3|.
  let pipe_dispatched := Wire.mk "pipe_dispatched"
  let pipe_active_d1 := Wire.mk "pipe_active_d1"
  let pipe_active_d2 := Wire.mk "pipe_active_d2"
  let _pipe_any := Wire.mk "pipe_any"
  let pipe_collision_gates := [
    Gate.mkOR add_valid_in mul_valid_in (Wire.mk "pipe_am"),
    Gate.mkOR (Wire.mk "pipe_am") fma_valid_in pipe_dispatched
  ]
  let pipe_collision_inst1 : CircuitInstance := {
    moduleName := "DFlipFlop"
    instName := "u_pipe_active_reg1"
    portMap := [("d", pipe_dispatched), ("q", pipe_active_d1),
                ("clock", clock), ("reset", reset_misc)]
  }
  let pipe_collision_inst2 : CircuitInstance := {
    moduleName := "DFlipFlop"
    instName := "u_pipe_active_reg2"
    portMap := [("d", pipe_active_d1), ("q", pipe_active_d2),
                ("clock", clock), ("reset", reset_misc)]
  }
  let pipe_was_active := Wire.mk "pipe_was_active"
  let pipe_active_or_gate := [Gate.mkOR pipe_active_d1 pipe_active_d2 pipe_was_active]

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
    gates := reset_buf_gates ++ decode_gates ++ misc_valid_gate ++
             mux1_gates ++ mux2_gates ++ mux3_gates ++ mux4_gates ++ mux5_gates ++
             pipe_collision_gates ++ pipe_active_or_gate ++ busy_gate ++ int_result_gates
    instances := [misc_inst, adder_inst, mul_inst, fma_inst, div_inst, sqrt_inst,
                  pipe_collision_inst1, pipe_collision_inst2]
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

/-- Build Combined Single+Double FP Execution Unit structural circuit for RV32D.

    Instantiates both SP (F-extension) and DP (D-extension) sub-units:
    - SP units: FPMisc, FPAdder, FPMultiplier, FPFMA, FPDivider, FPSqrt
    - DP units: FPDoubleMisc, FPDoubleConverter, FPAdderD, FPMultiplierD, FPFMAD, FPDividerD, FPSqrtD
    - Input NaN-unboxing for SP operands
    - Output NaN-boxing for SP results (bits 63:32 = 0xFFFFFFFF)
    - 5-stage priority multiplexing for writeback
-/
def mkFPExecUnitD : Circuit :=
  -- Inputs (64-bit operands, 6-bit opcode)
  let src1 := makeIndexedWires "src1" 64
  let src2 := makeIndexedWires "src2" 64
  let src3 := makeIndexedWires "src3" 64
  let op := makeIndexedWires "op" 6
  let rm := makeIndexedWires "rm" 3
  let dest_tag := makeIndexedWires "dest_tag" 6
  let valid_in := Wire.mk "valid_in"
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let zero := Wire.mk "zero"
  let one := Wire.mk "one"

  -- Outputs
  let result := makeIndexedWires "result" 64
  let tag_out := makeIndexedWires "tag_out" 6
  let exceptions := makeIndexedWires "exceptions" 5
  let valid_out := Wire.mk "valid_out"
  let busy := Wire.mk "busy"
  let result_is_int := Wire.mk "result_is_int"

  -- Reset fanout tree
  let reset_add_sp := Wire.mk "rst_add_sp"
  let reset_mul_sp := Wire.mk "rst_mul_sp"
  let reset_fma_sp := Wire.mk "rst_fma_sp"
  let reset_div_sp := Wire.mk "rst_div_sp"
  let reset_sqrt_sp := Wire.mk "rst_sqrt_sp"
  let reset_misc_sp := Wire.mk "rst_misc_sp"
  let reset_add_dp := Wire.mk "rst_add_dp"
  let reset_mul_dp := Wire.mk "rst_mul_dp"
  let reset_fma_dp := Wire.mk "rst_fma_dp"
  let reset_div_dp := Wire.mk "rst_div_dp"
  let reset_sqrt_dp := Wire.mk "rst_sqrt_dp"
  let reset_misc_dp := Wire.mk "rst_misc_dp"
  let reset_gates := [
    Gate.mkBUF reset reset_add_sp, Gate.mkBUF reset reset_mul_sp,
    Gate.mkBUF reset reset_fma_sp, Gate.mkBUF reset reset_div_sp,
    Gate.mkBUF reset reset_sqrt_sp, Gate.mkBUF reset reset_misc_sp,
    Gate.mkBUF reset reset_add_dp, Gate.mkBUF reset reset_mul_dp,
    Gate.mkBUF reset reset_fma_dp, Gate.mkBUF reset reset_div_dp,
    Gate.mkBUF reset reset_sqrt_dp, Gate.mkBUF reset reset_misc_dp
  ]

  -- Inverted op bits
  let not_op0 := Wire.mk "nop0"
  let not_op1 := Wire.mk "nop1"
  let not_op2 := Wire.mk "nop2"
  let not_op3 := Wire.mk "nop3"
  let not_op4 := Wire.mk "nop4"
  let not_op5 := Wire.mk "nop5"
  let op_inv_gates := [
    Gate.mkNOT (op[0]!) not_op0, Gate.mkNOT (op[1]!) not_op1,
    Gate.mkNOT (op[2]!) not_op2, Gate.mkNOT (op[3]!) not_op3,
    Gate.mkNOT (op[4]!) not_op4, Gate.mkNOT (op[5]!) not_op5
  ]

  let is_dp := op[5]!
  let is_sp := not_op5

  -- Opcode category decoding (shared by SP and DP via op[4:0])
  let op_is_add_sub := Wire.mk "op_is_add_sub"
  let op_is_mul := Wire.mk "op_is_mul"
  let op_is_div := Wire.mk "op_is_div"
  let op_is_sqrt := Wire.mk "op_is_sqrt"
  let op_is_fma := Wire.mk "op_is_fma"
  let op_is_misc := Wire.mk "op_is_misc"

  let op_hi_zero_01 := Wire.mk "op_hz01"
  let op_hi_zero_23 := Wire.mk "op_hz23"
  let op1_only := Wire.mk "op1_only"
  let op01_both := Wire.mk "op01_both"
  let op2_only := Wire.mk "op2_only"
  let op2_and_not3 := Wire.mk "op2_n3"
  let op2_and_not34 := Wire.mk "op2_n34"
  let op3_and_not24 := Wire.mk "op3_n24"

  let cat_decode_gates := [
    Gate.mkAND not_op1 not_op2 op_hi_zero_01,
    Gate.mkAND not_op3 not_op4 op_hi_zero_23,
    Gate.mkAND op_hi_zero_01 op_hi_zero_23 op_is_add_sub,

    Gate.mkAND (op[1]!) not_op0 op1_only,
    Gate.mkAND op1_only not_op2 (Wire.mk "mul_t0"),
    Gate.mkAND (Wire.mk "mul_t0") op_hi_zero_23 op_is_mul,

    Gate.mkAND (op[0]!) (op[1]!) op01_both,
    Gate.mkAND op01_both not_op2 (Wire.mk "div_t0"),
    Gate.mkAND (Wire.mk "div_t0") op_hi_zero_23 op_is_div,

    Gate.mkAND (op[2]!) not_op0 op2_only,
    Gate.mkAND op2_only not_op1 (Wire.mk "sqrt_t0"),
    Gate.mkAND (Wire.mk "sqrt_t0") op_hi_zero_23 op_is_sqrt,

    Gate.mkOR (op[0]!) (op[1]!) (Wire.mk "op01_any"),
    Gate.mkAND (op[2]!) (Wire.mk "op01_any") op2_and_not3,
    Gate.mkAND op2_and_not3 not_op3 (Wire.mk "op2_n3_real"),
    Gate.mkAND (Wire.mk "op2_n3_real") not_op4 op2_and_not34,
    Gate.mkAND (op[3]!) not_op2 (Wire.mk "fma8_t0"),
    Gate.mkAND (Wire.mk "fma8_t0") not_op1 (Wire.mk "fma8_t1"),
    Gate.mkAND (Wire.mk "fma8_t1") not_op0 (Wire.mk "fma8_t2"),
    Gate.mkAND (Wire.mk "fma8_t2") not_op4 op3_and_not24,
    Gate.mkOR op2_and_not34 op3_and_not24 op_is_fma,

    Gate.mkOR op_is_add_sub op_is_mul (Wire.mk "misc_t0"),
    Gate.mkOR op_is_div op_is_sqrt (Wire.mk "misc_t1"),
    Gate.mkOR (Wire.mk "misc_t0") (Wire.mk "misc_t1") (Wire.mk "misc_t2"),
    Gate.mkOR (Wire.mk "misc_t2") op_is_fma (Wire.mk "misc_t3"),
    Gate.mkNOT (Wire.mk "misc_t3") op_is_misc
  ]

  -- FMA sub/neg decoding
  let fma_subtract_addend := Wire.mk "fma_sub_addend"
  let fma_negate_product := Wire.mk "fma_neg_product"
  let fma_ctrl_gates := [
    Gate.mkAND op2_and_not34 (op[1]!) fma_subtract_addend,
    Gate.mkAND (op[1]!) (op[0]!) (Wire.mk "fma_neg_57"),
    Gate.mkAND op2_and_not34 (Wire.mk "fma_neg_57") (Wire.mk "fma_neg_a"),
    Gate.mkOR (Wire.mk "fma_neg_a") op3_and_not24 fma_negate_product
  ]

  -- Gated valids to sub-units
  let add_valid_sp := Wire.mk "add_v_sp"
  let add_valid_dp := Wire.mk "add_v_dp"
  let mul_valid_sp := Wire.mk "mul_v_sp"
  let mul_valid_dp := Wire.mk "mul_v_dp"
  let fma_valid_sp := Wire.mk "fma_v_sp"
  let fma_valid_dp := Wire.mk "fma_v_dp"
  let div_start_sp := Wire.mk "div_st_sp"
  let div_start_dp := Wire.mk "div_st_dp"
  let sqrt_start_sp := Wire.mk "sqrt_st_sp"
  let sqrt_start_dp := Wire.mk "sqrt_st_dp"
  let misc_valid_sp := Wire.mk "misc_v_sp"
  let misc_valid_dp := Wire.mk "misc_v_dp"

  let valid_gates := [
    Gate.mkAND valid_in op_is_add_sub (Wire.mk "v_add"),
    Gate.mkAND (Wire.mk "v_add") is_sp add_valid_sp,
    Gate.mkAND (Wire.mk "v_add") is_dp add_valid_dp,

    Gate.mkAND valid_in op_is_mul (Wire.mk "v_mul"),
    Gate.mkAND (Wire.mk "v_mul") is_sp mul_valid_sp,
    Gate.mkAND (Wire.mk "v_mul") is_dp mul_valid_dp,

    Gate.mkAND valid_in op_is_fma (Wire.mk "v_fma"),
    Gate.mkAND (Wire.mk "v_fma") is_sp fma_valid_sp,
    Gate.mkAND (Wire.mk "v_fma") is_dp fma_valid_dp,

    Gate.mkAND valid_in op_is_div (Wire.mk "v_div"),
    Gate.mkAND (Wire.mk "v_div") is_sp div_start_sp,
    Gate.mkAND (Wire.mk "v_div") is_dp div_start_dp,

    Gate.mkAND valid_in op_is_sqrt (Wire.mk "v_sqrt"),
    Gate.mkAND (Wire.mk "v_sqrt") is_sp sqrt_start_sp,
    Gate.mkAND (Wire.mk "v_sqrt") is_dp sqrt_start_dp,

    Gate.mkAND valid_in op_is_misc (Wire.mk "v_misc"),
    Gate.mkAND (Wire.mk "v_misc") is_sp misc_valid_sp,
    Gate.mkAND (Wire.mk "v_misc") is_dp misc_valid_dp
  ]

  -- ══════════════════════════════════════════════
  -- SP Operand Unboxing
  -- Check if upper 32 bits are all 1s. If not, unbox as canonical SP NaN (0x7FC00000).
  -- Exception: int-reading ops (FCVT.S.W=14, FCVT.S.WU=15, FMV.W.X=17) read raw src1[31:0].
  -- ══════════════════════════════════════════════
  let (s1_hi_ones, s1_hi_ones_gates) := (List.range 32).foldl
    (fun (acc : Wire × List Gate) i =>
      if i == 0 then (src1[32]!, [])
      else
        let out := Wire.mk s!"s1_hi_and_{i}"
        (out, acc.2 ++ [Gate.mkAND acc.1 (src1[32 + i]!) out])
    ) (zero, [])

  let (s2_hi_ones, s2_hi_ones_gates) := (List.range 32).foldl
    (fun (acc : Wire × List Gate) i =>
      if i == 0 then (src2[32]!, [])
      else
        let out := Wire.mk s!"s2_hi_and_{i}"
        (out, acc.2 ++ [Gate.mkAND acc.1 (src2[32 + i]!) out])
    ) (zero, [])

  let (s3_hi_ones, s3_hi_ones_gates) := (List.range 32).foldl
    (fun (acc : Wire × List Gate) i =>
      if i == 0 then (src3[32]!, [])
      else
        let out := Wire.mk s!"s3_hi_and_{i}"
        (out, acc.2 ++ [Gate.mkAND acc.1 (src3[32 + i]!) out])
    ) (zero, [])

  -- Detect SP ops where src1 bypasses NaN-unboxing:
  -- FCVT.S.W(14), FCVT.S.WU(15), FMV.X.W(16), FMV.W.X(17)
  -- 14=01110, 15=01111, 16=10000, 17=10001. All have is_sp.
  let op_s1_is_int := Wire.mk "op_s1_is_int"
  let s1_int_gates := [
    Gate.mkAND (op[3]!) (op[2]!) (Wire.mk "s1_int_32"),
    Gate.mkAND (Wire.mk "s1_int_32") (op[1]!) (Wire.mk "s1_int_1415"),
    Gate.mkAND not_op4 (Wire.mk "s1_int_1415") (Wire.mk "s1_int_grp1415"),
    Gate.mkAND (op[4]!) not_op3 (Wire.mk "s1_int_17_t0"),
    Gate.mkAND not_op2 not_op1 (Wire.mk "s1_int_17_t1"),
    Gate.mkAND (Wire.mk "s1_int_17_t0") (Wire.mk "s1_int_17_t1") (Wire.mk "s1_int_16_17"),
    Gate.mkOR (Wire.mk "s1_int_grp1415") (Wire.mk "s1_int_16_17") op_s1_is_int
  ]

  let s1_bypass_box := Wire.mk "s1_byp_box"
  let s1_byp_gate := Gate.mkOR s1_hi_ones op_s1_is_int s1_bypass_box

  let src1_sp := makeIndexedWires "src1_sp" 32
  let src2_sp := makeIndexedWires "src2_sp" 32
  let src3_sp := makeIndexedWires "src3_sp" 32
  let unbox_gates := (List.range 32).flatMap fun i =>
    let canon_bit := if i >= 22 && i <= 30 then one else zero
    [Gate.mkMUX canon_bit (src1[i]!) s1_bypass_box (src1_sp[i]!),
     Gate.mkMUX canon_bit (src2[i]!) s2_hi_ones (src2_sp[i]!),
     Gate.mkMUX canon_bit (src3[i]!) s3_hi_ones (src3_sp[i]!)]

  -- ══════════════════════════════════════════════
  -- SP Sub-Units
  -- ══════════════════════════════════════════════
  let misc_sp_res := makeIndexedWires "misc_sp_res" 32
  let misc_sp_exc := makeIndexedWires "misc_sp_exc" 5
  let misc_sp_inst : CircuitInstance := {
    moduleName := "FPMisc", instName := "u_misc_sp",
    portMap :=
      (List.range 32 |>.flatMap fun i => [ (s!"src1_{i}", src1_sp[i]!), (s!"src2_{i}", src2_sp[i]!) ]) ++
      (List.range 5 |>.map fun i => (s!"op_{i}", op[i]!)) ++
      (List.range 3 |>.map fun i => (s!"rm_{i}", rm[i]!)) ++
      [ ("zero", zero), ("one", one) ] ++
      (List.range 32 |>.map fun i => (s!"result_{i}", misc_sp_res[i]!)) ++
      (List.range 5 |>.map fun i => (s!"exc_{i}", misc_sp_exc[i]!))
  }

  let add_sp_res := makeIndexedWires "add_sp_res" 32
  let add_sp_tag := makeIndexedWires "add_sp_tag" 6
  let add_sp_exc := makeIndexedWires "add_sp_exc" 5
  let add_sp_valid := Wire.mk "add_sp_valid"
  let adder_sp_inst : CircuitInstance := {
    moduleName := "FPAdder", instName := "u_adder_sp",
    portMap :=
      (List.range 32 |>.flatMap fun i => [ (s!"src1_{i}", src1_sp[i]!), (s!"src2_{i}", src2_sp[i]!) ]) ++
      [ ("op_sub", op[0]!) ] ++
      (List.range 3 |>.map fun i => (s!"rm_{i}", rm[i]!)) ++
      (List.range 6 |>.map fun i => (s!"dest_tag_{i}", dest_tag[i]!)) ++
      [ ("valid_in", add_valid_sp), ("clock", clock), ("reset", reset_add_sp), ("zero", zero) ] ++
      (List.range 32 |>.map fun i => (s!"result_{i}", add_sp_res[i]!)) ++
      (List.range 6 |>.map fun i => (s!"tag_out_{i}", add_sp_tag[i]!)) ++
      (List.range 5 |>.map fun i => (s!"exc_{i}", add_sp_exc[i]!)) ++
      [ ("valid_out", add_sp_valid) ]
  }

  let mul_sp_res := makeIndexedWires "mul_sp_res" 32
  let mul_sp_tag := makeIndexedWires "mul_sp_tag" 6
  let mul_sp_exc := makeIndexedWires "mul_sp_exc" 5
  let mul_sp_valid := Wire.mk "mul_sp_valid"
  let mul_sp_inst : CircuitInstance := {
    moduleName := "FPMultiplier", instName := "u_mul_sp",
    portMap :=
      (List.range 32 |>.flatMap fun i => [ (s!"src1_{i}", src1_sp[i]!), (s!"src2_{i}", src2_sp[i]!) ]) ++
      (List.range 3 |>.map fun i => (s!"rm_{i}", rm[i]!)) ++
      (List.range 6 |>.map fun i => (s!"dest_tag_{i}", dest_tag[i]!)) ++
      [ ("valid_in", mul_valid_sp), ("clock", clock), ("reset", reset_mul_sp), ("zero", zero) ] ++
      (List.range 32 |>.map fun i => (s!"result_{i}", mul_sp_res[i]!)) ++
      (List.range 6 |>.map fun i => (s!"tag_out_{i}", mul_sp_tag[i]!)) ++
      (List.range 5 |>.map fun i => (s!"exc_{i}", mul_sp_exc[i]!)) ++
      [ ("valid_out", mul_sp_valid) ]
  }

  let fma_sp_res := makeIndexedWires "fma_sp_res" 32
  let fma_sp_tag := makeIndexedWires "fma_sp_tag" 6
  let fma_sp_exc := makeIndexedWires "fma_sp_exc" 5
  let fma_sp_valid := Wire.mk "fma_sp_valid"
  let fma_sp_inst : CircuitInstance := {
    moduleName := "FPFMA", instName := "u_fma_sp",
    portMap :=
      (List.range 32 |>.flatMap fun i => [ (s!"src1_{i}", src1_sp[i]!), (s!"src2_{i}", src2_sp[i]!), (s!"src3_{i}", src3_sp[i]!) ]) ++
      (List.range 3 |>.map fun i => (s!"rm_{i}", rm[i]!)) ++
      (List.range 6 |>.map fun i => (s!"dest_tag_{i}", dest_tag[i]!)) ++
      [ ("negate_product", fma_negate_product), ("subtract_addend", fma_subtract_addend),
        ("valid_in", fma_valid_sp), ("clock", clock), ("reset", reset_fma_sp), ("zero", zero) ] ++
      (List.range 32 |>.map fun i => (s!"result_{i}", fma_sp_res[i]!)) ++
      (List.range 6 |>.map fun i => (s!"tag_out_{i}", fma_sp_tag[i]!)) ++
      (List.range 5 |>.map fun i => (s!"exc_{i}", fma_sp_exc[i]!)) ++
      [ ("valid_out", fma_sp_valid) ]
  }

  let div_sp_res := makeIndexedWires "div_sp_res" 32
  let div_sp_tag := makeIndexedWires "div_sp_tag" 6
  let div_sp_exc := makeIndexedWires "div_sp_exc" 5
  let div_sp_valid := Wire.mk "div_sp_valid"
  let div_sp_busy := Wire.mk "div_sp_busy"
  let div_sp_inst : CircuitInstance := {
    moduleName := "FPDivider", instName := "u_div_sp",
    portMap :=
      (List.range 32 |>.flatMap fun i => [ (s!"src1_{i}", src1_sp[i]!), (s!"src2_{i}", src2_sp[i]!) ]) ++
      (List.range 3 |>.map fun i => (s!"rm_{i}", rm[i]!)) ++
      (List.range 6 |>.map fun i => (s!"dest_tag_{i}", dest_tag[i]!)) ++
      [ ("start", div_start_sp), ("clock", clock), ("reset", reset_div_sp), ("zero", zero), ("one", one) ] ++
      (List.range 32 |>.map fun i => (s!"result_{i}", div_sp_res[i]!)) ++
      (List.range 6 |>.map fun i => (s!"tag_out_{i}", div_sp_tag[i]!)) ++
      (List.range 5 |>.map fun i => (s!"exc_{i}", div_sp_exc[i]!)) ++
      [ ("valid_out", div_sp_valid), ("busy", div_sp_busy) ]
  }

  let sqrt_sp_res := makeIndexedWires "sqrt_sp_res" 32
  let sqrt_sp_tag := makeIndexedWires "sqrt_sp_tag" 6
  let sqrt_sp_exc := makeIndexedWires "sqrt_sp_exc" 5
  let sqrt_sp_valid := Wire.mk "sqrt_sp_valid"
  let sqrt_sp_busy := Wire.mk "sqrt_sp_busy"
  let sqrt_sp_inst : CircuitInstance := {
    moduleName := "FPSqrt", instName := "u_sqrt_sp",
    portMap :=
      (List.range 32 |>.map fun i => (s!"src1_{i}", src1_sp[i]!)) ++
      (List.range 3 |>.map fun i => (s!"rm_{i}", rm[i]!)) ++
      (List.range 6 |>.map fun i => (s!"dest_tag_{i}", dest_tag[i]!)) ++
      [ ("start", sqrt_start_sp), ("clock", clock), ("reset", reset_sqrt_sp), ("zero", zero), ("one", one) ] ++
      (List.range 32 |>.map fun i => (s!"result_{i}", sqrt_sp_res[i]!)) ++
      (List.range 6 |>.map fun i => (s!"tag_out_{i}", sqrt_sp_tag[i]!)) ++
      (List.range 5 |>.map fun i => (s!"exc_{i}", sqrt_sp_exc[i]!)) ++
      [ ("valid_out", sqrt_sp_valid), ("busy", sqrt_sp_busy) ]
  }

  -- ══════════════════════════════════════════════
  -- DP Sub-Units
  -- ══════════════════════════════════════════════
  let misc_dp_res := makeIndexedWires "misc_dp_res" 64
  let misc_dp_exc := makeIndexedWires "misc_dp_exc" 5
  let misc_dp_rint := Wire.mk "misc_dp_rint"
  let misc_dp_inst : CircuitInstance := {
    moduleName := "FPDoubleMisc", instName := "u_misc_dp",
    portMap :=
      (List.range 64 |>.flatMap fun i => [ (s!"src1_{i}", src1[i]!), (s!"src2_{i}", src2[i]!) ]) ++
      (List.range 6 |>.map fun i => (s!"op_{i}", op[i]!)) ++
      (List.range 3 |>.map fun i => (s!"rm_{i}", rm[i]!)) ++
      [ ("zero", zero), ("one", one) ] ++
      (List.range 64 |>.map fun i => (s!"result_{i}", misc_dp_res[i]!)) ++
      (List.range 5 |>.map fun i => (s!"exc_{i}", misc_dp_exc[i]!)) ++
      [ ("result_is_int", misc_dp_rint) ]
  }

  let conv_dp_res := makeIndexedWires "conv_dp_res" 64
  let conv_dp_exc := makeIndexedWires "conv_dp_exc" 5
  let conv_dp_rint := Wire.mk "conv_dp_rint"
  let conv_dp_inst : CircuitInstance := {
    moduleName := "FPDoubleConverter", instName := "u_conv_dp",
    portMap :=
      (List.range 64 |>.map fun i => (s!"src1_{i}", src1[i]!)) ++
      (List.range 6 |>.map fun i => (s!"op_{i}", op[i]!)) ++
      (List.range 3 |>.map fun i => (s!"rm_{i}", rm[i]!)) ++
      [ ("zero", zero), ("one", one) ] ++
      (List.range 64 |>.map fun i => (s!"result_{i}", conv_dp_res[i]!)) ++
      (List.range 5 |>.map fun i => (s!"exc_{i}", conv_dp_exc[i]!)) ++
      [ ("result_is_int", conv_dp_rint) ]
  }
  -- 64-bit integer / FP conversions (FPLongConverter)
  -- SP: FCVT.L.S (24), FCVT.LU.S (25), FCVT.S.L (26), FCVT.S.LU (27)
  -- DP: FCVT.L.D (58), FCVT.LU.D (59), FCVT.D.L (60), FCVT.D.LU (61)
  let long_op := makeIndexedWires "long_op" 3
  let long_op_gates := [
    Gate.mkBUF (op[0]!) (long_op[0]!),
    Gate.mkMUX (op[1]!) (op[2]!) (op[5]!) (long_op[1]!),
    Gate.mkBUF (op[5]!) (long_op[2]!)
  ]

  let is_long_sp := Wire.mk "is_long_sp"
  let is_long_dp := Wire.mk "is_long_dp"
  let is_long_conv := Wire.mk "is_long_conv"
  let op1_or_op2 := Wire.mk "op1_or_op2"
  let long_conv_dec_gates := [
    Gate.mkAND (op[4]!) (op[3]!) (Wire.mk "long_op43"),
    Gate.mkAND (Wire.mk "long_op43") not_op2 (Wire.mk "long_op43_n2"),
    Gate.mkAND not_op5 (Wire.mk "long_op43_n2") is_long_sp,

    Gate.mkOR (op[1]!) (op[2]!) op1_or_op2,
    Gate.mkAND (Wire.mk "long_op43") op1_or_op2 (Wire.mk "long_dp_t0"),
    Gate.mkAND (op[5]!) (Wire.mk "long_dp_t0") is_long_dp,

    Gate.mkOR is_long_sp is_long_dp is_long_conv
  ]

  let not_long_op1 := Wire.mk "not_long_op1"
  let sp_f2i_active := Wire.mk "sp_f2i_active"
  let sp_f2i_gates := [
    Gate.mkNOT (long_op[1]!) not_long_op1,
    Gate.mkAND is_long_sp not_long_op1 sp_f2i_active
  ]
  let long_src1 := (List.range 64).map fun i =>
    if i < 32 then Wire.mk s!"long_s1_{i}" else src1[i]!
  let long_src1_gates := sp_f2i_gates ++ (List.range 32).map fun i =>
    Gate.mkMUX (src1[i]!) (src1_sp[i]!) sp_f2i_active (long_src1[i]!)

  let conv_long_res := makeIndexedWires "conv_long_res" 64
  let conv_long_exc := makeIndexedWires "conv_long_exc" 5
  let conv_long_rint := Wire.mk "conv_long_rint"
  let conv_long_inst : CircuitInstance := {
    moduleName := "FPLongConverter", instName := "u_conv_long",
    portMap :=
      (List.range 64 |>.map fun i => (s!"src1_{i}", long_src1[i]!)) ++
      (List.range 3 |>.map fun i => (s!"op_{i}", long_op[i]!)) ++
      (List.range 3 |>.map fun i => (s!"rm_{i}", rm[i]!)) ++
      [ ("zero", zero), ("one", one) ] ++
      (List.range 64 |>.map fun i => (s!"result_{i}", conv_long_res[i]!)) ++
      (List.range 5 |>.map fun i => (s!"exc_{i}", conv_long_exc[i]!)) ++
      [ ("result_is_int", conv_long_rint) ]
  }


  let add_dp_res := makeIndexedWires "add_dp_res" 64
  let add_dp_tag := makeIndexedWires "add_dp_tag" 6
  let add_dp_exc := makeIndexedWires "add_dp_exc" 5
  let add_dp_valid := Wire.mk "add_dp_valid"
  let adder_dp_inst : CircuitInstance := {
    moduleName := "FPAdderD", instName := "u_adder_dp",
    portMap :=
      (List.range 64 |>.flatMap fun i => [ (s!"src1_{i}", src1[i]!), (s!"src2_{i}", src2[i]!) ]) ++
      [ ("op_sub", op[0]!) ] ++
      (List.range 3 |>.map fun i => (s!"rm_{i}", rm[i]!)) ++
      (List.range 6 |>.map fun i => (s!"dest_tag_{i}", dest_tag[i]!)) ++
      [ ("valid_in", add_valid_dp), ("clock", clock), ("reset", reset_add_dp), ("zero", zero) ] ++
      (List.range 64 |>.map fun i => (s!"result_{i}", add_dp_res[i]!)) ++
      (List.range 6 |>.map fun i => (s!"tag_out_{i}", add_dp_tag[i]!)) ++
      (List.range 5 |>.map fun i => (s!"exc_{i}", add_dp_exc[i]!)) ++
      [ ("valid_out", add_dp_valid) ]
  }

  let mul_dp_res := makeIndexedWires "mul_dp_res" 64
  let mul_dp_tag := makeIndexedWires "mul_dp_tag" 6
  let mul_dp_exc := makeIndexedWires "mul_dp_exc" 5
  let mul_dp_valid := Wire.mk "mul_dp_valid"
  let mul_dp_inst : CircuitInstance := {
    moduleName := "FPMultiplierD", instName := "u_mul_dp",
    portMap :=
      (List.range 64 |>.flatMap fun i => [ (s!"src1_{i}", src1[i]!), (s!"src2_{i}", src2[i]!) ]) ++
      (List.range 3 |>.map fun i => (s!"rm_{i}", rm[i]!)) ++
      (List.range 6 |>.map fun i => (s!"dest_tag_{i}", dest_tag[i]!)) ++
      [ ("valid_in", mul_valid_dp), ("clock", clock), ("reset", reset_mul_dp), ("zero", zero) ] ++
      (List.range 64 |>.map fun i => (s!"result_{i}", mul_dp_res[i]!)) ++
      (List.range 6 |>.map fun i => (s!"tag_out_{i}", mul_dp_tag[i]!)) ++
      (List.range 5 |>.map fun i => (s!"exc_{i}", mul_dp_exc[i]!)) ++
      [ ("valid_out", mul_dp_valid) ]
  }

  let fma_dp_res := makeIndexedWires "fma_dp_res" 64
  let fma_dp_tag := makeIndexedWires "fma_dp_tag" 6
  let fma_dp_exc := makeIndexedWires "fma_dp_exc" 5
  let fma_dp_valid := Wire.mk "fma_dp_valid"
  let fma_dp_inst : CircuitInstance := {
    moduleName := "FPFMAD", instName := "u_fma_dp",
    portMap :=
      (List.range 64 |>.flatMap fun i => [ (s!"src1_{i}", src1[i]!), (s!"src2_{i}", src2[i]!), (s!"src3_{i}", src3[i]!) ]) ++
      (List.range 3 |>.map fun i => (s!"rm_{i}", rm[i]!)) ++
      (List.range 6 |>.map fun i => (s!"dest_tag_{i}", dest_tag[i]!)) ++
      [ ("negate_product", fma_negate_product), ("subtract_addend", fma_subtract_addend),
        ("valid_in", fma_valid_dp), ("clock", clock), ("reset", reset_fma_dp), ("zero", zero) ] ++
      (List.range 64 |>.map fun i => (s!"result_{i}", fma_dp_res[i]!)) ++
      (List.range 6 |>.map fun i => (s!"tag_out_{i}", fma_dp_tag[i]!)) ++
      (List.range 5 |>.map fun i => (s!"exc_{i}", fma_dp_exc[i]!)) ++
      [ ("valid_out", fma_dp_valid) ]
  }

  let div_dp_res := makeIndexedWires "div_dp_res" 64
  let div_dp_tag := makeIndexedWires "div_dp_tag" 6
  let div_dp_exc := makeIndexedWires "div_dp_exc" 5
  let div_dp_valid := Wire.mk "div_dp_valid"
  let div_dp_busy := Wire.mk "div_dp_busy"
  let div_dp_inst : CircuitInstance := {
    moduleName := "FPDividerD", instName := "u_div_dp",
    portMap :=
      (List.range 64 |>.flatMap fun i => [ (s!"src1_{i}", src1[i]!), (s!"src2_{i}", src2[i]!) ]) ++
      (List.range 3 |>.map fun i => (s!"rm_{i}", rm[i]!)) ++
      (List.range 6 |>.map fun i => (s!"dest_tag_{i}", dest_tag[i]!)) ++
      [ ("start", div_start_dp), ("clock", clock), ("reset", reset_div_dp), ("zero", zero), ("one", one) ] ++
      (List.range 64 |>.map fun i => (s!"result_{i}", div_dp_res[i]!)) ++
      (List.range 6 |>.map fun i => (s!"tag_out_{i}", div_dp_tag[i]!)) ++
      (List.range 5 |>.map fun i => (s!"exc_{i}", div_dp_exc[i]!)) ++
      [ ("valid_out", div_dp_valid), ("busy", div_dp_busy) ]
  }

  let sqrt_dp_res := makeIndexedWires "sqrt_dp_res" 64
  let sqrt_dp_tag := makeIndexedWires "sqrt_dp_tag" 6
  let sqrt_dp_exc := makeIndexedWires "sqrt_dp_exc" 5
  let sqrt_dp_valid := Wire.mk "sqrt_dp_valid"
  let sqrt_dp_busy := Wire.mk "sqrt_dp_busy"
  let sqrt_dp_inst : CircuitInstance := {
    moduleName := "FPSqrtD", instName := "u_sqrt_dp",
    portMap :=
      (List.range 64 |>.map fun i => (s!"src1_{i}", src1[i]!)) ++
      (List.range 3 |>.map fun i => (s!"rm_{i}", rm[i]!)) ++
      (List.range 6 |>.map fun i => (s!"dest_tag_{i}", dest_tag[i]!)) ++
      [ ("start", sqrt_start_dp), ("clock", clock), ("reset", reset_sqrt_dp), ("zero", zero), ("one", one) ] ++
      (List.range 64 |>.map fun i => (s!"result_{i}", sqrt_dp_res[i]!)) ++
      (List.range 6 |>.map fun i => (s!"tag_out_{i}", sqrt_dp_tag[i]!)) ++
      (List.range 5 |>.map fun i => (s!"exc_{i}", sqrt_dp_exc[i]!)) ++
      [ ("valid_out", sqrt_dp_valid), ("busy", sqrt_dp_busy) ]
  }

  -- ══════════════════════════════════════════════
  -- Merged Outputs (SP NaN-boxed with DP results)
  -- ══════════════════════════════════════════════
  -- 1. Adder
  let add_result := makeIndexedWires "add_res" 64
  let add_tag := makeIndexedWires "add_tag" 6
  let add_exc := makeIndexedWires "add_exc" 5
  let add_valid := Wire.mk "add_valid"
  let add_merge_gates :=
    (List.range 64 |>.map fun i =>
      let sp_boxed := if i >= 32 then one else add_sp_res[i]!
      Gate.mkMUX sp_boxed (add_dp_res[i]!) add_dp_valid (add_result[i]!)) ++
    (List.range 6 |>.map fun i =>
      Gate.mkMUX (add_sp_tag[i]!) (add_dp_tag[i]!) add_dp_valid (add_tag[i]!)) ++
    (List.range 5 |>.map fun i =>
      Gate.mkMUX (add_sp_exc[i]!) (add_dp_exc[i]!) add_dp_valid (add_exc[i]!)) ++
    [Gate.mkOR add_sp_valid add_dp_valid add_valid]

  -- 2. Multiplier
  let mul_result := makeIndexedWires "mul_res" 64
  let mul_tag := makeIndexedWires "mul_tag" 6
  let mul_exc := makeIndexedWires "mul_exc" 5
  let mul_valid := Wire.mk "mul_valid"
  let mul_merge_gates :=
    (List.range 64 |>.map fun i =>
      let sp_boxed := if i >= 32 then one else mul_sp_res[i]!
      Gate.mkMUX sp_boxed (mul_dp_res[i]!) mul_dp_valid (mul_result[i]!)) ++
    (List.range 6 |>.map fun i =>
      Gate.mkMUX (mul_sp_tag[i]!) (mul_dp_tag[i]!) mul_dp_valid (mul_tag[i]!)) ++
    (List.range 5 |>.map fun i =>
      Gate.mkMUX (mul_sp_exc[i]!) (mul_dp_exc[i]!) mul_dp_valid (mul_exc[i]!)) ++
    [Gate.mkOR mul_sp_valid mul_dp_valid mul_valid]

  -- 3. FMA
  let fma_result := makeIndexedWires "fma_res" 64
  let fma_tag := makeIndexedWires "fma_tag" 6
  let fma_exc := makeIndexedWires "fma_exc" 5
  let fma_valid := Wire.mk "fma_valid"
  let fma_merge_gates :=
    (List.range 64 |>.map fun i =>
      let sp_boxed := if i >= 32 then one else fma_sp_res[i]!
      Gate.mkMUX sp_boxed (fma_dp_res[i]!) fma_dp_valid (fma_result[i]!)) ++
    (List.range 6 |>.map fun i =>
      Gate.mkMUX (fma_sp_tag[i]!) (fma_dp_tag[i]!) fma_dp_valid (fma_tag[i]!)) ++
    (List.range 5 |>.map fun i =>
      Gate.mkMUX (fma_sp_exc[i]!) (fma_dp_exc[i]!) fma_dp_valid (fma_exc[i]!)) ++
    [Gate.mkOR fma_sp_valid fma_dp_valid fma_valid]

  -- 4. Divider
  let div_result := makeIndexedWires "div_res" 64
  let div_tag := makeIndexedWires "div_tag" 6
  let div_exc := makeIndexedWires "div_exc" 5
  let div_valid := Wire.mk "div_valid"
  let div_merge_gates :=
    (List.range 64 |>.map fun i =>
      let sp_boxed := if i >= 32 then one else div_sp_res[i]!
      Gate.mkMUX sp_boxed (div_dp_res[i]!) div_dp_valid (div_result[i]!)) ++
    (List.range 6 |>.map fun i =>
      Gate.mkMUX (div_sp_tag[i]!) (div_dp_tag[i]!) div_dp_valid (div_tag[i]!)) ++
    (List.range 5 |>.map fun i =>
      Gate.mkMUX (div_sp_exc[i]!) (div_dp_exc[i]!) div_dp_valid (div_exc[i]!)) ++
    [Gate.mkOR div_sp_valid div_dp_valid div_valid]

  -- 5. Sqrt
  let sqrt_result := makeIndexedWires "sqrt_res" 64
  let sqrt_tag := makeIndexedWires "sqrt_tag" 6
  let sqrt_exc := makeIndexedWires "sqrt_exc" 5
  let sqrt_valid := Wire.mk "sqrt_valid"
  let sqrt_merge_gates :=
    (List.range 64 |>.map fun i =>
      let sp_boxed := if i >= 32 then one else sqrt_sp_res[i]!
      Gate.mkMUX sp_boxed (sqrt_dp_res[i]!) sqrt_dp_valid (sqrt_result[i]!)) ++
    (List.range 6 |>.map fun i =>
      Gate.mkMUX (sqrt_sp_tag[i]!) (sqrt_dp_tag[i]!) sqrt_dp_valid (sqrt_tag[i]!)) ++
    (List.range 5 |>.map fun i =>
      Gate.mkMUX (sqrt_sp_exc[i]!) (sqrt_dp_exc[i]!) sqrt_dp_valid (sqrt_exc[i]!)) ++
    [Gate.mkOR sqrt_sp_valid sqrt_dp_valid sqrt_valid]

  -- 6. Misc & Converter
  -- Detect if op is a DP converter op (44..49) or a DP move (56/57)
  let is_dp_conv := Wire.mk "is_dp_conv"
  let is_dp_conv_gates := [
    Gate.mkAND (op[3]!) (op[2]!) (Wire.mk "dpc_4447"),
    Gate.mkAND not_op4 (Wire.mk "dpc_4447") (Wire.mk "dpc_g4447"),
    Gate.mkAND (op[4]!) not_op3 (Wire.mk "dpc_4849_t0"),
    Gate.mkAND not_op2 not_op1 (Wire.mk "dpc_4849_t1"),
    Gate.mkAND (Wire.mk "dpc_4849_t0") (Wire.mk "dpc_4849_t1") (Wire.mk "dpc_g4849"),
    -- FMV.X.D (56) / FMV.D.X (57): the converter passes the raw 64-bit operand
    Gate.mkAND (op[5]!) (op[4]!) (Wire.mk "dpc_fmv_t0"),
    Gate.mkAND (Wire.mk "dpc_fmv_t0") (op[3]!) (Wire.mk "dpc_fmv_t1"),
    Gate.mkAND (Wire.mk "dpc_fmv_t1") not_op2 (Wire.mk "dpc_fmv_t2"),
    Gate.mkAND (Wire.mk "dpc_fmv_t2") not_op1 (Wire.mk "dpc_g5657"),
    Gate.mkOR (Wire.mk "dpc_g4447") (Wire.mk "dpc_g4849") (Wire.mk "dpc_any0"),
    Gate.mkOR (Wire.mk "dpc_any0") (Wire.mk "dpc_g5657") (Wire.mk "dpc_any"),
    Gate.mkAND is_dp (Wire.mk "dpc_any") is_dp_conv
  ]

  -- SP ops that write an integer register (FMV.X.W, FCVT.W.S/WU.S, FCLASS.S,
  -- FEQ/FLT/FLE.S). Their 32-bit result must be sign-extended to XLEN; every
  -- other SP result is NaN-boxed into the 64-bit FP register.
  let sp_writes_int := Wire.mk "sp_writes_int"
  let grp_8_15 := Wire.mk "sp_g8_15"
  let not_both_21 := Wire.mk "sp_not_both_21"
  let any_210 := Wire.mk "sp_any_210"
  let grp_8_15_filt := Wire.mk "sp_g8_15_filt"
  let grp_16_18 := Wire.mk "sp_g16_18"
  let sp_int_detect_gates := [
    Gate.mkAND (op[3]!) not_op4 grp_8_15,
    Gate.mkAND (op[2]!) (op[1]!) (Wire.mk "sp_b21"),
    Gate.mkNOT (Wire.mk "sp_b21") not_both_21,
    Gate.mkOR (op[0]!) (op[1]!) (Wire.mk "sp_a01"),
    Gate.mkOR (Wire.mk "sp_a01") (op[2]!) any_210,
    Gate.mkAND grp_8_15 not_both_21 (Wire.mk "sp_gf1"),
    Gate.mkAND (Wire.mk "sp_gf1") any_210 grp_8_15_filt,
    Gate.mkAND (op[4]!) not_op3 (Wire.mk "sp_g16_t1"),
    Gate.mkAND not_op0 not_op2 (Wire.mk "sp_g16_t2"),
    Gate.mkAND (Wire.mk "sp_g16_t1") (Wire.mk "sp_g16_t2") grp_16_18,
    Gate.mkOR grp_8_15_filt grp_16_18 sp_writes_int
  ]

  let misc_res_pre := makeIndexedWires "misc_res_pre" 64
  let misc_exc_pre := makeIndexedWires "misc_exc_pre" 5
  let misc_result := makeIndexedWires "misc_res" 64
  let misc_exc := makeIndexedWires "misc_exc" 5
  let misc_valid := Wire.mk "misc_valid"
  let misc_merge_gates :=
    (List.range 64 |>.flatMap fun i =>
      let dp_sub := Wire.mk s!"m_dpsub_{i}"
      if i >= 32 then
        -- Upper 32 bits: sign-extend an int result, NaN-box an FP result
        let sp_hi := Wire.mk s!"misc_sp_hi_{i}"
        [Gate.mkMUX one (misc_sp_res[31]!) sp_writes_int sp_hi,
         Gate.mkMUX (misc_dp_res[i]!) (conv_dp_res[i]!) is_dp_conv dp_sub,
         Gate.mkMUX sp_hi dp_sub is_dp (misc_res_pre[i]!)]
      else
        [Gate.mkMUX (misc_dp_res[i]!) (conv_dp_res[i]!) is_dp_conv dp_sub,
         Gate.mkMUX (misc_sp_res[i]!) dp_sub is_dp (misc_res_pre[i]!)]) ++
    (List.range 5 |>.flatMap fun i =>
      let dp_sub_exc := Wire.mk s!"m_dpexc_{i}"
      [Gate.mkMUX (misc_dp_exc[i]!) (conv_dp_exc[i]!) is_dp_conv dp_sub_exc,
       Gate.mkMUX (misc_sp_exc[i]!) dp_sub_exc is_dp (misc_exc_pre[i]!)]) ++
    (List.range 64 |>.map fun i =>
      Gate.mkMUX (misc_res_pre[i]!) (conv_long_res[i]!) is_long_conv (misc_result[i]!)) ++
    (List.range 5 |>.map fun i =>
      Gate.mkMUX (misc_exc_pre[i]!) (conv_long_exc[i]!) is_long_conv (misc_exc[i]!)) ++
    [Gate.mkOR misc_valid_sp misc_valid_dp misc_valid]

  -- ══════════════════════════════════════════════
  -- 1-Cycle Pipeline Register for Misc/Converter Path
  -- Decouples RS issue + 64-bit converter from CDB mux
  -- ══════════════════════════════════════════════
  let misc_reg_result := makeIndexedWires "misc_reg_res" 64
  let misc_reg_tag := makeIndexedWires "misc_reg_tag" 6
  let misc_reg_exc := makeIndexedWires "misc_reg_exc" 5
  let misc_reg_valid := Wire.mk "misc_reg_valid"
  let misc_reg_writes_int := Wire.mk "misc_reg_rint"

  let misc_pipe_dffs :=
    (List.range 64 |>.map fun i => Gate.mkDFF (misc_result[i]!) clock reset_misc_dp (misc_reg_result[i]!)) ++
    (List.range 6 |>.map fun i => Gate.mkDFF (dest_tag[i]!) clock reset_misc_dp (misc_reg_tag[i]!)) ++
    (List.range 5 |>.map fun i => Gate.mkDFF (misc_exc[i]!) clock reset_misc_dp (misc_reg_exc[i]!)) ++
    [Gate.mkDFF misc_valid clock reset_misc_dp misc_reg_valid,
     Gate.mkDFF (Wire.mk "active_writes_int") clock reset_misc_dp misc_reg_writes_int]

  -- ══════════════════════════════════════════════
  -- 5-Level Priority Writeback MUX Tree
  -- Level 1: MUX(misc_reg, adder, adder_valid) -> t1
  -- Level 2: MUX(t1, mul, mul_valid) -> t2
  -- Level 3: MUX(t2, fma, fma_valid) -> t3
  -- Level 4: MUX(t3, div, div_valid) -> t4
  -- Level 5: MUX(t4, sqrt, sqrt_valid) -> output
  -- ══════════════════════════════════════════════
  let t1_result := makeIndexedWires "t1_res" 64
  let t1_tag := makeIndexedWires "t1_tag" 6
  let t1_exc := makeIndexedWires "t1_exc" 5
  let t1_valid := Wire.mk "t1_valid"
  let mux1_gates :=
    (List.range 64 |>.map fun i => Gate.mkMUX (misc_reg_result[i]!) (add_result[i]!) add_valid (t1_result[i]!)) ++
    (List.range 6 |>.map fun i => Gate.mkMUX (misc_reg_tag[i]!) (add_tag[i]!) add_valid (t1_tag[i]!)) ++
    (List.range 5 |>.map fun i => Gate.mkMUX (misc_reg_exc[i]!) (add_exc[i]!) add_valid (t1_exc[i]!)) ++
    [Gate.mkOR misc_reg_valid add_valid t1_valid]

  let t2_result := makeIndexedWires "t2_res" 64
  let t2_tag := makeIndexedWires "t2_tag" 6
  let t2_exc := makeIndexedWires "t2_exc" 5
  let t2_valid := Wire.mk "t2_valid"
  let mux2_gates :=
    (List.range 64 |>.map fun i => Gate.mkMUX (t1_result[i]!) (mul_result[i]!) mul_valid (t2_result[i]!)) ++
    (List.range 6 |>.map fun i => Gate.mkMUX (t1_tag[i]!) (mul_tag[i]!) mul_valid (t2_tag[i]!)) ++
    (List.range 5 |>.map fun i => Gate.mkMUX (t1_exc[i]!) (mul_exc[i]!) mul_valid (t2_exc[i]!)) ++
    [Gate.mkOR t1_valid mul_valid t2_valid]

  let t3_result := makeIndexedWires "t3_res" 64
  let t3_tag := makeIndexedWires "t3_tag" 6
  let t3_exc := makeIndexedWires "t3_exc" 5
  let t3_valid := Wire.mk "t3_valid"
  let mux3_gates :=
    (List.range 64 |>.map fun i => Gate.mkMUX (t2_result[i]!) (fma_result[i]!) fma_valid (t3_result[i]!)) ++
    (List.range 6 |>.map fun i => Gate.mkMUX (t2_tag[i]!) (fma_tag[i]!) fma_valid (t3_tag[i]!)) ++
    (List.range 5 |>.map fun i => Gate.mkMUX (t2_exc[i]!) (fma_exc[i]!) fma_valid (t3_exc[i]!)) ++
    [Gate.mkOR t2_valid fma_valid t3_valid]

  let t4_result := makeIndexedWires "t4_res" 64
  let t4_tag := makeIndexedWires "t4_tag" 6
  let t4_exc := makeIndexedWires "t4_exc" 5
  let t4_valid := Wire.mk "t4_valid"
  let mux4_gates :=
    (List.range 64 |>.map fun i => Gate.mkMUX (t3_result[i]!) (div_result[i]!) div_valid (t4_result[i]!)) ++
    (List.range 6 |>.map fun i => Gate.mkMUX (t3_tag[i]!) (div_tag[i]!) div_valid (t4_tag[i]!)) ++
    (List.range 5 |>.map fun i => Gate.mkMUX (t3_exc[i]!) (div_exc[i]!) div_valid (t4_exc[i]!)) ++
    [Gate.mkOR t3_valid div_valid t4_valid]

  let mux5_gates :=
    (List.range 64 |>.map fun i => Gate.mkMUX (t4_result[i]!) (sqrt_result[i]!) sqrt_valid (result[i]!)) ++
    (List.range 6 |>.map fun i => Gate.mkMUX (t4_tag[i]!) (sqrt_tag[i]!) sqrt_valid (tag_out[i]!)) ++
    (List.range 5 |>.map fun i => Gate.mkMUX (t4_exc[i]!) (sqrt_exc[i]!) sqrt_valid (exceptions[i]!)) ++
    [Gate.mkOR t4_valid sqrt_valid valid_out]

  -- ══════════════════════════════════════════════
  -- Collision Prevention & Busy
  -- ══════════════════════════════════════════════
  let pipe_dispatched := Wire.mk "pipe_dispatched_d"
  let pipe_active_d1 := Wire.mk "pipe_active_d1_d"
  let pipe_active_d2 := Wire.mk "pipe_active_d2_d"
  let pipe_collision_gates := [
    Gate.mkOR (Wire.mk "v_add") (Wire.mk "v_mul") (Wire.mk "pipe_am_d"),
    Gate.mkOR (Wire.mk "pipe_am_d") (Wire.mk "v_fma") pipe_dispatched
  ]
  let pipe_collision_inst1 : CircuitInstance := {
    moduleName := "DFlipFlop", instName := "u_pipe_d_reg1",
    portMap := [("d", pipe_dispatched), ("q", pipe_active_d1), ("clock", clock), ("reset", reset_misc_dp)]
  }
  let pipe_collision_inst2 : CircuitInstance := {
    moduleName := "DFlipFlop", instName := "u_pipe_d_reg2",
    portMap := [("d", pipe_active_d1), ("q", pipe_active_d2), ("clock", clock), ("reset", reset_misc_dp)]
  }
  let pipe_was_active := Wire.mk "pipe_was_active_d"
  let pipe_active_or_gate := [Gate.mkOR pipe_active_d1 pipe_active_d2 pipe_was_active]

  let busy_gate := [
    Gate.mkOR div_sp_busy div_dp_busy (Wire.mk "busy_div_any"),
    Gate.mkOR sqrt_sp_busy sqrt_dp_busy (Wire.mk "busy_sqrt_any"),
    Gate.mkOR (Wire.mk "busy_div_any") (Wire.mk "busy_sqrt_any") (Wire.mk "busy_iter"),
    Gate.mkOR (Wire.mk "busy_iter") pipe_was_active (Wire.mk "busy_core_d"),
    Gate.mkOR add_valid mul_valid (Wire.mk "pout_am_d"),
    Gate.mkOR fma_valid sqrt_valid (Wire.mk "pout_fs_d"),
    Gate.mkOR (Wire.mk "pout_am_d") (Wire.mk "pout_fs_d") (Wire.mk "pout_amfs_d"),
    Gate.mkOR (Wire.mk "pout_amfs_d") div_valid (Wire.mk "pout_amfsd_d"),
    Gate.mkOR (Wire.mk "pout_amfsd_d") misc_reg_valid (Wire.mk "any_pout_d"),
    Gate.mkOR (Wire.mk "busy_core_d") (Wire.mk "any_pout_d") busy
  ]

  -- ══════════════════════════════════════════════
  -- result_is_int
  -- High when output comes from misc path and targets INT PRF
  -- (SP int-writing op detection lives above, next to the misc merge)
  -- ══════════════════════════════════════════════
  let dp_misc_or_conv_rint := Wire.mk "dp_rint_comb"
  let active_writes_int_pre := Wire.mk "active_writes_int_pre"
  let int_result_gates := [
    Gate.mkMUX misc_dp_rint conv_dp_rint is_dp_conv dp_misc_or_conv_rint,
    Gate.mkMUX sp_writes_int dp_misc_or_conv_rint is_dp active_writes_int_pre,
    Gate.mkMUX active_writes_int_pre conv_long_rint is_long_conv (Wire.mk "active_writes_int"),
    Gate.mkOR mul_valid add_valid (Wire.mk "rint_d_t1"),
    Gate.mkOR fma_valid div_valid (Wire.mk "rint_d_t2"),
    Gate.mkOR sqrt_valid (Wire.mk "rint_d_t1") (Wire.mk "rint_d_t3"),
    Gate.mkOR (Wire.mk "rint_d_t2") (Wire.mk "rint_d_t3") (Wire.mk "rint_d_t4"),
    Gate.mkNOT (Wire.mk "rint_d_t4") (Wire.mk "no_override_d"),
    Gate.mkAND misc_reg_valid (Wire.mk "no_override_d") (Wire.mk "rint_d_t5"),
    Gate.mkAND (Wire.mk "rint_d_t5") misc_reg_writes_int result_is_int
  ]

  let all_gates :=
    reset_gates ++ op_inv_gates ++ cat_decode_gates ++ fma_ctrl_gates ++ valid_gates ++
    s1_hi_ones_gates ++ s2_hi_ones_gates ++ s3_hi_ones_gates ++
    s1_int_gates ++ [s1_byp_gate] ++ unbox_gates ++
    add_merge_gates ++ mul_merge_gates ++ fma_merge_gates ++ div_merge_gates ++ sqrt_merge_gates ++
    is_dp_conv_gates ++ sp_int_detect_gates ++ misc_merge_gates ++ misc_pipe_dffs ++
    long_op_gates ++ long_conv_dec_gates ++ long_src1_gates ++
    mux1_gates ++ mux2_gates ++ mux3_gates ++ mux4_gates ++ mux5_gates ++
    pipe_collision_gates ++ pipe_active_or_gate ++ busy_gate ++ int_result_gates

  { name := "FPExecUnit_D"
    inputs := src1 ++ src2 ++ src3 ++ op ++ rm ++ dest_tag ++
              [valid_in, clock, reset, zero, one]
    outputs := result ++ tag_out ++ exceptions ++ [valid_out, busy, result_is_int]
    gates := all_gates
    instances := [
      misc_sp_inst, adder_sp_inst, mul_sp_inst, fma_sp_inst, div_sp_inst, sqrt_sp_inst,
      misc_dp_inst, conv_dp_inst, conv_long_inst, adder_dp_inst, mul_dp_inst, fma_dp_inst, div_dp_inst, sqrt_dp_inst,
      pipe_collision_inst1, pipe_collision_inst2
    ]
    signalGroups := [
      { name := "src1", width := 64, wires := src1 },
      { name := "src2", width := 64, wires := src2 },
      { name := "src3", width := 64, wires := src3 },
      { name := "op", width := 6, wires := op },
      { name := "rm", width := 3, wires := rm },
      { name := "dest_tag", width := 6, wires := dest_tag },
      { name := "result", width := 64, wires := result },
      { name := "tag_out", width := 6, wires := tag_out },
      { name := "exceptions", width := 5, wires := exceptions }
    ]
    keepHierarchy := true
  }

/-- Convenience alias -/
def fpExecUnitD : Circuit := mkFPExecUnitD

def fpExecUnit : Circuit := mkFPExecUnit

end Shoumei.RISCV.Execution
