/-
HDL/Tests.lean - Verification and Unit Tests for Two-Level HDL

Validates:
- Structural properties of lowered circuits (inputs, outputs, signal groups)
- Definitional reduction of high-level signal semantics through `rfl`
- Behavioral equivalence of arithmetic, multiplexing, and bit-slicing
-/

import Shoumei.HDL.Types
import Shoumei.HDL.Expr
import Shoumei.HDL.Module
import Shoumei.HDL.Lower
import Shoumei.HDL.Semantics
import Shoumei.HDL.Examples.PipelinedStage

namespace Shoumei.HDL.Tests

open Shoumei
open Shoumei.HDL
open Shoumei.HDL.Examples

/-! ## Structural Theorems on Lowered Pipelined MAC -/

def testMAC : Circuit :=
  pipelinedMACCircuit (Wire.mk "clock") (Wire.mk "reset")

/-- Input count: 16 (a) + 16 (b) + 32 (c) = 64 inputs. -/
theorem pipelinedMAC_input_count : testMAC.inputs.length = 64 := by
  native_decide

/-- Output count: 32 (result) = 32 outputs. -/
theorem pipelinedMAC_output_count : testMAC.outputs.length = 32 := by
  native_decide

/-- Signal group count: bundled buses for result, stage1, and stage2. -/
theorem pipelinedMAC_signal_groups : testMAC.signalGroups.length = 4 := by
  native_decide

/-! ## Semantic Reduction Tests through `rfl` -/

def dummyEnv : Env := fun _ => false

-- Test 1: Addition semantics
def addSig : Signal 8 :=
  .add (.const 10) (.const 25)

theorem eval_add : evalSignal dummyEnv addSig = 35 := by
  rfl

-- Test 2: Subtraction semantics
def subSig : Signal 8 :=
  .sub (.const 50) (.const 8)

theorem eval_sub : evalSignal dummyEnv subSig = 42 := by
  rfl

-- Test 3: Multiplexer selection
def muxThen : Signal 8 :=
  .mux .true1 (.const 42) (.const 99)

def muxElse : Signal 8 :=
  .mux .false1 (.const 42) (.const 99)

theorem eval_mux_then : evalSignal dummyEnv muxThen = 42 := by
  rfl

theorem eval_mux_else : evalSignal dummyEnv muxElse = 99 := by
  rfl

-- Test 4: Concatenation semantics (MSB first)
def concatSig : Signal 16 :=
  .concat (.const (BitVec.ofNat 8 0xAB)) (.const (BitVec.ofNat 8 0xCD))

theorem eval_concat : evalSignal dummyEnv concatSig = 0xABCD := by
  rfl

-- Test 5: Bit extraction semantics
def extractHi : Signal 8 :=
  .extract concatSig 15 8

def extractLo : Signal 8 :=
  .extract concatSig 7 0

theorem eval_extract_hi : evalSignal dummyEnv extractHi = 0xAB := by
  rfl

theorem eval_extract_lo : evalSignal dummyEnv extractLo = 0xCD := by
  rfl

-- Test 6: Relational comparisons
def eqTrueSig : Signal 1 :=
  .eq (.const (BitVec.ofNat 8 42)) (.const (BitVec.ofNat 8 42))

def eqFalseSig : Signal 1 :=
  .eq (.const (BitVec.ofNat 8 42)) (.const (BitVec.ofNat 8 99))

theorem eval_eq_true : evalSignal dummyEnv eqTrueSig = 1 := by
  rfl

theorem eval_eq_false : evalSignal dummyEnv eqFalseSig = 0 := by
  rfl

-- Test 7: Static shifts
def shiftSig : Signal 8 :=
  Signal.shl 2 (.const (BitVec.ofNat 8 0x0F))

theorem eval_shl : evalSignal dummyEnv shiftSig = 0x3C := by
  decide

end Shoumei.HDL.Tests
