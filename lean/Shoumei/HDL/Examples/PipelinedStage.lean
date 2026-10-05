/-
HDL/Examples/PipelinedStage.lean - Pipelined Arithmetic Example in High-Level DSL

Demonstrates a 2-stage pipelined Multiply-Accumulate (MAC) unit:
- Stage 1: Registers inputs and computes product
- Stage 2: Adds addend to registered product and produces registered output
- Lowers down to a clean netlist Circuit with DFF gates and submodules
-/

import Shoumei.HDL.Types
import Shoumei.HDL.Expr
import Shoumei.HDL.Module
import Shoumei.HDL.Lower

namespace Shoumei.HDL.Examples

open Shoumei
open Shoumei.HDL

/-- Construct a 2-stage 32-bit Multiply-Accumulate unit in the high-level DSL. -/
def mkPipelinedMAC (clock reset : Wire) : HDLModule :=
  let a : Signal 16 := .input "a" 16
  let b : Signal 16 := .input "b" 16
  let c : Signal 32 := .input "c" 32

  -- Stage 1: Product computation
  let prod : Signal 32 := .mul a b

  -- Stage 1 Pipeline Registers
  let prod_reg : Signal 32 := Signal.register "prod_stage1" clock reset prod
  let c_reg : Signal 32 := Signal.register "c_stage1" clock reset c

  -- Stage 2: Accumulation
  let sum : Signal 32 := .add prod_reg c_reg

  -- Stage 2 Output Register
  let result_reg : Signal 32 := Signal.register "result_stage2" clock reset sum

  let m : HDLModule := HDLModule.empty "PipelinedMAC"
  let m := m.addInput "a" 16
  let m := m.addInput "b" 16
  let m := m.addInput "c" 32
  let m := m.addOutput "result" 32 result_reg
  m

/-- Lowered Circuit representation of the 2-stage MAC unit. -/
def pipelinedMACCircuit (clock reset : Wire) : Circuit :=
  lowerModule (mkPipelinedMAC clock reset)

end Shoumei.HDL.Examples
