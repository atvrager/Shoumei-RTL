/-
DSL/AnnotationTest.lean - Codegen V2 Annotation Readback Tests

Verifies that:
1. Annotated circuits have the correct number of signal groups and bundles
2. Annotations reference valid wire names from the underlying circuit
3. Unannotated circuits still work (default empty annotations)
4. The new DSL types are properly constructed

Run: lake build (these are compile-time checks via #eval)
-/

import Shoumei.DSL
import Shoumei.DSL.Interfaces
import Shoumei.Circuits.Sequential.Queue
import Shoumei.Circuits.Combinational.ALU
import Shoumei.RISCV.Execution.ReservationStation

open Shoumei
open Shoumei.Circuits.Sequential
open Shoumei.Circuits.Combinational
open Shoumei.RISCV.Execution

/-! ## Basic DSL type tests -/

-- SignalType construction
#eval do
  let t1 : SignalType := .Bool
  let t2 : SignalType := .UInt 32
  let t3 : SignalType := .SInt 16
  IO.println s!"SignalType: Bool={repr t1}, UInt32={repr t2}, SInt16={repr t3}"

-- SignalGroup construction
#eval do
  let sg := SignalGroup.mk' "test_bus" 8
  IO.println s!"SignalGroup '{sg.name}': width={sg.width}, wires={sg.wires.length}"
  assert! sg.width == 8
  assert! sg.wires.length == 8
  assert! sg.wires[0]!.name == "test_bus_0"
  assert! sg.wires[7]!.name == "test_bus_7"
  IO.println "  ✓ SignalGroup.mk' works correctly"

-- InterfaceBundle construction
#eval do
  let ib : InterfaceBundle := {
    name := "test_iface"
    signals := [("bits", .UInt 32), ("valid", .Bool), ("ready", .Bool)]
    protocol := some "decoupled"
  }
  IO.println s!"InterfaceBundle '{ib.name}': {ib.signals.length} signals, protocol={repr ib.protocol}"
  assert! ib.signals.length == 3
  IO.println "  ✓ InterfaceBundle construction works"

/-! ## Canonical interface library tests -/

open Shoumei.DSL.Interfaces in
#eval do
  let d := decoupledBundle 32
  assert! d.signals.length == 3
  assert! d.protocol == some "decoupled"
  IO.println s!"decoupledBundle(32): {d.signals.length} signals ✓"

  let op := operandBundle
  assert! op.signals.length == 3
  IO.println s!"operandBundle: {op.signals.length} signals ✓"

  let cdb := cdbEntryBundle
  assert! cdb.signals.length == 2
  IO.println s!"cdbEntryBundle: {cdb.signals.length} signals ✓"

  let rw := regWriteBundle 6 32
  assert! rw.signals.length == 3
  IO.println s!"regWriteBundle(6,32): {rw.signals.length} signals ✓"

  let rr := regReadBundle 6 32
  assert! rr.signals.length == 2
  IO.println s!"regReadBundle(6,32): {rr.signals.length} signals ✓"

/-! ## Backward compatibility: unannotated circuits still work -/

#eval do
  let c := mkQueue1StructuralComplete 8
  assert! c.signalGroups.length == 0
  assert! c.inputBundles.length == 0
  assert! c.outputBundles.length == 0
  assert! c.rams.length == 0
  IO.println s!"Queue1_8 (unannotated): {c.gates.length} gates, 0 annotations ✓"

#eval do
  let c := mkALU32
  assert! c.signalGroups.length == 0
  assert! c.inputBundles.length == 0
  assert! c.outputBundles.length == 0
  IO.println s!"ALU32 (unannotated): 0 annotations ✓"

/-! ## Queue1_32 annotation tests -/

#eval do
  let c := mkQueue1Annotated 32
  IO.println s!"Queue1_32 annotated:"
  IO.println s!"  name: {c.name}"
  IO.println s!"  inputs: {c.inputs.length}"
  IO.println s!"  outputs: {c.outputs.length}"
  IO.println s!"  gates: {c.gates.length}"
  IO.println s!"  signalGroups: {c.signalGroups.length}"
  IO.println s!"  inputBundles: {c.inputBundles.length}"
  IO.println s!"  outputBundles: {c.outputBundles.length}"

  -- Verify signal groups
  assert! c.signalGroups.length == 2
  let sg0 := c.signalGroups[0]!
  assert! sg0.name == "data_reg"
  assert! sg0.width == 32
  assert! sg0.wires.length == 32
  IO.println s!"  signalGroup[0]: {sg0.name}[{sg0.width}] ✓"

  let sg1 := c.signalGroups[1]!
  assert! sg1.name == "data_next"
  assert! sg1.width == 32
  IO.println s!"  signalGroup[1]: {sg1.name}[{sg1.width}] ✓"

  -- Verify interface bundles
  assert! c.inputBundles.length == 2
  assert! c.inputBundles[0]!.name == "enq"
  assert! c.inputBundles[0]!.protocol == some "decoupled"
  assert! c.inputBundles[1]!.name == "deq"
  IO.println s!"  inputBundles: enq(decoupled), deq(decoupled) ✓"

  assert! c.outputBundles.length == 2
  assert! c.outputBundles[0]!.name == "enq"
  assert! c.outputBundles[1]!.name == "deq"
  assert! c.outputBundles[1]!.protocol == some "decoupled"
  IO.println s!"  outputBundles: enq(ready), deq(decoupled) ✓"

  -- Gate list unchanged from base
  let base := mkQueue1StructuralComplete 32
  assert! c.gates.length == base.gates.length
  assert! c.inputs.length == base.inputs.length
  assert! c.outputs.length == base.outputs.length
  IO.println s!"  gates/inputs/outputs match base circuit ✓"

/-! ## ALU32 annotation tests -/

#eval do
  let c := mkALU32Annotated
  IO.println s!"ALU32 annotated:"
  IO.println s!"  signalGroups: {c.signalGroups.length}"
  IO.println s!"  inputBundles: {c.inputBundles.length}"
  IO.println s!"  outputBundles: {c.outputBundles.length}"

  -- 14 signal groups: a, b, op, result + 10 functional unit outputs
  assert! c.signalGroups.length == 14
  assert! c.signalGroups[0]!.name == "a"
  assert! c.signalGroups[0]!.width == 32
  assert! c.signalGroups[3]!.name == "result"
  IO.println s!"  14 signal groups (a, b, op, result + 10 FU outputs) ✓"

  assert! c.inputBundles.length == 1
  assert! c.inputBundles[0]!.name == "alu"
  IO.println s!"  1 input bundle (alu) ✓"

  assert! c.outputBundles.length == 1
  assert! c.outputBundles[0]!.name == "alu"
  IO.println s!"  1 output bundle (alu) ✓"

  -- Gate list unchanged
  let base := mkALU32
  assert! c.gates.length == base.gates.length
  IO.println s!"  gates match base circuit ✓"

/-! ## ReservationStation4 annotation tests -/

#eval do
  let c := mkReservationStation4Annotated
  IO.println s!"ReservationStation4 annotated:"
  IO.println s!"  signalGroups: {c.signalGroups.length}"
  IO.println s!"  inputBundles: {c.inputBundles.length}"
  IO.println s!"  outputBundles: {c.outputBundles.length}"

  -- 13 signal groups
  assert! c.signalGroups.length == 13
  assert! c.signalGroups[0]!.name == "issue_opcode"
  assert! c.signalGroups[0]!.width == 6
  assert! c.signalGroups[6]!.name == "cdb_tag"
  assert! c.signalGroups[12]!.name == "alloc_ptr"
  IO.println s!"  13 signal groups ✓"

  -- 3 input bundles: issue, cdb, dispatch
  assert! c.inputBundles.length == 3
  assert! c.inputBundles[0]!.name == "issue"
  assert! c.inputBundles[0]!.signals.length == 9
  assert! c.inputBundles[1]!.name == "cdb"
  assert! c.inputBundles[1]!.signals.length == 3
  assert! c.inputBundles[2]!.name == "dispatch"
  IO.println s!"  3 input bundles (issue[9], cdb[3], dispatch[1]) ✓"

  -- 2 output bundles: issue (status), dispatch (data)
  assert! c.outputBundles.length == 2
  assert! c.outputBundles[0]!.name == "issue"
  assert! c.outputBundles[0]!.signals.length == 1
  assert! c.outputBundles[1]!.name == "dispatch"
  assert! c.outputBundles[1]!.signals.length == 5
  IO.println s!"  2 output bundles (issue[1], dispatch[5]) ✓"

  -- Gate list and instances unchanged
  let base := mkReservationStation4
  assert! c.gates.length == base.gates.length
  assert! c.instances.length == base.instances.length
  assert! c.inputs.length == base.inputs.length
  assert! c.outputs.length == base.outputs.length
  IO.println s!"  gates/instances/ports match base circuit ✓"

/-! ## MulDivRS4 inherits annotations -/

#eval do
  let c := mkMulDivRS4Annotated
  assert! c.name == "MulDivRS4"
  assert! c.signalGroups.length == 13
  assert! c.inputBundles.length == 3
  assert! c.outputBundles.length == 2
  IO.println s!"MulDivRS4 annotated: name={c.name}, annotations inherited ✓"

/-! ## Queue1 parametric test (different widths) -/

#eval do
  for w in [1, 4, 8, 16, 32] do
    let c := mkQueue1Annotated w
    assert! c.signalGroups[0]!.width == w
    assert! c.signalGroups[0]!.wires.length == w
    assert! c.signalGroups[1]!.width == w
    IO.println s!"  Queue1_{w}: data_reg[{w}], data_next[{w}] ✓"
  IO.println "Queue1 parametric annotation test passed ✓"
