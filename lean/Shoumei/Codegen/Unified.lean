/-
Codegen/Unified.lean - Unified Code Generation Infrastructure

Provides a single, consistent interface for generating all output formats:
- SystemVerilog (hierarchical, output/sv-from-lean/)
- SystemVerilog Netlist (flat, output/sv-netlist/)
- Chisel (hierarchical, chisel/src/main/scala/generated/)
- SystemC (output/systemc/)

Usage:
  writeCircuit myCircuit  -- Generates all 4 outputs
  writeCircuitSV myCircuit  -- Just SystemVerilog
  writeCircuitNetlist myCircuit  -- Just SystemVerilog netlist
  writeCircuitChisel myCircuit  -- Just Chisel
  writeCircuitSystemC myCircuit  -- Just SystemC
-/

import Shoumei.DSL
import Shoumei.Codegen.SystemVerilog
import Shoumei.Codegen.SystemVerilogNetlist
import Shoumei.Codegen.Chisel
import Shoumei.Codegen.SystemC
import Shoumei.Codegen.Testbench
import Shoumei.Codegen.ASAP7

namespace Shoumei.Codegen.Unified

open Shoumei
open Shoumei.Codegen

-- Output paths (centralized configuration)
def svOutputDir : String := "output/sv-from-lean"
def svNetlistOutputDir : String := "output/sv-netlist"
def chiselOutputDir : String := "chisel/src/main/scala/generated"
def systemcOutputDir : String := "output/systemc"
def asap7OutputDir : String := "output/sv-asap7"

-- Write SystemVerilog (hierarchical) for a circuit
-- Pass allCircuits for sub-module port structure lookup in hierarchical modules
def writeCircuitSV (c : Circuit) (allCircuits : List Circuit := []) : IO Unit := do
  let sv := SystemVerilog.toSystemVerilog c allCircuits
  let path := s!"{svOutputDir}/{c.name}.sv"
  IO.FS.writeFile path sv

-- Write SystemVerilog Netlist (flat) for a circuit
def writeCircuitNetlist (c : Circuit) : IO Unit := do
  let sv := SystemVerilogNetlist.toSystemVerilogNetlist c
  let path := s!"{svNetlistOutputDir}/{c.name}.sv"
  IO.FS.writeFile path sv

-- Write Chisel (hierarchical) for a circuit
-- Pass allCircuits for sub-module port direction lookup in hierarchical modules
def writeCircuitChisel (c : Circuit) (allCircuits : List Circuit := []) : IO Unit := do
  let chisel := Chisel.toChisel c allCircuits
  let path := s!"{chiselOutputDir}/{c.name}.scala"
  IO.FS.writeFile path chisel

-- Write SystemC for a circuit (.h and .cpp)
def writeCircuitSystemC (c : Circuit) (allCircuits : List Circuit := []) : IO Unit := do
  let header := SystemC.toSystemCHeader c allCircuits
  let impl := SystemC.toSystemCImpl c allCircuits
  let hPath := s!"{systemcOutputDir}/{c.name}.h"
  let cppPath := s!"{systemcOutputDir}/{c.name}.cpp"
  IO.FS.writeFile hPath header
  IO.FS.writeFile cppPath impl

-- Write ASAP7 tech-mapped SystemVerilog for a circuit (only if keepHierarchy)
def writeCircuitASAP7 (c : Circuit) (allCircuits : List Circuit := []) : IO Unit := do
  if c.keepHierarchy then
    let sv := ASAP7.toASAP7SystemVerilog c allCircuits
    let path := s!"{asap7OutputDir}/{c.name}.sv"
    IO.FS.writeFile path sv

-- Modules with known Chisel codegen limitations (instance bus-port bit mapping)
-- These are verified via SV LEC + compositional certs instead
-- TODO: Fix Chisel codegen for these modules so this skip list can be removed:
--   - FP circuits: JVM method size limits (flat circuits too large for single Scala method)
--   - FPAdder/FPDivider: FIRRTL false-positive combinational cycle on carry-chain topology
--   - CPU_RV32IF/IMF: instance bus-port bit mapping (issue_opcode_5 as individual port)
-- All are verified via SV LEC + compositional certs.
private def chiselSkipList : List String :=
  ["FPAdder", "FPDivider", "FPMisc", "FPMultiplier", "FPFMA", "FPExecUnit",
   "CPU_RV32IF", "CPU_RV32IMF"]

-- Write all output formats for a circuit
def writeCircuit (c : Circuit) (allCircuits : List Circuit := []) : IO Unit := do
  writeCircuitSV c allCircuits
  writeCircuitNetlist c
  if chiselSkipList.contains c.name then
    IO.println s!"  (skipping Chisel for {c.name} — verified via SV LEC)"
  else
    writeCircuitChisel c allCircuits
  writeCircuitSystemC c allCircuits
  writeCircuitASAP7 c allCircuits
  let asap7Tag := if c.keepHierarchy then " +ASAP7" else ""
  IO.println s!"✓ Generated {c.name}: {c.gates.length} gates, {c.instances.length} instances{asap7Tag}"

-- Verbose version with individual file confirmation
def writeCircuitVerbose (c : Circuit) (allCircuits : List Circuit := []) : IO Unit := do
  writeCircuitSV c
  IO.println s!"  ✓ {c.name}.sv"

  writeCircuitNetlist c
  IO.println s!"  ✓ {c.name}.sv (netlist)"

  writeCircuitChisel c allCircuits
  IO.println s!"  ✓ {c.name}.scala"

  writeCircuitSystemC c allCircuits
  IO.println s!"  ✓ {c.name}.h / {c.name}.cpp"

  IO.println s!"  ({c.gates.length} gates, {c.instances.length} instances)"

-- Write a filelist.f for a directory listing all files matching an extension
def writeFilelist (dir : String) (ext : String) : IO Unit := do
  let entries ← System.FilePath.readDir dir
  let files := entries.filter (fun e => e.fileName.endsWith ext)
  let sorted := files.toList.map (fun e => e.fileName) |>.mergeSort (· < ·)
  let content := String.intercalate "\n" sorted ++ "\n"
  IO.FS.writeFile s!"{dir}/filelist.f" content

-- Initialize output directories
def initOutputDirs : IO Unit := do
  IO.FS.createDirAll svOutputDir
  IO.FS.createDirAll svNetlistOutputDir
  IO.FS.createDirAll chiselOutputDir
  IO.FS.createDirAll systemcOutputDir
  IO.FS.createDirAll asap7OutputDir

-- Write SystemVerilog testbench for a TestbenchConfig
def writeTestbenchSV (cfg : Testbench.TestbenchConfig) : IO Unit :=
  Testbench.writeTestbenchSV cfg

-- Write SystemC testbench for a TestbenchConfig
def writeTestbenchSystemC (cfg : Testbench.TestbenchConfig) : IO Unit :=
  Testbench.writeTestbenchSystemC cfg

-- Write both testbenches
def writeTestbenches (cfg : Testbench.TestbenchConfig) : IO Unit :=
  Testbench.writeTestbenches cfg

end Shoumei.Codegen.Unified
