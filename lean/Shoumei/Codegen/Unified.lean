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

namespace Shoumei.Codegen.Unified

open Shoumei
open Shoumei.Codegen

-- Output paths (centralized configuration)
def svOutputDir : String := "output/sv-from-lean"
def svNetlistOutputDir : String := "output/sv-netlist"
def chiselOutputDir : String := "chisel/src/main/scala/generated"
def systemcOutputDir : String := "output/systemc"

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

-- Write all output formats for a circuit
def writeCircuit (c : Circuit) (allCircuits : List Circuit := []) : IO Unit := do
  writeCircuitSV c allCircuits
  writeCircuitNetlist c
  writeCircuitChisel c allCircuits
  writeCircuitSystemC c allCircuits
  IO.println s!"✓ Generated {c.name}: {c.gates.length} gates, {c.instances.length} instances"

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

-- Initialize output directories
def initOutputDirs : IO Unit := do
  IO.FS.createDirAll svOutputDir
  IO.FS.createDirAll svNetlistOutputDir
  IO.FS.createDirAll chiselOutputDir
  IO.FS.createDirAll systemcOutputDir

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
