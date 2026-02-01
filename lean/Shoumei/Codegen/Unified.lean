/-
Codegen/Unified.lean - Unified Code Generation Infrastructure

Provides a single, consistent interface for generating all output formats:
- SystemVerilog (output/sv-from-lean/)
- Chisel (chisel/src/main/scala/generated/)
- SystemC (output/systemc/)

Usage:
  writeCircuit myCircuit  -- Generates all 3 outputs
  writeCircuitSV myCircuit  -- Just SystemVerilog
  writeCircuitChisel myCircuit  -- Just Chisel
  writeCircuitSystemC myCircuit  -- Just SystemC
-/

import Shoumei.DSL
import Shoumei.Codegen.SystemVerilog
import Shoumei.Codegen.Chisel
import Shoumei.Codegen.SystemC

namespace Shoumei.Codegen.Unified

open Shoumei
open Shoumei.Codegen

-- Output paths (centralized configuration)
def svOutputDir : String := "output/sv-from-lean"
def chiselOutputDir : String := "chisel/src/main/scala/generated"
def systemcOutputDir : String := "output/systemc"

-- Write SystemVerilog for a circuit
def writeCircuitSV (c : Circuit) : IO Unit := do
  let sv := SystemVerilog.toSystemVerilog c
  let path := s!"{svOutputDir}/{c.name}.sv"
  IO.FS.writeFile path sv

-- Write Chisel for a circuit
def writeCircuitChisel (c : Circuit) : IO Unit := do
  let chisel := Chisel.toChisel c
  let path := s!"{chiselOutputDir}/{c.name}.scala"
  IO.FS.writeFile path chisel

-- Write SystemC for a circuit (.h and .cpp)
def writeCircuitSystemC (c : Circuit) : IO Unit := do
  let header := SystemC.toSystemCHeader c
  let impl := SystemC.toSystemCImpl c
  let hPath := s!"{systemcOutputDir}/{c.name}.h"
  let cppPath := s!"{systemcOutputDir}/{c.name}.cpp"
  IO.FS.writeFile hPath header
  IO.FS.writeFile cppPath impl

-- Write all output formats for a circuit
def writeCircuit (c : Circuit) : IO Unit := do
  writeCircuitSV c
  writeCircuitChisel c
  writeCircuitSystemC c
  IO.println s!"✓ Generated {c.name}: {c.gates.length} gates, {c.instances.length} instances"

-- Verbose version with individual file confirmation
def writeCircuitVerbose (c : Circuit) : IO Unit := do
  writeCircuitSV c
  IO.println s!"  ✓ {c.name}.sv"

  writeCircuitChisel c
  IO.println s!"  ✓ {c.name}.scala"

  writeCircuitSystemC c
  IO.println s!"  ✓ {c.name}.h / {c.name}.cpp"

  IO.println s!"  ({c.gates.length} gates, {c.instances.length} instances)"

-- Initialize output directories
def initOutputDirs : IO Unit := do
  IO.FS.createDirAll svOutputDir
  IO.FS.createDirAll chiselOutputDir
  IO.FS.createDirAll systemcOutputDir

end Shoumei.Codegen.Unified
