/-
Codegen/Unified.lean - Unified Code Generation Infrastructure

Provides a single, consistent interface for generating all output formats:
- SystemVerilog (hierarchical, output/sv-from-lean/)
- SystemVerilog Netlist (flat, output/sv-netlist/)
- Chisel (hierarchical, chisel/src/main/scala/generated/)
- C++ Simulation (output/cpp_sim/)

Usage:
  writeCircuit myCircuit  -- Generates all 4 outputs
  writeCircuitSV myCircuit  -- Just SystemVerilog
  writeCircuitNetlist myCircuit  -- Just SystemVerilog netlist
  writeCircuitChisel myCircuit  -- Just Chisel
  writeCircuitCppSim myCircuit  -- Just C++ Simulation
-/

import Shoumei.DSL
import Shoumei.Codegen.SystemVerilog
import Shoumei.Codegen.SystemVerilogNetlist
import Shoumei.Codegen.Chisel
import Shoumei.Codegen.CppSim
import Shoumei.Codegen.Testbench
import Shoumei.Codegen.ASAP7

namespace Shoumei.Codegen.Unified

open Shoumei
open Shoumei.Codegen

-- Incremental codegen: content-hash circuits, skip unchanged ones
def cacheDir : String := ".codegen-cache"

/-- Compute a dependency-aware hash for a circuit.
    Includes hashes of all transitively instantiated sub-circuits. -/
def lookupHash (hashMap : List (String × UInt64)) (name : String) : Option UInt64 :=
  hashMap.find? (fun p => p.1 == name) |>.map (·.2)

def circuitHashWithDeps (hashMap : List (String × UInt64)) (c : Circuit) : UInt64 :=
  let baseHash := hash c
  let depHashes := c.instances.filterMap fun inst =>
    lookupHash hashMap inst.moduleName
  hash (baseHash, hash depHashes)

/-- Pre-compute hashes for all circuits in dependency order.
    Since allCircuits is already in topological order (leaves first),
    we can compute hashes in a single pass. -/
def computeAllHashes (allCircuits : List Circuit) : List (String × UInt64) :=
  allCircuits.foldl (fun acc c =>
    let h := circuitHashWithDeps acc c
    acc ++ [(c.name, h)]
  ) []

/-- Check if circuit hash matches cached value. -/
def isUpToDate (name : String) (h : UInt64) : IO Bool := do
  let path := s!"{cacheDir}/{name}.hash"
  if ← System.FilePath.pathExists path then
    let stored ← IO.FS.readFile path
    return stored.trimAscii.toString == toString h
  return false

/-- Write circuit hash to cache. -/
def updateCache (name : String) (h : UInt64) : IO Unit := do
  IO.FS.createDirAll cacheDir
  IO.FS.writeFile s!"{cacheDir}/{name}.hash" (toString h)

-- Output paths (centralized configuration)
def svOutputDir : String := "output/sv-from-lean"
def svNetlistOutputDir : String := "output/sv-netlist"
def chiselOutputDir : String := "chisel/src/main/scala/generated"
def cppSimOutputDir : String := "output/cpp_sim"
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

-- Write C++ Simulation for a circuit (.h and .cpp)
def writeCircuitCppSim (c : Circuit) (allCircuits : List Circuit := []) : IO Unit := do
  let header := CppSim.toCppSimHeader c allCircuits
  let impl := CppSim.toCppSimImpl c allCircuits
  let hPath := s!"{cppSimOutputDir}/{c.name}.h"
  let cppPath := s!"{cppSimOutputDir}/{c.name}.cpp"
  IO.FS.writeFile hPath header
  IO.FS.writeFile cppPath impl

-- Write ASAP7 tech-mapped SystemVerilog for a circuit (only if keepHierarchy)
def writeCircuitASAP7 (c : Circuit) (allCircuits : List Circuit := []) : IO Unit := do
  if c.keepHierarchy then
    let sv := ASAP7.toASAP7SystemVerilog c allCircuits
    let path := s!"{asap7OutputDir}/{c.name}.sv"
    IO.FS.writeFile path sv

-- Write all output formats for a circuit
-- When force=false, skip generation if the circuit hash matches the cached value.
-- hashMap provides pre-computed dependency-aware hashes.
def writeCircuit (c : Circuit) (allCircuits : List Circuit := [])
    (force : Bool := true) (hashMap : List (String × UInt64) := {}) : IO Unit := do
  -- Check cache (skip if unchanged)
  if !force then
    if let some h := lookupHash hashMap c.name then
      if ← isUpToDate c.name h then
        IO.println s!"— {c.name} (unchanged, skipping)"
        return
  writeCircuitSV c allCircuits
  writeCircuitNetlist c
  writeCircuitChisel c allCircuits
  writeCircuitCppSim c allCircuits
  writeCircuitASAP7 c allCircuits
  -- Update cache after successful generation
  if let some h := lookupHash hashMap c.name then
    updateCache c.name h
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

  writeCircuitCppSim c allCircuits
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
  IO.FS.createDirAll cppSimOutputDir
  IO.FS.createDirAll asap7OutputDir

-- Write SystemVerilog testbench for a TestbenchConfig
def writeTestbenchSV (cfg : Testbench.TestbenchConfig) : IO Unit :=
  Testbench.writeTestbenchSV cfg

-- Write C++ simulation testbench for a TestbenchConfig
def writeTestbenchCppSim (cfg : Testbench.TestbenchConfig) : IO Unit :=
  Testbench.writeTestbenchCppSim cfg

-- Write both testbenches
def writeTestbenches (cfg : Testbench.TestbenchConfig) : IO Unit :=
  Testbench.writeTestbenches cfg

end Shoumei.Codegen.Unified
