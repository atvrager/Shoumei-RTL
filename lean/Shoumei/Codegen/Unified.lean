/-
Codegen/Unified.lean - Unified Code Generation Infrastructure

Provides a single, consistent interface for generating all output formats:
- SystemVerilog (hierarchical, output/sv-from-lean/)
- SystemVerilog Netlist (flat, output/sv-netlist/)
- C++ Simulation (output/cpp_sim/)

Usage:
  writeCircuit myCircuit  -- Generates all outputs
  writeCircuitSV myCircuit  -- Just SystemVerilog
  writeCircuitNetlist myCircuit  -- Just SystemVerilog netlist
  writeCircuitCppSim myCircuit  -- Just C++ Simulation
-/

import Shoumei.DSL
import Shoumei.Codegen.SystemVerilog
import Shoumei.Codegen.SystemVerilogNetlist
import Shoumei.Codegen.CppSim
import Shoumei.Codegen.Testbench
import Shoumei.Codegen.TechMap
import Shoumei.Codegen.CellNetlist

namespace Shoumei.Codegen.Unified

open Shoumei
open Shoumei.Components
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

/-- Bump whenever a code generator changes in a way that alters emitted text
    without altering circuit structure, or when the set of emitted formats
    changes.  The cache key includes this version, so a bump invalidates every
    cached output and forces a full regeneration. -/
def codegenVersion : String := "pdk-techmap-2026-09-20c"

/-- Check if circuit hash matches cached value (and the codegen version). -/
def isUpToDate (name : String) (h : UInt64) : IO Bool := do
  let path := s!"{cacheDir}/{name}.hash"
  if ← System.FilePath.pathExists path then
    let stored ← IO.FS.readFile path
    return stored.trimAscii.toString == s!"{codegenVersion}:{h}"
  return false

/-- Write circuit hash to cache (tagged with the codegen version). -/
def updateCache (name : String) (h : UInt64) : IO Unit := do
  IO.FS.createDirAll cacheDir
  IO.FS.writeFile s!"{cacheDir}/{name}.hash" s!"{codegenVersion}:{h}"

-- Output paths (centralized configuration)
def svOutputDir : String := "output/sv-from-lean"
def svNetlistOutputDir : String := "output/sv-netlist"
def cppSimOutputDir : String := "output/cpp_sim"
def pdkOutputDir : PDK → String
  | .asap7    => "output/sv-asap7"
  | .gf180mcu => "output/sv-gf180"

/-- Every PDK the codegen emits tech-mapped SV for. -/
def allPdks : List PDK := [.asap7, .gf180mcu]

-- Write SystemVerilog (hierarchical) for a circuit
-- Pass allCircuits for sub-module port structure lookup in hierarchical modules
def writeCircuitSV (c : Circuit) (allCircuits : List Circuit := [])
    (precomputedLoaded : Std.HashMap String (Std.HashSet String) := {}) : IO Unit := do
  let sv := SystemVerilog.toSystemVerilog c allCircuits precomputedLoaded
  let path := s!"{svOutputDir}/{c.name}.sv"
  IO.FS.writeFile path sv

-- Write SystemVerilog Netlist (flat) for a circuit
def writeCircuitNetlist (c : Circuit) : IO Unit := do
  let sv := SystemVerilogNetlist.toSystemVerilogNetlist c
  let path := s!"{svNetlistOutputDir}/{c.name}.sv"
  IO.FS.writeFile path sv

-- Write C++ Simulation for a circuit (.h and .cpp)
def writeCircuitCppSim (c : Circuit) (allCircuits : List Circuit := []) : IO Unit := do
  let header := CppSim.toCppSimHeader c allCircuits
  let impl := CppSim.toCppSimImpl c allCircuits
  let hPath := s!"{cppSimOutputDir}/{c.name}.h"
  let cppPath := s!"{cppSimOutputDir}/{c.name}.cpp"
  IO.FS.writeFile hPath header
  IO.FS.writeFile cppPath impl

-- Write PDK tech-mapped SystemVerilog for a circuit (only if keepHierarchy)
def writeCircuitPDK (pdk : PDK) (c : Circuit) (allCircuits : List Circuit := [])
    (precomputedLoaded : Std.HashMap String (Std.HashSet String) := {}) : IO Unit := do
  if c.keepHierarchy then
    let sv := CellNetlist.toSV (techMap pdk c) allCircuits precomputedLoaded
    let path := s!"{pdkOutputDir pdk}/{c.name}.sv"
    IO.FS.writeFile path sv

-- Write all output formats for a circuit
-- When force=false, skip generation if the circuit hash matches the cached value.
-- hashMap provides pre-computed dependency-aware hashes.
def writeCircuit (c : Circuit) (allCircuits : List Circuit := [])
    (force : Bool := true) (hashMap : List (String × UInt64) := {})
    (precomputedLoaded : Std.HashMap String (Std.HashSet String) := {}) : IO Unit := do
  -- Check cache (skip if unchanged)
  if !force then
    if let some h := lookupHash hashMap c.name then
      if ← isUpToDate c.name h then
        IO.println s!"— {c.name} (unchanged, skipping)"
        return
  writeCircuitSV c allCircuits precomputedLoaded
  writeCircuitNetlist c
  writeCircuitCppSim c allCircuits
  for pdk in allPdks do
    writeCircuitPDK pdk c allCircuits precomputedLoaded
  -- Update cache after successful generation
  if let some h := lookupHash hashMap c.name then
    updateCache c.name h
  let pdkTag := if c.keepHierarchy then " +techmap" else ""
  IO.println s!"✓ Generated {c.name}: {c.gates.length} gates, {c.instances.length} instances{pdkTag}"

-- Verbose version with individual file confirmation
def writeCircuitVerbose (c : Circuit) (allCircuits : List Circuit := []) : IO Unit := do
  writeCircuitSV c
  IO.println s!"  ✓ {c.name}.sv"

  writeCircuitNetlist c
  IO.println s!"  ✓ {c.name}.sv (netlist)"

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

def physicalOutputDir : String := "physical"

/-- Write a physical synthesis filelist (.f) for a given synth wrapper.
    Prefers the target PDK's tech-mapped modules over the generic sv-from-lean
    modules, so a mapped module is never shadowed by its gate-level form. -/
def writePhysicalFilelist (wrapperName : String) (pdk : PDK := .asap7) : IO Unit := do
  let dir := pdkOutputDir pdk
  let mappedEntries ← System.FilePath.readDir dir
  let mappedFiles := mappedEntries.filter (fun e => e.fileName.endsWith ".sv")
  let mappedNames := mappedFiles.toList.map (fun e => e.fileName) |>.toArray
  let leanEntries ← System.FilePath.readDir svOutputDir
  let leanFiles := leanEntries.filter (fun e =>
    e.fileName.endsWith ".sv" && !mappedNames.contains e.fileName)
  let mappedPaths := mappedFiles.toList.map (fun e => s!"{dir}/{e.fileName}")
  let leanPaths := leanFiles.toList.map (fun e => s!"{svOutputDir}/{e.fileName}")
  let allPaths := (mappedPaths ++ leanPaths).mergeSort (· < ·)
    |>.append [s!"{physicalOutputDir}/{wrapperName}.sv"]
  let content := String.intercalate "\n" allPaths ++ "\n"
  IO.FS.writeFile s!"{physicalOutputDir}/{wrapperName}.f" content


/-- Delete stale generated files.

    Files in the generated-output directories whose base name is not among
    `keepNames` and whose contents carry a code-generation marker are removed.
    This keeps removed/renamed modules (e.g. a renamed CPU top or a resized
    register) from lingering in the build filelists and breaking elaboration. -/
def pruneStaleOutputs (keepNames : List String) : IO Unit := do
  -- Match case-insensitively: generators emit "Generated by", "Auto-generated", etc.
  let markers := ["generated by", "auto-generated", "do not edit", "generated from",
                  "generated systemverilog", "generated risc-v", "eval_comb_all", "comb_logic"]
  let dirs := [svOutputDir, svNetlistOutputDir, cppSimOutputDir] ++ allPdks.map pdkOutputDir
  for dir in dirs do
    let entries ← System.FilePath.readDir dir
    for e in entries do
      let name := e.fileName
      if name == "filelist.f" then continue
      let base := (name.takeWhile (· != '.')).toString
      if keepNames.contains base then continue
      let path := s!"{dir}/{name}"
      let content ← (try IO.FS.readFile path catch _ => pure "")
      let lower := content.toLower
      if markers.any (lower.contains ·) then
        IO.FS.removeFile path
        -- Drop the hash-cache entry too, so the file is regenerated if the
        -- module ever comes back (the incremental cache skips unchanged names).
        let cachePath := s!"{cacheDir}/{base}.hash"
        if ← System.FilePath.pathExists cachePath then
          IO.FS.removeFile cachePath
        IO.println s!"  pruned stale output: {path}"

-- Initialize output directories
def initOutputDirs : IO Unit := do
  IO.FS.createDirAll svOutputDir
  IO.FS.createDirAll svNetlistOutputDir
  IO.FS.createDirAll cppSimOutputDir
  for pdk in allPdks do
    IO.FS.createDirAll (pdkOutputDir pdk)

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
