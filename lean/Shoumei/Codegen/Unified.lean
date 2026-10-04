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

/-- Hash a circuit together with everything it instantiates, transitively.
    Dependencies come from `byName` and are memoised in `memo`, so the outcome
    does not depend on the order of `allCircuits`.  A single forward pass drops
    a dependency that appears later in the list, and a later change to that
    dependency then never invalidates the cached output.

    A provisional entry goes in before recursing, so a dependency cycle
    terminates instead of looping; the true hash replaces it on the way out. -/
partial def hashWithDeps (byName : Std.HashMap String Circuit)
    (memo : Std.HashMap String UInt64) (c : Circuit) :
    UInt64 × Std.HashMap String UInt64 :=
  match memo.get? c.name with
  | some h => (h, memo)
  | none =>
    let memoProv := memo.insert c.name (hash c)
    let (depHashes, memo') := c.instances.foldl
      (init := (([] : List UInt64), memoProv))
      fun (acc : List UInt64 × Std.HashMap String UInt64) inst =>
        match byName.get? inst.moduleName with
        | some sub =>
          let (h, m') := hashWithDeps byName acc.2 sub
          (acc.1 ++ [h], m')
        -- Not emitted by this generator, so its content cannot change here.
        | none => acc
    let h := hash (hash c, hash depHashes)
    (h, memo'.insert c.name h)

/-- Pre-compute dependency-aware hashes for every circuit.  Order-independent:
    a circuit's hash covers its dependencies however the list is arranged. -/
def computeAllHashes (allCircuits : List Circuit) : List (String × UInt64) :=
  let byName : Std.HashMap String Circuit :=
    allCircuits.foldl (fun m c => m.insert c.name c) {}
  let (pairs, _) := allCircuits.foldl
    (init := (([] : List (String × UInt64)), ({} : Std.HashMap String UInt64)))
    fun (acc : List (String × UInt64) × Std.HashMap String UInt64) c =>
      let (h, memo') := hashWithDeps byName acc.2 c
      (acc.1 ++ [(c.name, h)], memo')
  pairs

/-- Bump whenever a code generator changes in a way that alters emitted text
    without altering circuit structure, or when the set of emitted formats
    changes.  The cache key includes this version, so a bump invalidates every
    cached output and forces a full regeneration. -/
def codegenVersion : String := "geom64-dpi-2026-09-20g"

-- Output paths (centralized configuration)
def svOutputDir : String := "output/sv-from-lean"

/-- Check if circuit hash matches cached value (and the codegen version).
    `emitted` is every file the caller would write: a deleted output (or a
    cleaned directory) must force regeneration, and the hash file alone would
    otherwise report the circuit as up to date.  Checking only the SV left a
    deleted netlist or C++ model permanently missing. -/
def isUpToDate (name : String) (h : UInt64) (emitted : List String) : IO Bool := do
  let path := s!"{cacheDir}/{name}.hash"
  unless (← System.FilePath.pathExists path) do return false
  for f in emitted do
    unless (← System.FilePath.pathExists f) do return false
  let stored ← IO.FS.readFile path
  return stored.trimAscii.toString == s!"{codegenVersion}:{h}"

/-- Write circuit hash to cache (tagged with the codegen version). -/
def updateCache (name : String) (h : UInt64) : IO Unit := do
  IO.FS.createDirAll cacheDir
  IO.FS.writeFile s!"{cacheDir}/{name}.hash" s!"{codegenVersion}:{h}"

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

/-- Every file writeCircuit emits for a circuit.  The up-to-date check needs
    the full list: checking only the SV left a deleted netlist or C++ model
    permanently missing. -/
def emittedPaths (c : Circuit) : List String :=
  [s!"{svOutputDir}/{c.name}.sv", s!"{svNetlistOutputDir}/{c.name}.sv",
   s!"{cppSimOutputDir}/{c.name}.h", s!"{cppSimOutputDir}/{c.name}.cpp"]
  ++ (if c.keepHierarchy then allPdks.map (fun pdk => s!"{pdkOutputDir pdk}/{c.name}.sv") else [])

-- Write all output formats for a circuit
-- When force=false, skip generation if the circuit hash matches the cached value.
-- hashMap provides pre-computed dependency-aware hashes.
def writeCircuit (c : Circuit) (allCircuits : List Circuit := [])
    (force : Bool := true) (hashMap : List (String × UInt64) := {})
    (precomputedLoaded : Std.HashMap String (Std.HashSet String) := {}) : IO Unit := do
  -- Check cache (skip if unchanged)
  if !force then
    if let some h := lookupHash hashMap c.name then
      if ← isUpToDate c.name h (emittedPaths c) then
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
