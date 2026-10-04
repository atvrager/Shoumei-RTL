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

/-- Configuration for output paths in code generation. -/
structure OutputConfig where
  svDir : System.FilePath := "output/sv-from-lean"
  netlistDir : System.FilePath := "output/sv-netlist"
  cppSimDir : System.FilePath := "output/cpp_sim"
  asap7Dir : System.FilePath := "output/sv-asap7"
  gf180Dir : System.FilePath := "output/sv-gf180"
  secDir : System.FilePath := "output/sv-sec"
  testbenchDir : System.FilePath := "testbench/generated"
  configMkPath : System.FilePath := "output/config.mk"
  physicalDir : System.FilePath := "physical"
  instrDictPath : System.FilePath := "third_party/riscv-opcodes/instr_dict.json"
  deriving Inhabited

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
    (precomputedLoaded : Std.HashMap String (Std.HashSet String) := {})
    (outDir : System.FilePath := System.FilePath.mk svOutputDir) : IO Unit := do
  let sv := SystemVerilog.toSystemVerilog c allCircuits precomputedLoaded
  let path := outDir / s!"{c.name}.sv"
  IO.FS.writeFile path.toString sv

-- Write SystemVerilog Netlist (flat) for a circuit
def writeCircuitNetlist (c : Circuit)
    (outDir : System.FilePath := System.FilePath.mk svNetlistOutputDir) : IO Unit := do
  let sv := SystemVerilogNetlist.toSystemVerilogNetlist c
  let path := outDir / s!"{c.name}.sv"
  IO.FS.writeFile path.toString sv

-- Write C++ Simulation for a circuit (.h and .cpp)
def writeCircuitCppSim (c : Circuit) (allCircuits : List Circuit := [])
    (outDir : System.FilePath := System.FilePath.mk cppSimOutputDir) : IO Unit := do
  let header := CppSim.toCppSimHeader c allCircuits
  let impl := CppSim.toCppSimImpl c allCircuits
  let hPath := outDir / s!"{c.name}.h"
  let cppPath := outDir / s!"{c.name}.cpp"
  IO.FS.writeFile hPath.toString header
  IO.FS.writeFile cppPath.toString impl

-- Write PDK tech-mapped SystemVerilog for a circuit (only if keepHierarchy)
def writeCircuitPDK (pdk : PDK) (c : Circuit) (allCircuits : List Circuit := [])
    (precomputedLoaded : Std.HashMap String (Std.HashSet String) := {})
    (outDir : System.FilePath := System.FilePath.mk (pdkOutputDir pdk)) : IO Unit := do
  if c.keepHierarchy then
    let sv := CellNetlist.toSV (techMap pdk c) allCircuits precomputedLoaded
    let path := outDir / s!"{c.name}.sv"
    IO.FS.writeFile path.toString sv

/-- Every file writeCircuit emits for a circuit. -/
def emittedPaths (c : Circuit) (cfg : OutputConfig := {}) : List String :=
  [(cfg.svDir / s!"{c.name}.sv").toString,
   (cfg.netlistDir / s!"{c.name}.sv").toString,
   (cfg.cppSimDir / s!"{c.name}.h").toString,
   (cfg.cppSimDir / s!"{c.name}.cpp").toString]
  ++ (if c.keepHierarchy then
        [(cfg.asap7Dir / s!"{c.name}.sv").toString,
         (cfg.gf180Dir / s!"{c.name}.sv").toString]
      else [])

-- Write all output formats for a circuit
def writeCircuit (c : Circuit) (allCircuits : List Circuit := [])
    (precomputedLoaded : Std.HashMap String (Std.HashSet String) := {})
    (cfg : OutputConfig := {}) : IO Unit := do
  writeCircuitSV c allCircuits precomputedLoaded cfg.svDir
  writeCircuitNetlist c cfg.netlistDir
  writeCircuitCppSim c allCircuits cfg.cppSimDir
  for pdk in allPdks do
    let pDir := match pdk with
      | .asap7 => cfg.asap7Dir
      | .gf180mcu => cfg.gf180Dir
    writeCircuitPDK pdk c allCircuits precomputedLoaded pDir
  let pdkTag := if c.keepHierarchy then " +techmap" else ""
  IO.println s!"✓ Generated {c.name}: {c.gates.length} gates, {c.instances.length} instances{pdkTag}"

-- Verbose version with individual file confirmation
def writeCircuitVerbose (c : Circuit) (allCircuits : List Circuit := [])
    (cfg : OutputConfig := {}) : IO Unit := do
  writeCircuitSV c allCircuits {} cfg.svDir
  IO.println s!"  ✓ {c.name}.sv"

  writeCircuitNetlist c cfg.netlistDir
  IO.println s!"  ✓ {c.name}.sv (netlist)"

  writeCircuitCppSim c allCircuits cfg.cppSimDir
  IO.println s!"  ✓ {c.name}.h / {c.name}.cpp"

  IO.println s!"  ({c.gates.length} gates, {c.instances.length} instances)"

-- Write a filelist.f for a directory listing all files matching an extension
def writeFilelist (dir : System.FilePath) (ext : String) : IO Unit := do
  let entries ← try dir.readDir catch _ => pure #[]
  let files := entries.filter (fun e => e.fileName.endsWith ext)
  let sorted := files.toList.map (fun e => e.fileName) |>.mergeSort (· < ·)
  let content := String.intercalate "\n" sorted ++ "\n"
  IO.FS.writeFile (dir / "filelist.f").toString content

def physicalOutputDir : String := "physical"

/-- Write a physical synthesis filelist (.f) for a given synth wrapper.
    Prefers the target PDK's tech-mapped modules over the generic sv-from-lean
    modules, so a mapped module is never shadowed by its gate-level form. -/
def writePhysicalFilelist (wrapperName : String)
    (asap7Dir : System.FilePath := System.FilePath.mk (pdkOutputDir .asap7))
    (svDir : System.FilePath := System.FilePath.mk svOutputDir)
    (physDir : System.FilePath := System.FilePath.mk physicalOutputDir) : IO Unit := do
  let mappedEntries ← try asap7Dir.readDir catch _ => pure #[]
  let mappedFiles := mappedEntries.filter (fun e => e.fileName.endsWith ".sv")
  let mappedNames := mappedFiles.toList.map (fun e => e.fileName) |>.toArray
  let leanEntries ← try svDir.readDir catch _ => pure #[]
  let leanFiles := leanEntries.filter (fun e =>
    e.fileName.endsWith ".sv" && !mappedNames.contains e.fileName)
  let mappedPaths := mappedFiles.toList.map (fun e => (asap7Dir / e.fileName).toString)
  let leanPaths := leanFiles.toList.map (fun e => (svDir / e.fileName).toString)
  let allPaths := (mappedPaths ++ leanPaths).mergeSort (· < ·)
    |>.append [(physDir / s!"{wrapperName}.sv").toString]
  let content := String.intercalate "\n" allPaths ++ "\n"
  IO.FS.writeFile (physDir / s!"{wrapperName}.f").toString content

/-- Delete stale generated files.

    Files in the generated-output directories whose base name is not among
    `keepNames` and whose contents carry a code-generation marker are removed.
    This keeps removed or renamed modules (for example a renamed CPU top or a resized
    register) from lingering in the build filelists and breaking elaboration. -/
def pruneStaleOutputs (keepNames : List String) (cfg : OutputConfig := {}) : IO Unit := do
  -- Match case-insensitively: generators emit "Generated by", "Auto-generated", and more.
  let markers := ["generated by", "auto-generated", "do not edit", "generated from",
                  "generated systemverilog", "generated risc-v", "eval_comb_all", "comb_logic"]
  let dirs := [cfg.svDir, cfg.netlistDir, cfg.cppSimDir, cfg.asap7Dir, cfg.gf180Dir]
  for dir in dirs do
    let entries ← try dir.readDir catch _ => pure #[]
    for e in entries do
      let name := e.fileName
      if name == "filelist.f" then continue
      let base := (name.takeWhile (· != '.')).toString
      if keepNames.contains base then continue
      let path := dir / name
      let content ← (try IO.FS.readFile path.toString catch _ => pure "")
      let lower := content.toLower
      if markers.any (lower.contains ·) then
        IO.FS.removeFile path.toString
        IO.println s!"  pruned stale output: {path}"

-- Initialize output directories
def initOutputDirs (cfg : OutputConfig := {}) : IO Unit := do
  IO.FS.createDirAll cfg.svDir
  IO.FS.createDirAll cfg.netlistDir
  IO.FS.createDirAll cfg.cppSimDir
  IO.FS.createDirAll cfg.asap7Dir
  IO.FS.createDirAll cfg.gf180Dir

-- Write SystemVerilog testbench for a TestbenchConfig
def writeTestbenchSV (cfg : Testbench.TestbenchConfig)
    (outDir : System.FilePath := System.FilePath.mk "testbench/generated") : IO Unit :=
  Testbench.writeTestbenchSV cfg outDir

-- Write C++ simulation testbench for a TestbenchConfig
def writeTestbenchCppSim (cfg : Testbench.TestbenchConfig)
    (outDir : System.FilePath := System.FilePath.mk "testbench/generated") : IO Unit :=
  Testbench.writeTestbenchCppSim cfg outDir

-- Write both testbenches
def writeTestbenches (cfg : Testbench.TestbenchConfig)
    (outDir : System.FilePath := System.FilePath.mk "testbench/generated") : IO Unit :=
  Testbench.writeTestbenches cfg outDir

end Shoumei.Codegen.Unified
