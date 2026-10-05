/-
GenerateLeaves.lean - Code Generator for Leaf Subsystems

Emits SystemVerilog, flat netlist, PDK tech-mapped SV, and C++ simulation
models for foundation, combinational, and sequential subsystems.
-/

import Shoumei.Codegen.Unified
import Shoumei.LeafRegistry

open Shoumei.Codegen.Unified
open Shoumei.LeafRegistry

def parseArg (pfx : String) (args : List String) : Option String :=
  args.findSome? (fun a =>
    if a.startsWith pfx then some (a.drop pfx.length).toString else none)

def main (args : List String) : IO Unit := do
  let outSv := parseArg "--out-sv=" args |>.map System.FilePath.mk
    |>.getD (System.FilePath.mk "output/sv-from-lean")
  let outNetlist := parseArg "--out-netlist=" args |>.map System.FilePath.mk
    |>.getD (System.FilePath.mk "output/sv-netlist")
  let outCppSim := parseArg "--out-cpp-sim=" args |>.map System.FilePath.mk
    |>.getD (System.FilePath.mk "output/cpp_sim")
  let outAsap7 := parseArg "--out-asap7=" args |>.map System.FilePath.mk
    |>.getD (System.FilePath.mk "output/sv-asap7")
  let outGf180 := parseArg "--out-gf180=" args |>.map System.FilePath.mk
    |>.getD (System.FilePath.mk "output/sv-gf180")
  let subsystemOpt := parseArg "--subsystem=" args
  let circuitOpt := parseArg "--circuit=" args

  let cfg : OutputConfig := {
    svDir := outSv,
    netlistDir := outNetlist,
    cppSimDir := outCppSim,
    asap7Dir := outAsap7,
    gf180Dir := outGf180
  }

  IO.FS.createDirAll cfg.svDir
  IO.FS.createDirAll cfg.netlistDir
  IO.FS.createDirAll cfg.cppSimDir
  IO.FS.createDirAll cfg.asap7Dir
  IO.FS.createDirAll cfg.gf180Dir

  let selectedCircuits : List Circuit ← match circuitOpt with
    | some name =>
      match leafCircuits.find? (fun (c : Circuit) => c.name == name) with
      | some c => pure [c]
      | none =>
        IO.eprintln s!"Unknown circuit in leaf registry: {name}"
        IO.Process.exit 1
    | none =>
      match subsystemOpt with
      | some sub =>
        match leafCircuitsForSubsystem sub with
        | some cs => pure cs
        | none =>
          IO.eprintln s!"Unknown leaf subsystem: {sub}"
          IO.Process.exit 1
      | none => pure leafCircuits

  let bannerSub := subsystemOpt.getD "leaves"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println s!"  証明 Shoumei RTL - Code Generation ({bannerSub})"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println ""

  let mut count := 0
  for c in selectedCircuits do
    writeCircuit c leafCircuits {} cfg
    count := count + 1

  IO.println ""
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println s!"✓ Generated {count} circuits"
  IO.println s!"  SV:      {cfg.svDir}"
  IO.println s!"  Netlist: {cfg.netlistDir}"
  IO.println s!"  C++ Sim: {cfg.cppSimDir}"
  IO.println s!"  ASAP7:   {cfg.asap7Dir}"
  IO.println s!"  GF180:   {cfg.gf180Dir}"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
