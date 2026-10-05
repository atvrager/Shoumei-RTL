/-
GenerateAll.lean - Centralized Code Generation for All Circuits

Single entry point for generating all circuits in the project.
Just add your circuit here and it gets all 3 output formats automatically.

Usage: lake exe generate_all
-/

import Shoumei.Codegen.Unified
import Shoumei.Codegen.SECMiter
import Shoumei.Components.Select
import Shoumei.Verification.ExportCerts
import Shoumei.DSL.PortResolve
import Shoumei.Verification.DualRTL
import Shoumei.CircuitRegistry
import Shoumei.Circuits.Sequential.Register

import Shoumei.RISCV.CodegenTest
import Shoumei.RISCV.CPUTestbench
import Shoumei.RISCV.TraceSchema
import Shoumei.RISCV.Config

open Shoumei.CircuitRegistry
open Shoumei.Codegen.Unified
open Shoumei.Circuits.Sequential
open Shoumei.RISCV
open Shoumei.RISCV.CPUTestbench

def parseArg (pfx : String) (args : List String) : Option String :=
  args.findSome? (fun a =>
    if a.startsWith pfx then some (a.drop pfx.length).toString else none)

def main (args : List String) : IO Unit := do
  -- The circuit registry below is also the certificate registry: a
  -- compositional certificate is only meaningful for a circuit that is actually
  -- emitted.  `--export-certs` prints that registry, validating as it goes, and
  -- exits without generating anything.
  if args.contains "--export-certs" then
    Shoumei.Verification.ExportCerts.printCertificates allCircuits riscvDecoderModules
    return
  if args.contains "--export-refinements" then
    IO.eprintln "Refinements export is disabled in generate_all to keep code generation fast."
    IO.Process.exit 1
  if args.contains "--export-sec-manifest" || args.contains "--sec-manifest" then
    Shoumei.Verification.DualRTL.printManifest allCircuits
    return
  if args.contains "--check-sec-specs" then
    let rc ← Shoumei.Verification.DualRTL.checkSpecs allCircuits
    if rc != 0 then IO.Process.exit rc.toUInt8
    return
  if args.contains "--check-drivers" then
    let clashes := Shoumei.DSL.PortResolve.checkRegistryDrivers allCircuits
    if clashes.isEmpty then
      IO.println s!"✓ No wire in {allCircuits.length} circuits has more than one driver"
      return
    else
      IO.eprintln s!"✗ Driver check failed: {clashes.length} multiply-driven wires:"
      for c in clashes do
        IO.eprintln s!"  {c.moduleName}: {c.wireName} ({c.drivers} drivers)"
      IO.Process.exit 1
  if args.contains "--check-wiring" then
    let missing := Shoumei.DSL.PortResolve.checkRegistryWiring allCircuits
    if missing.isEmpty then
      IO.println s!"✓ All {allCircuits.length} circuits are WellWired (0 unconnected instance inputs)"
      return
    else
      IO.eprintln s!"✗ Wiring check failed: {missing.length} unconnected instance inputs found:"
      for m in missing do
        IO.eprintln s!"  {m.parentModule} / {m.childModule} {m.instName}: {m.portWire.name}"
      IO.Process.exit 1

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
  let outSec := parseArg "--out-sec=" args |>.map System.FilePath.mk
    |>.getD (System.FilePath.mk "output/sv-sec")
  let outTestbench := parseArg "--out-testbench=" args |>.map System.FilePath.mk
    |>.getD (System.FilePath.mk "testbench/generated")
  let outConfigMk := parseArg "--out-config-mk=" args |>.map System.FilePath.mk
    |>.getD (System.FilePath.mk "output/config.mk")
  let outPhysical := parseArg "--out-physical=" args |>.map System.FilePath.mk
    |>.getD (System.FilePath.mk "physical")
  let instrDict := parseArg "--instr-dict=" args |>.map System.FilePath.mk
    |>.getD Shoumei.RISCV.instrDictPath
  let subsystemOpt := parseArg "--subsystem=" args
  let circuitOpt := parseArg "--circuit=" args
  let skipTestbench := args.contains "--skip-testbench"
  let skipSec := args.contains "--skip-sec"
  let skipDecoders := args.contains "--skip-decoders"

  let cfg : OutputConfig := {
    svDir := outSv,
    netlistDir := outNetlist,
    cppSimDir := outCppSim,
    asap7Dir := outAsap7,
    gf180Dir := outGf180,
    secDir := outSec,
    testbenchDir := outTestbench,
    configMkPath := outConfigMk,
    physicalDir := outPhysical,
    instrDictPath := instrDict
  }

  let selectedCircuits : List Circuit ← match circuitOpt with
    | some name =>
      match allCircuits.find? (fun (c : Circuit) => c.name == name) with
      | some c => pure [c]
      | none =>
        IO.eprintln s!"Unknown circuit: {name}"
        IO.Process.exit 1
    | none =>
      match subsystemOpt with
      | some sub =>
        match circuitsForSubsystem sub with
        | some cs => pure cs
        | none =>
          IO.eprintln s!"Unknown subsystem: {sub}"
          IO.Process.exit 1
      | none => pure allCircuits

  let isAllSubsystem := subsystemOpt.isNone || subsystemOpt == some "all"

  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  let subTag := match subsystemOpt with
    | some s => s!" ({s})"
    | none => ""
  IO.println s!"  証明 Shoumei RTL - Code Generation{subTag}"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println ""

  -- A wire with two drivers is a modelling error that proofs do not catch: the
  -- emitted SystemVerilog just gets two continuous assignments for the net. Fail
  -- before writing anything rather than ship a netlist whose value depends on
  -- evaluation order.
  let driverClashes := Shoumei.DSL.PortResolve.checkRegistryDrivers allCircuits
  if !driverClashes.isEmpty then
    IO.eprintln s!"✗ {driverClashes.length} wire(s) are driven more than once; refusing to generate:"
    for c in driverClashes do
      IO.eprintln s!"  {c.moduleName}: {c.wireName} ({c.drivers} drivers)"
    IO.eprintln "  Each wire is a single net, so a second driver silently overrides the first."
    IO.Process.exit 1

  -- Initialize output directories
  initOutputDirs cfg

  -- Pre-compute loaded-wire map
  let loadedMap := Shoumei.Codegen.SystemVerilog.computeAllLoadedWires allCircuits

  -- Generate circuits
  let mut count := 0
  for c in selectedCircuits do
    writeCircuit c allCircuits loadedMap cfg
    count := count + 1

  -- Generate RISC-V decoders
  if (isAllSubsystem || subsystemOpt == some "decoders") && circuitOpt.isNone && !skipDecoders then
    IO.println ""
    IO.println "Generating RISC-V decoders..."
    let opcodesPath := cfg.instrDictPath
    unless (← opcodesPath.pathExists) do
      IO.eprintln s!"instr_dict.json is missing at {opcodesPath}"
      IO.eprintln "Build it with: bazel build //generators:instr_dict"
      IO.Process.exit 1
    let defs ← Shoumei.RISCV.loadInstrDictFromFile opcodesPath
    Shoumei.RISCV.generateDecoders defs riscvDecoderModules cfg.svDir cfg.cppSimDir

  -- Generate testbenches
  if (isAllSubsystem || subsystemOpt == some "testbench") && circuitOpt.isNone && !skipTestbench then
    IO.println ""
    IO.println "Generating testbenches..."
    writeTestbenches cpuTestbenchConfig cfg.testbenchDir
    IO.println ""
    IO.println "Generating config.mk..."
    let cpuCfg := defaultCPUConfig
    let configMk := s!"# Auto-generated by generate_all — do not edit\n" ++
      s!"CPU_NAME := {cpuCfg.isaString}\n" ++
      s!"SPIKE_ISA := {cpuCfg.spikeIsa}\n" ++
      s!"TB_MEM_SIZE := {cpuCfg.memSizeWords}\n" ++
      s!"TIMEOUT_CYCLES := {cpuCfg.timeoutCycles}\n" ++
      s!"NUM_PHYS_REGS := {cpuCfg.numPhysRegs}\n" ++
      s!"ROB_ENTRIES := {cpuCfg.robEntries}\n" ++
      s!"SB_ENTRIES := {cpuCfg.storeBufferEntries}\n" ++
      s!"RS_ENTRIES := {cpuCfg.rsEntries}\n"
    if let some parent := cfg.configMkPath.parent then
      IO.FS.createDirAll parent
    IO.FS.writeFile cfg.configMkPath.toString configMk
    IO.println s!"✓ Generated {cfg.configMkPath}"

    IO.println ""
    IO.println "Generating trace schema..."
    IO.FS.createDirAll cfg.testbenchDir
    IO.FS.writeFile (cfg.testbenchDir / "trace_schema.gen.h").toString
      Shoumei.TraceSchema.renderCHeader
    if ← System.FilePath.isDir "viewer/src" then
      IO.FS.writeFile "viewer/src/schema.gen.ts" Shoumei.TraceSchema.renderTsSchema
    IO.println "✓ Generated trace schema"

  -- Generate SEC miters and scripts
  if (isAllSubsystem || subsystemOpt == some "sec") && circuitOpt.isNone && !skipSec then
    IO.println ""
    IO.println "Generating SEC miters and verification scripts..."
    let secOutputDir := cfg.secDir
    IO.FS.createDirAll secOutputDir
    let miter160 := Shoumei.Codegen.SECMiter.generateSECMiter mkRegister160Flat
      mkRegister160Hierarchical "Register160_sec_miter"
    IO.FS.writeFile (secOutputDir / "Register160_sec_miter.sv").toString miter160
    let svDirStr := cfg.svDir.toString
    let secDirStr := cfg.secDir.toString
    let formality160 := Shoumei.Codegen.SECMiter.generateFormalityTcl "Register160Flat" "Register160"
      [s!"{svDirStr}/Register160Flat.sv"]
      [s!"{svDirStr}/Register64.sv", s!"{svDirStr}/Register32.sv", s!"{svDirStr}/Register160.sv"]
    IO.FS.writeFile (secOutputDir / "Register160_formality.tcl").toString formality160
    let yosys160 := Shoumei.Codegen.SECMiter.generateYosysTcl "Register160Flat" "Register160"
      [s!"{svDirStr}/Register160Flat.sv", s!"{svDirStr}/Register64.sv", s!"{svDirStr}/Register32.sv",
       s!"{svDirStr}/Register160.sv"]
    IO.FS.writeFile (secOutputDir / "Register160_yosys.tcl").toString yosys160
    let vcFormal160 := Shoumei.Codegen.SECMiter.generateVCFormalTcl "Register160_sec_miter"
      [s!"{svDirStr}/Register160Flat.sv", s!"{svDirStr}/Register64.sv", s!"{svDirStr}/Register32.sv",
       s!"{svDirStr}/Register160.sv", s!"{secDirStr}/Register160_sec_miter.sv"]
    IO.FS.writeFile (secOutputDir / "Register160_vc_formal.tcl").toString vcFormal160
    let svaFormal160 := Shoumei.Codegen.SECMiter.generateVCFormalTcl "Register160"
      [s!"{svDirStr}/Register64.sv", s!"{svDirStr}/Register32.sv", s!"{svDirStr}/Register160.sv"]
    IO.FS.writeFile (secOutputDir / "Register160_sva_formal.tcl").toString svaFormal160
    let svaFormalEn64 := Shoumei.Codegen.SECMiter.generateVCFormalTcl "RegisterEn64"
      [s!"{svDirStr}/RegisterEn64.sv"]
    IO.FS.writeFile (secOutputDir / "RegisterEn64_sva_formal.tcl").toString svaFormalEn64
    let svaFormalLogicUnit32 := Shoumei.Codegen.SECMiter.generateVCFormalTcl "LogicUnit32"
      [s!"{svDirStr}/LogicUnit32.sv"] "clock" "reset" (hasClock := false)
    IO.FS.writeFile (secOutputDir / "LogicUnit32_sva_formal.tcl").toString svaFormalLogicUnit32
    let svaFormalLogicUnit64 := Shoumei.Codegen.SECMiter.generateVCFormalTcl "LogicUnit64"
      [s!"{svDirStr}/LogicUnit64.sv"] "clock" "reset" (hasClock := false)
    IO.FS.writeFile (secOutputDir / "LogicUnit64_sva_formal.tcl").toString svaFormalLogicUnit64
    let svaFormalMux4x32 := Shoumei.Codegen.SECMiter.generateVCFormalTcl "Mux4x32"
      [s!"{svDirStr}/Mux4x32.sv"] "clock" "reset" (hasClock := false)
    IO.FS.writeFile (secOutputDir / "Mux4x32_sva_formal.tcl").toString svaFormalMux4x32
    let svaFormalMux8x32 := Shoumei.Codegen.SECMiter.generateVCFormalTcl "Mux8x32"
      [s!"{svDirStr}/Mux4x32.sv", s!"{svDirStr}/Mux8x32.sv"] "clock" "reset" (hasClock := false)
    IO.FS.writeFile (secOutputDir / "Mux8x32_sva_formal.tcl").toString svaFormalMux8x32
    let svaFormalPopcount8 := Shoumei.Codegen.SECMiter.generateVCFormalTcl "Popcount8"
      [s!"{svDirStr}/Popcount8.sv"] "clock" "reset" (hasClock := false)
    IO.FS.writeFile (secOutputDir / "Popcount8_sva_formal.tcl").toString svaFormalPopcount8
    IO.println s!"✓ Generated SEC miters and scripts in {secOutputDir}"

  -- Prune stale generated files
  if isAllSubsystem && circuitOpt.isNone then
    IO.println ""
    IO.println "Pruning stale generated outputs..."
    pruneStaleOutputs emittedModuleNames cfg

    -- Generate filelist.f for each output directory
    IO.println ""
    IO.println "Generating filelists..."
    writeFilelist cfg.svDir ".sv"
    writeFilelist cfg.netlistDir ".sv"
    writeFilelist cfg.cppSimDir ".h"
    for pdk in allPdks do
      let pDir := match pdk with
        | .asap7 => cfg.asap7Dir
        | .gf180mcu => cfg.gf180Dir
      writeFilelist pDir ".sv"
    IO.println "✓ Generated filelist.f in each output directory"

    -- Generate physical synthesis filelists
    let physEntries ← try cfg.physicalDir.readDir catch _ => pure #[]
    let synthWrappers := physEntries.filter (fun e => e.fileName.endsWith "_synth.sv")
    if !synthWrappers.isEmpty then
      IO.println ""
      IO.println "Generating physical synthesis filelists..."
      for wrapper in synthWrappers do
        let name := (wrapper.fileName.take (wrapper.fileName.length - 3)).toString
        writePhysicalFilelist name cfg.asap7Dir cfg.svDir cfg.physicalDir
        IO.println s!"  ✓ {name}.f"
      IO.println s!"✓ Generated {synthWrappers.size} physical filelists"


  IO.println ""
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println s!"✓ Generated {count} circuits"
  IO.println s!"  SV:      {cfg.svDir}"
  IO.println s!"  Netlist: {cfg.netlistDir}"
  IO.println s!"  C++ Sim: {cfg.cppSimDir}"
  IO.println s!"  ASAP7:   {cfg.asap7Dir}"
  IO.println s!"  GF180:   {cfg.gf180Dir}"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
