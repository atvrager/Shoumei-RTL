/-
GenerateSec.lean - Standalone CLI for generating SEC miters and verification scripts.
-/

import Shoumei.Codegen.SECMiter
import Shoumei.Circuits.Sequential.Register

open Shoumei.Circuits.Sequential

def parseArg (pfx : String) (args : List String) : Option String :=
  args.findSome? (fun a =>
    if a.startsWith pfx then some (a.drop pfx.length).toString else none)

def main (args : List String) : IO Unit := do
  let outSec := parseArg "--out-sec=" args |>.map System.FilePath.mk
    |>.getD (System.FilePath.mk "output/sv-sec")
  let outSv := parseArg "--out-sv=" args |>.map System.FilePath.mk
    |>.getD (System.FilePath.mk "output/sv-from-lean")

  IO.println "Generating SEC miters and verification scripts..."
  let secOutputDir := outSec
  IO.FS.createDirAll secOutputDir
  let miter160 := Shoumei.Codegen.SECMiter.generateSECMiter mkRegister160Flat
    mkRegister160Hierarchical "Register160_sec_miter"
  IO.FS.writeFile (secOutputDir / "Register160_sec_miter.sv").toString miter160
  let svDirStr := outSv.toString
  let secDirStr := outSec.toString
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
