/-
SubtractorCodegen.lean - Code Generation for Subtractors

Generates SystemVerilog and Chisel code for Subtractor circuits.
-/

import Shoumei.Circuits.Combinational.Subtractor
import Shoumei.Codegen.SystemVerilog
import Shoumei.Codegen.Chisel

namespace Shoumei.Circuits.Combinational

open Shoumei

-- Generate SystemVerilog for Subtractor4
def generateSubtractor4SystemVerilog : String :=
  Codegen.SystemVerilog.toSystemVerilog mkSubtractor4

-- Generate Chisel for Subtractor4
def generateSubtractor4Chisel : String :=
  Codegen.Chisel.toChisel mkSubtractor4

-- Generate SystemVerilog for Subtractor8
def generateSubtractor8SystemVerilog : String :=
  Codegen.SystemVerilog.toSystemVerilog mkSubtractor8

-- Generate Chisel for Subtractor8
def generateSubtractor8Chisel : String :=
  Codegen.Chisel.toChisel mkSubtractor8

-- Generate SystemVerilog for Subtractor32
def generateSubtractor32SystemVerilog : String :=
  Codegen.SystemVerilog.toSystemVerilog mkSubtractor32

-- Generate Chisel for Subtractor32
def generateSubtractor32Chisel : String :=
  Codegen.Chisel.toChisel mkSubtractor32

-- Write Subtractor4 SystemVerilog to file
def writeSubtractor4SystemVerilog : IO Unit := do
  let sv := generateSubtractor4SystemVerilog
  let path := "output/sv-from-lean/Subtractor4.sv"
  IO.FS.writeFile path sv
  IO.println s!"✓ Generated: {path}"

-- Write Subtractor4 Chisel to file
def writeSubtractor4Chisel : IO Unit := do
  let chisel := generateSubtractor4Chisel
  let path := "chisel/src/main/scala/generated/Subtractor4.scala"
  IO.FS.writeFile path chisel
  IO.println s!"✓ Generated: {path}"

-- Write Subtractor8 SystemVerilog to file
def writeSubtractor8SystemVerilog : IO Unit := do
  let sv := generateSubtractor8SystemVerilog
  let path := "output/sv-from-lean/Subtractor8.sv"
  IO.FS.writeFile path sv
  IO.println s!"✓ Generated: {path}"

-- Write Subtractor8 Chisel to file
def writeSubtractor8Chisel : IO Unit := do
  let chisel := generateSubtractor8Chisel
  let path := "chisel/src/main/scala/generated/Subtractor8.scala"
  IO.FS.writeFile path chisel
  IO.println s!"✓ Generated: {path}"

-- Write Subtractor32 SystemVerilog to file
def writeSubtractor32SystemVerilog : IO Unit := do
  let sv := generateSubtractor32SystemVerilog
  let path := "output/sv-from-lean/Subtractor32.sv"
  IO.FS.writeFile path sv
  IO.println s!"✓ Generated: {path}"

-- Write Subtractor32 Chisel to file
def writeSubtractor32Chisel : IO Unit := do
  let chisel := generateSubtractor32Chisel
  let path := "chisel/src/main/scala/generated/Subtractor32.scala"
  IO.FS.writeFile path chisel
  IO.println s!"✓ Generated: {path}"

-- Main entry point for Subtractor code generation
def generateSubtractors : IO Unit := do
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "  Phase 1: Subtractors (2's Complement)"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println ""

  IO.println "==> Subtractor4 (4-bit, 24 gates: 4 NOT + 20 RCA)"
  writeSubtractor4SystemVerilog
  writeSubtractor4Chisel
  IO.println ""

  IO.println "==> Subtractor8 (8-bit, 48 gates: 8 NOT + 40 RCA)"
  writeSubtractor8SystemVerilog
  writeSubtractor8Chisel
  IO.println ""

  IO.println "==> Subtractor32 (32-bit, 192 gates: 32 NOT + 160 RCA)"
  writeSubtractor32SystemVerilog
  writeSubtractor32Chisel
  IO.println ""

  IO.println "✓ Subtractor code generation complete"

end Shoumei.Circuits.Combinational
