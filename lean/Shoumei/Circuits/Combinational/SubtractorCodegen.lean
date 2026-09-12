/-
SubtractorCodegen.lean - Code Generation for Subtractors

Generates SystemVerilog code for Subtractor circuits.
-/

import Shoumei.Circuits.Combinational.Subtractor
import Shoumei.Codegen.SystemVerilog

namespace Shoumei.Circuits.Combinational

open Shoumei

-- Generate SystemVerilog for Subtractor4
def generateSubtractor4SystemVerilog : String :=
  Codegen.SystemVerilog.toSystemVerilog mkSubtractor4

-- Generate SystemVerilog for Subtractor8
def generateSubtractor8SystemVerilog : String :=
  Codegen.SystemVerilog.toSystemVerilog mkSubtractor8

-- Generate SystemVerilog for Subtractor32
def generateSubtractor32SystemVerilog : String :=
  Codegen.SystemVerilog.toSystemVerilog mkSubtractor32

-- Write Subtractor4 SystemVerilog to file
def writeSubtractor4SystemVerilog : IO Unit := do
  let sv := generateSubtractor4SystemVerilog
  let path := "output/sv-from-lean/Subtractor4.sv"
  IO.FS.writeFile path sv
  IO.println s!"✓ Generated: {path}"

-- Write Subtractor8 SystemVerilog to file
def writeSubtractor8SystemVerilog : IO Unit := do
  let sv := generateSubtractor8SystemVerilog
  let path := "output/sv-from-lean/Subtractor8.sv"
  IO.FS.writeFile path sv
  IO.println s!"✓ Generated: {path}"

-- Write Subtractor32 SystemVerilog to file
def writeSubtractor32SystemVerilog : IO Unit := do
  let sv := generateSubtractor32SystemVerilog
  let path := "output/sv-from-lean/Subtractor32.sv"
  IO.FS.writeFile path sv
  IO.println s!"✓ Generated: {path}"

-- Main entry point for Subtractor code generation
def generateSubtractors : IO Unit := do
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "  Phase 1: Subtractors (2's Complement)"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println ""

  IO.println "==> Subtractor4 (4-bit, 24 gates: 4 NOT + 20 RCA)"
  writeSubtractor4SystemVerilog
  IO.println ""

  IO.println "==> Subtractor8 (8-bit, 48 gates: 8 NOT + 40 RCA)"
  writeSubtractor8SystemVerilog
  IO.println ""

  IO.println "==> Subtractor32 (32-bit, 192 gates: 32 NOT + 160 RCA)"
  writeSubtractor32SystemVerilog
  IO.println ""

  IO.println "✓ Subtractor code generation complete"

end Shoumei.Circuits.Combinational
