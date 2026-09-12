/-
RippleCarryAdderCodegen.lean - Code Generation for Ripple-Carry Adders

Generates SystemVerilog code for RCA circuits.
-/

import Shoumei.Circuits.Combinational.RippleCarryAdder
import Shoumei.Codegen.SystemVerilog

namespace Shoumei.Circuits.Combinational

open Shoumei

-- Generate SystemVerilog for RippleCarryAdder4
def generateRCA4SystemVerilog : String :=
  Codegen.SystemVerilog.toSystemVerilog mkRippleCarryAdder4

-- Generate SystemVerilog for RippleCarryAdder8
def generateRCA8SystemVerilog : String :=
  Codegen.SystemVerilog.toSystemVerilog mkRippleCarryAdder8

-- Generate SystemVerilog for RippleCarryAdder32
def generateRCA32SystemVerilog : String :=
  Codegen.SystemVerilog.toSystemVerilog mkRippleCarryAdder32

-- Write RCA4 SystemVerilog to file
def writeRCA4SystemVerilog : IO Unit := do
  let sv := generateRCA4SystemVerilog
  let path := "output/sv-from-lean/RippleCarryAdder4.sv"
  IO.FS.writeFile path sv
  IO.println s!"✓ Generated: {path}"

-- Write RCA8 SystemVerilog to file
def writeRCA8SystemVerilog : IO Unit := do
  let sv := generateRCA8SystemVerilog
  let path := "output/sv-from-lean/RippleCarryAdder8.sv"
  IO.FS.writeFile path sv
  IO.println s!"✓ Generated: {path}"

-- Write RCA32 SystemVerilog to file
def writeRCA32SystemVerilog : IO Unit := do
  let sv := generateRCA32SystemVerilog
  let path := "output/sv-from-lean/RippleCarryAdder32.sv"
  IO.FS.writeFile path sv
  IO.println s!"✓ Generated: {path}"

-- Main entry point for RCA code generation
def generateRippleCarryAdders : IO Unit := do
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "  Phase 1: Ripple-Carry Adders"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println ""

  IO.println "==> RippleCarryAdder4 (4-bit, 20 gates)"
  writeRCA4SystemVerilog
  IO.println ""

  IO.println "==> RippleCarryAdder8 (8-bit, 40 gates)"
  writeRCA8SystemVerilog
  IO.println ""

  IO.println "==> RippleCarryAdder32 (32-bit, 160 gates)"
  writeRCA32SystemVerilog
  IO.println ""

  IO.println "✓ Ripple-Carry Adder code generation complete"

end Shoumei.Circuits.Combinational
