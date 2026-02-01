/-
RippleCarryAdderCodegen.lean - Code Generation for Ripple-Carry Adders

Generates SystemVerilog and Chisel code for RCA circuits.
-/

import Shoumei.Circuits.Combinational.RippleCarryAdder
import Shoumei.Codegen.SystemVerilog
import Shoumei.Codegen.Chisel

namespace Shoumei.Circuits.Combinational

open Shoumei

-- Generate SystemVerilog for RippleCarryAdder4
def generateRCA4SystemVerilog : String :=
  Codegen.SystemVerilog.toSystemVerilog mkRippleCarryAdder4

-- Generate Chisel for RippleCarryAdder4
def generateRCA4Chisel : String :=
  Codegen.Chisel.toChisel mkRippleCarryAdder4

-- Generate SystemVerilog for RippleCarryAdder8
def generateRCA8SystemVerilog : String :=
  Codegen.SystemVerilog.toSystemVerilog mkRippleCarryAdder8

-- Generate Chisel for RippleCarryAdder8
def generateRCA8Chisel : String :=
  Codegen.Chisel.toChisel mkRippleCarryAdder8

-- Generate SystemVerilog for RippleCarryAdder32
def generateRCA32SystemVerilog : String :=
  Codegen.SystemVerilog.toSystemVerilog mkRippleCarryAdder32

-- Generate Chisel for RippleCarryAdder32
def generateRCA32Chisel : String :=
  Codegen.Chisel.toChisel mkRippleCarryAdder32

-- Write RCA4 SystemVerilog to file
def writeRCA4SystemVerilog : IO Unit := do
  let sv := generateRCA4SystemVerilog
  let path := "output/sv-from-lean/RippleCarryAdder4.sv"
  IO.FS.writeFile path sv
  IO.println s!"✓ Generated: {path}"

-- Write RCA4 Chisel to file
def writeRCA4Chisel : IO Unit := do
  let chisel := generateRCA4Chisel
  let path := "output/chisel-src/RippleCarryAdder4.scala"
  IO.FS.writeFile path chisel
  IO.FS.writeFile "chisel/src/main/scala/generated/RippleCarryAdder4.scala" chisel
  IO.println s!"✓ Generated: {path}"

-- Write RCA8 SystemVerilog to file
def writeRCA8SystemVerilog : IO Unit := do
  let sv := generateRCA8SystemVerilog
  let path := "output/sv-from-lean/RippleCarryAdder8.sv"
  IO.FS.writeFile path sv
  IO.println s!"✓ Generated: {path}"

-- Write RCA8 Chisel to file
def writeRCA8Chisel : IO Unit := do
  let chisel := generateRCA8Chisel
  let path := "output/chisel-src/RippleCarryAdder8.scala"
  IO.FS.writeFile path chisel
  IO.FS.writeFile "chisel/src/main/scala/generated/RippleCarryAdder8.scala" chisel
  IO.println s!"✓ Generated: {path}"

-- Write RCA32 SystemVerilog to file
def writeRCA32SystemVerilog : IO Unit := do
  let sv := generateRCA32SystemVerilog
  let path := "output/sv-from-lean/RippleCarryAdder32.sv"
  IO.FS.writeFile path sv
  IO.println s!"✓ Generated: {path}"

-- Write RCA32 Chisel to file
def writeRCA32Chisel : IO Unit := do
  let chisel := generateRCA32Chisel
  let path := "output/chisel-src/RippleCarryAdder32.scala"
  IO.FS.writeFile path chisel
  IO.FS.writeFile "chisel/src/main/scala/generated/RippleCarryAdder32.scala" chisel
  IO.println s!"✓ Generated: {path}"

-- Main entry point for RCA code generation
def generateRippleCarryAdders : IO Unit := do
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "  Phase 1: Ripple-Carry Adders"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println ""

  IO.println "==> RippleCarryAdder4 (4-bit, 20 gates)"
  writeRCA4SystemVerilog
  writeRCA4Chisel
  IO.println ""

  IO.println "==> RippleCarryAdder8 (8-bit, 40 gates)"
  writeRCA8SystemVerilog
  writeRCA8Chisel
  IO.println ""

  IO.println "==> RippleCarryAdder32 (32-bit, 160 gates)"
  writeRCA32SystemVerilog
  writeRCA32Chisel
  IO.println ""

  IO.println "✓ Ripple-Carry Adder code generation complete"

end Shoumei.Circuits.Combinational
