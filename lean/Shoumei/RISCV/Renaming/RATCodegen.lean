/-
RISCV/Renaming/RATCodegen.lean - Code generation for RAT

Generates SystemVerilog and Chisel output for the RAT circuit and its
submodules (Decoder5, Mux32x6).
-/

import Shoumei.DSL
import Shoumei.Codegen.SystemVerilog
import Shoumei.Codegen.Chisel
import Shoumei.RISCV.Renaming.RAT
import Shoumei.Circuits.Combinational.Decoder
import Shoumei.Circuits.Combinational.MuxTree

namespace Shoumei.RISCV.Renaming.RATCodegen

open Shoumei
open Shoumei.Codegen
open Shoumei.Circuits.Combinational
open Shoumei.RISCV.Renaming

def writeCircuit (c : Circuit) : IO Unit := do
  let sv := SystemVerilog.toSystemVerilog c
  let chisel := Chisel.toChisel c

  let svPath := s!"output/sv-from-lean/{c.name}.sv"
  let chiselPath := s!"chisel/src/main/scala/generated/{c.name}.scala"

  IO.FS.writeFile svPath sv
  IO.FS.writeFile chiselPath chisel

  IO.println s!"  Generated {c.name}: {c.gates.length} gates, {c.instances.length} instances"

def generateRAT : IO Unit := do
  IO.println "Generating RAT (Register Alias Table)..."

  -- Generate the RAT top-level
  let rat := mkRAT64
  writeCircuit rat

  -- Generate submodules: Decoder5 and Mux32x6
  -- (These may already exist from earlier phases, but regenerate to be safe)
  let dec5 := mkDecoder 5
  writeCircuit dec5

  let mux32x6 := mkMuxTree 32 6
  writeCircuit mux32x6

  IO.println "  RAT generation complete."

def main : IO Unit := do
  generateRAT

end Shoumei.RISCV.Renaming.RATCodegen
