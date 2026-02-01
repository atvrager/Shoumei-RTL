/-
RISCV/Renaming/PhysRegFileCodegen.lean - Code generation for Physical Register File

Generates SystemVerilog and Chisel output for the PRF circuit and its
submodules (Decoder6, Mux64x32).
-/

import Shoumei.DSL
import Shoumei.Codegen.SystemVerilog
import Shoumei.Codegen.Chisel
import Shoumei.RISCV.Renaming.PhysRegFile
import Shoumei.Circuits.Combinational.Decoder
import Shoumei.Circuits.Combinational.MuxTree

namespace Shoumei.RISCV.Renaming.PhysRegFileCodegen

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

/-- Helper: Compute log2 ceiling -/
private def log2Ceil (n : Nat) : Nat :=
  if n <= 1 then 0
  else Nat.log2 n + (if 2^(Nat.log2 n) < n then 1 else 0)

def generatePhysRegFile : IO Unit := do
  IO.println "Generating PhysRegFile (Physical Register File)..."

  let numRegs := 64
  let dataWidth := 32
  let tagWidth := log2Ceil numRegs  -- 6

  -- Generate top-level PRF circuit
  let prf := mkPhysRegFile64
  writeCircuit prf

  -- Generate submodules
  -- (These may already exist from earlier phases, but regenerate to be safe)
  let dec := mkDecoder tagWidth
  writeCircuit dec

  let mux := mkMuxTree numRegs dataWidth
  writeCircuit mux

  IO.println "  PhysRegFile generation complete."

def main : IO Unit := do
  generatePhysRegFile

end Shoumei.RISCV.Renaming.PhysRegFileCodegen
