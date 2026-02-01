
import Shoumei.Circuits.Sequential.QueueComponents
import Shoumei.Codegen.SystemVerilog

open Shoumei.Circuits.Sequential
open Shoumei.Codegen

def main : IO Unit := do
  IO.println "Building QueueRAM 2 8..."
  let ram := mkQueueRAM 2 8
  IO.println "RAM built. Generating SV..."
  let sv := SystemVerilog.toSystemVerilog ram
  IO.println "SV generated."
  IO.println sv
