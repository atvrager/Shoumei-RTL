import Shoumei.Circuits.Combinational.Decoder
import Shoumei.Codegen.SystemVerilog

open Shoumei.Circuits.Combinational
open Shoumei.Codegen

def main : IO Unit := do
  let svDir := "output/sv-from-lean"

  -- Generate for Decoder2 (small test)
  IO.println "Generating Decoder2..."
  let sv2 := SystemVerilog.toSystemVerilog mkDecoder2
  IO.FS.writeFile (svDir ++ "/Decoder2.sv") sv2

  -- Generate for Decoder3
  IO.println "Generating Decoder3..."
  let sv3 := SystemVerilog.toSystemVerilog mkDecoder3
  IO.FS.writeFile (svDir ++ "/Decoder3.sv") sv3

  -- Generate for Decoder5 (for RAT)
  IO.println "Generating Decoder5..."
  let sv5 := SystemVerilog.toSystemVerilog mkDecoder5
  IO.FS.writeFile (svDir ++ "/Decoder5.sv") sv5

  IO.println "Done! Generated SystemVerilog for decoders."
