import Shoumei.Circuits.Combinational.Decoder
import Shoumei.Codegen.SystemVerilog
import Shoumei.Codegen.Chisel

open Shoumei.Circuits.Combinational
open Shoumei.Codegen

def main : IO Unit := do
  let svDir := "output/sv-from-lean"
  let chiselDir := "chisel/src/main/scala/generated"

  -- Generate for Decoder2 (small test)
  IO.println "Generating Decoder2..."
  let sv2 := SystemVerilog.toSystemVerilog mkDecoder2
  IO.FS.writeFile (svDir ++ "/Decoder2.sv") sv2
  let chisel2 := Chisel.toChisel mkDecoder2
  IO.FS.writeFile (chiselDir ++ "/Decoder2.scala") chisel2

  -- Generate for Decoder3
  IO.println "Generating Decoder3..."
  let sv3 := SystemVerilog.toSystemVerilog mkDecoder3
  IO.FS.writeFile (svDir ++ "/Decoder3.sv") sv3
  let chisel3 := Chisel.toChisel mkDecoder3
  IO.FS.writeFile (chiselDir ++ "/Decoder3.scala") chisel3

  -- Generate for Decoder5 (for RAT)
  IO.println "Generating Decoder5..."
  let sv5 := SystemVerilog.toSystemVerilog mkDecoder5
  IO.FS.writeFile (svDir ++ "/Decoder5.sv") sv5
  let chisel5 := Chisel.toChisel mkDecoder5
  IO.FS.writeFile (chiselDir ++ "/Decoder5.scala") chisel5

  IO.println "Done! Generated SystemVerilog and Chisel for decoders."
