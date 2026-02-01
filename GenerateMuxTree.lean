import Shoumei.Circuits.Combinational.MuxTree
import Shoumei.Codegen.SystemVerilog
import Shoumei.Codegen.Chisel

open Shoumei.Circuits.Combinational
open Shoumei.Codegen

def main : IO Unit := do
  let svDir := "output/sv-from-lean"
  let chiselDir := "chisel/src/main/scala/generated"

  IO.println "証明 Shoumei RTL - MuxTree Code Generator"
  IO.println "=========================================="
  IO.println ""

  -- Mux2x8
  IO.println "Generating Mux2x8..."
  let sv2x8 := SystemVerilog.toSystemVerilog mkMux2x8
  IO.FS.writeFile (svDir ++ "/Mux2x8.sv") sv2x8
  let chisel2x8 := Chisel.toChisel mkMux2x8
  IO.FS.writeFile (chiselDir ++ "/Mux2x8.scala") chisel2x8
  IO.println "✓ Mux2x8 generated"

  -- Mux4x8
  IO.println "Generating Mux4x8..."
  let sv4x8 := SystemVerilog.toSystemVerilog mkMux4x8
  IO.FS.writeFile (svDir ++ "/Mux4x8.sv") sv4x8
  let chisel4x8 := Chisel.toChisel mkMux4x8
  IO.FS.writeFile (chiselDir ++ "/Mux4x8.scala") chisel4x8
  IO.println "✓ Mux4x8 generated"

  -- Mux32x6
  IO.println "Generating Mux32x6..."
  let sv32x6 := SystemVerilog.toSystemVerilog mkMux32x6
  IO.FS.writeFile (svDir ++ "/Mux32x6.sv") sv32x6
  let chisel32x6 := Chisel.toChisel mkMux32x6
  IO.FS.writeFile (chiselDir ++ "/Mux32x6.scala") chisel32x6
  IO.println "✓ Mux32x6 generated"

  -- Mux64x32
  IO.println "Generating Mux64x32..."
  let sv64x32 := SystemVerilog.toSystemVerilog mkMux64x32
  IO.FS.writeFile (svDir ++ "/Mux64x32.sv") sv64x32
  let chisel64x32 := Chisel.toChisel mkMux64x32
  IO.FS.writeFile (chiselDir ++ "/Mux64x32.scala") chisel64x32
  IO.println "✓ Mux64x32 generated"

  IO.println ""
  IO.println "✓ All MuxTree variants generated successfully"
