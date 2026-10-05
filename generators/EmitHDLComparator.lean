import Shoumei.Codegen.SystemVerilog
import Shoumei.HDL.Examples.EqualityComparator

def main : IO Unit := do
  let c20 := Shoumei.HDL.Examples.equalityComparatorCircuit 20
  let sv20 := Shoumei.Codegen.SystemVerilog.toSystemVerilog c20
  IO.FS.writeFile "/home/fedora/.gemini/antigravity-cli/brain/9c9d2cb9-df03-425b-8a5b-bd311034f0d9/scratch/EqualityComparator20_hdl.sv" sv20

  let c32 := Shoumei.HDL.Examples.equalityComparatorCircuit 32
  let sv32 := Shoumei.Codegen.SystemVerilog.toSystemVerilog c32
  IO.FS.writeFile "/home/fedora/.gemini/antigravity-cli/brain/9c9d2cb9-df03-425b-8a5b-bd311034f0d9/scratch/EqualityComparator32_hdl.sv" sv32

  let c64 := Shoumei.HDL.Examples.equalityComparatorCircuit 64
  let sv64 := Shoumei.Codegen.SystemVerilog.toSystemVerilog c64
  IO.FS.writeFile "/home/fedora/.gemini/antigravity-cli/brain/9c9d2cb9-df03-425b-8a5b-bd311034f0d9/scratch/EqualityComparator64_hdl.sv" sv64

  IO.println "✓ Emitted EqualityComparator20, 32, and 64 from high-level HDL"
