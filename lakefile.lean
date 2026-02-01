import Lake
open Lake DSL

package «Shoumei» where
  -- Package configuration for Shoumei RTL
  -- Lake version: compatible with Lean 4.x

  -- Linter configuration: make warnings errors
  moreLeanArgs := #[
    "-DwarningAsError=true"  -- Treat all warnings as errors
  ]

lean_lib «Shoumei» where
  -- Main library containing DSL, semantics, theorems, and code generators
  srcDir := "lean"

-- Executable target for code generation
-- Runs code generators to produce SystemVerilog and Chisel output
@[default_target]
lean_exe codegen where
  root := `Main
  supportInterpreter := true

-- Executable target for testing RISC-V parser
lean_exe test_riscv where
  root := `TestRISCVParser
  supportInterpreter := true

-- Executable target for generating RV32I decoder (SystemVerilog + Chisel)
lean_exe generate_riscv_decoder where
  root := `GenerateRISCVDecoder
  supportInterpreter := true

-- Executable target for generating binary decoders (5→32, 6→64)
lean_exe generate_decoder where
  root := `GenerateDecoder
  supportInterpreter := true

-- Executable target for generating MuxTree variants (2:1, 4:1, 32:1, 64:1)
lean_exe generate_muxtree where
  root := `GenerateMuxTree
  supportInterpreter := true
