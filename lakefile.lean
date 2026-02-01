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

-- Executable target for testing SystemC code generation
lean_exe test_systemc where
  root := `TestSystemC
  supportInterpreter := true

-- Executable target for SystemC code generation (all 23 modules)
lean_exe codegen_systemc where
  root := `GenerateSystemC
  supportInterpreter := true

-- Executable target for generating QueueN variants (2:8, 4:8, 64:6, 64:32)
lean_exe generate_queuen where
  root := `GenerateQueueN
  supportInterpreter := true

-- Executable target for generating RAT (Register Alias Table) circuits
lean_exe generate_rat where
  root := `GenerateRAT
  supportInterpreter := true

-- Executable target for generating FreeList (Free Physical Register List)
lean_exe generate_freelist where
  root := `GenerateFreeList
  supportInterpreter := true

-- Executable target for generating PhysRegFile (Physical Register File)
lean_exe generate_physregfile where
  root := `GeneratePhysRegFile
  supportInterpreter := true

-- Executable target for exporting verification certificates
-- Generates compositional-certs.txt from Lean verification certificates
lean_exe export_verification_certs where
  root := `ExportVerificationCerts
  supportInterpreter := true
