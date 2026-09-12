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

-- Executable target for CENTRALIZED code generation
-- Generates ALL circuits in one command (SV + flat netlist + C++ Sim + testbenches)
-- This is the recommended way to generate code
@[default_target]
lean_exe generate_all where
  root := `GenerateAll
  supportInterpreter := true

-- Executable target for legacy code generation
-- (Use generate_all instead - it is simpler and emits every output format)
lean_exe codegen where
  root := `Main
  supportInterpreter := true

-- Executable target for testing RISC-V parser
lean_exe test_riscv where
  root := `TestRISCVParser
  supportInterpreter := true

-- Executable target for generating RV32I decoder (SystemVerilog + C++ sim)
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

-- Executable target for testing C++ simulation code generation
lean_exe test_cppsim where
  root := `TestCppSim
  supportInterpreter := true

-- Executable target for C++ simulation code generation (all modules)
lean_exe codegen_cppsim where
  root := `GenerateCppSim
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

-- Executable target for generating IntegerExecUnit (Integer Execution Unit)
lean_exe generate_integer_exec where
  root := `GenerateIntegerExecUnit
  supportInterpreter := true

-- Executable target for generating BranchExecUnit (Branch Execution Unit)
lean_exe generate_branch_exec where
  root := `GenerateBranchExecUnit
  supportInterpreter := true

-- Executable target for generating OpType enum from riscv-opcodes JSON
lean_exe generate_optype where
  root := `GenerateOpType
  supportInterpreter := true

-- Executable target for generating .shoumei text format files
lean_exe generate_shoumei where
  root := `GenerateShoumei
  supportInterpreter := true

-- Executable target for generating RISC-V test assembly (.S files)
lean_exe gen_tests where
  root := `GenTests
  supportInterpreter := true
