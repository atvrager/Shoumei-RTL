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
  -- Main library containing DSL, semantics, theorems, and code generators.
  --
  -- `Shoumei.All` imports every module in the tree (see
  -- `scripts/gen-lean-root.py`), so a plain `lake build` compiles all of it.
  -- Without that root, a module nothing else imports is never compiled and rots
  -- unnoticed: nineteen had, before this existed.
  srcDir := "lean"
  roots := #[`Shoumei, `Shoumei.All]

-- Executable target for CENTRALIZED code generation
-- Generates ALL circuits in one command (SV + flat netlist + C++ Sim + testbenches)
-- This is the recommended way to generate code
@[default_target]
lean_exe generate_all where
  root := `GenerateAll
  supportInterpreter := true

-- Executable target for emitting the adder calibration matrix (Step 8 tooling)
lean_exe generate_adder_matrix where
  root := `GenerateAdderMatrix
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

-- Executable target for generating the instruction benchmark suite.
-- Derives one benchmark program per decoder instruction (riscv-opcodes table)
-- and validates every sample encoding by decoding it back.
lean_exe gen_benchmarks where
  root := `GenBenchmarks
  supportInterpreter := true
