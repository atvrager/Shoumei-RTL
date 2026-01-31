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
