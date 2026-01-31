import Lake
open Lake DSL

package «ProvenRTL» where
  -- Package configuration for Proven RTL
  -- Lake version: compatible with Lean 4.x

lean_lib «ProvenRTL» where
  -- Main library containing DSL, semantics, theorems, and code generators
  srcDir := "lean"

-- Executable target for code generation
-- Runs code generators to produce SystemVerilog and Chisel output
@[default_target]
lean_exe codegen where
  root := `Main
  supportInterpreter := true
