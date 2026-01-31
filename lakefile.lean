import Lake
open Lake DSL

package «ProvenRTL» where
  -- Package configuration for Proven RTL
  -- Lake version: compatible with Lean 4.x

@[default_target]
lean_lib «ProvenRTL» where
  -- Main library containing DSL, semantics, theorems, and code generators
  srcDir := "lean"

-- TODO: Add executable target for code generation
-- This will run code generators to produce SystemVerilog and Chisel output
-- Example:
-- lean_exe codegen where
--   root := `ProvenRTL.Examples.Adder
--   supportInterpreter := true
