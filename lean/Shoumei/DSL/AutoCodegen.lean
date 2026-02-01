/-
DSL/AutoCodegen.lean - Automatic Code Generation for All Circuits

Makes codegen automatic and discoverable - just define a Circuit and it gets generated.

Usage:
  -- In your module file (e.g., MyCircuit.lean):
  def myCircuit : Circuit := { ... }

  -- Register it for auto-generation:
  registerCircuit myCircuit

  -- Or use the convenience macro:
  @[codegen]
  def myCircuit : Circuit := { ... }

Then run: lake exe codegen_all
-/

import Shoumei.DSL
import Shoumei.Codegen.Unified

namespace Shoumei.DSL.AutoCodegen

open Shoumei
open Shoumei.Codegen.Unified

-- Global registry of circuits to generate
-- (In practice, this would be built at compile time via macros/attributes)
private def circuitRegistry : IO (List Circuit) := do
  -- This is a placeholder - ideally we'd use metaprogramming to auto-discover
  -- all definitions with @[codegen] attribute
  pure []

-- Helper: define and auto-register a circuit for codegen
def defineCircuit (name : String) (c : Circuit) : IO Circuit := do
  -- Could register in a global list here
  pure c

-- Generate all registered circuits
def generateAll : IO Unit := do
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "  証明 Shoumei RTL - Auto Code Generation"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println ""

  initOutputDirs

  let circuits ← circuitRegistry
  for c in circuits do
    writeCircuitVerbose c

  IO.println ""
  IO.println s!"✓ Generated {circuits.length} circuits"
  IO.println "  SV:      output/sv-from-lean/"
  IO.println "  Chisel:  chisel/src/main/scala/generated/"
  IO.println "  SystemC: output/systemc/"

end Shoumei.DSL.AutoCodegen
