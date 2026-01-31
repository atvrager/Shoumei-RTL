/-
ProvenRTL.lean - Main Module Entry Point

This is the root module that exports all ProvenRTL components.
Import this module to access the DSL, semantics, theorems, and code generators.

Usage:
  import ProvenRTL
-/

-- Core DSL and semantics
import ProvenRTL.DSL
import ProvenRTL.Semantics
import ProvenRTL.Theorems

-- Code generators
import ProvenRTL.Codegen.Common
import ProvenRTL.Codegen.SystemVerilog
import ProvenRTL.Codegen.Chisel

-- Examples
import ProvenRTL.Examples.Adder
