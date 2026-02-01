/-
Shoumei.lean - Main Module Entry Point

This is the root module that exports all Shoumei components.
Import this module to access the DSL, semantics, theorems, and code generators.

Usage:
  import Shoumei
-/

-- Core DSL and semantics
import Shoumei.DSL
import Shoumei.Semantics
import Shoumei.Theorems

-- Code generators
import Shoumei.Codegen.Common
import Shoumei.Codegen.SystemVerilog
import Shoumei.Codegen.Chisel
import Shoumei.Codegen.SystemC

-- Examples
import Shoumei.Examples.Adder
