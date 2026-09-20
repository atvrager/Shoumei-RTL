/-
Codegen/CellLibs/Library.lean - PDK to cell-library lookup
-/

import Shoumei.Codegen.CellLibs.ASAP7
import Shoumei.Codegen.CellLibs.GF180

namespace Shoumei.Codegen

open Shoumei
open Shoumei.Components

/-- The standard-cell library for a PDK. -/
def libraryFor : PDK → CellLibrary
  | .asap7     => asap7Library
  | .gf180mcu  => gf180Library

end Shoumei.Codegen
