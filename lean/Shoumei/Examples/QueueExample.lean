/-
QueueExample.lean - Queue/FIFO Code Generation Example

Generates SystemVerilog and Chisel for various Queue sizes.
This demonstrates ready/valid handshaking in synthesizable hardware.
-/

import Shoumei.Circuits.Sequential.Queue
import Shoumei.Codegen.SystemVerilog
import Shoumei.Codegen.Chisel

namespace Shoumei.Examples

open Shoumei.Circuits.Sequential
open Shoumei.Codegen.SystemVerilog (toSystemVerilog)
open Shoumei.Codegen.Chisel (toChisel)

-- Helper to generate Queue files for any width (using structural implementation)
def writeQueueFiles (width : Nat) : IO Unit := do
  let q := mkQueue1StructuralComplete width
  let svPath := s!"output/sv-from-lean/{q.name}.sv"
  let chiselPath := s!"chisel/src/main/scala/generated/{q.name}.scala"

  IO.FS.writeFile svPath (toSystemVerilog q)
  IO.FS.writeFile chiselPath (toChisel q)

  IO.println s!"✓ Generated: {svPath}"
  IO.println s!"✓ Generated: {chiselPath}"

-- Specific widths
def writeQueue1_8bit : IO Unit := writeQueueFiles 8
def writeQueue1_32bit : IO Unit := writeQueueFiles 32

-- Main entry point for Queue generation
def queueMain : IO Unit := do
  IO.println "証明 Shoumei RTL - Queue Code Generation (Structural)"
  IO.println "====================================================="
  IO.println ""
  IO.println "Building Queues from DFFs using DSL composition..."
  IO.println ""

  IO.println "==> Queue1_8 (8-bit data, 1-entry) - Structural from DFFs"
  writeQueue1_8bit
  IO.println ""

  IO.println "==> Queue1_32 (32-bit data, 1-entry) - Structural from DFFs"
  writeQueue1_32bit
  IO.println ""

  IO.println "✓ Structural Queue code generation complete"
  IO.println ""
  IO.println "Note: Queues are built compositionally from:"
  IO.println "      - DFFs for state (valid bit + data registers)"
  IO.println "      - Combinational gates (NOT, AND, OR, MUX) for control logic"
  IO.println "      - Ready/valid handshaking protocol"

end Shoumei.Examples
