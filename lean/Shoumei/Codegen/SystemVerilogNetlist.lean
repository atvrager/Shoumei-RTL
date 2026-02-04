/-
Codegen/SystemVerilogNetlist.lean - SystemVerilog Netlist Generator (Flat Mode)

Generates flat netlist SystemVerilog by recursively inlining all instances.
Output is a single module with only primitive gates, using hierarchical wire names.

Design principles:
- Fully flat: all instances recursively inlined to gates
- Hierarchical naming: `u_mem__reg_0__dff_q` preserves original structure
- Typed buses: logic [31:0] (reuses bus reconstruction from V2)
- Single always_ff per register group
- No module instantiations in output (pure netlist)

Use cases:
- Formal verification tools that prefer flat netlists
- Equivalence checking against hierarchical SV
- Gate-level simulation

Target: IEEE 1800-2017 SystemVerilog
Validation: Yosys equiv_make vs hierarchical SV
-/

import Shoumei.DSL
import Shoumei.DSL.Interfaces
import Shoumei.Codegen.Common
import Shoumei.Codegen.SystemVerilogV2

namespace Shoumei.Codegen.SystemVerilogNetlist

open Shoumei.Codegen
open Shoumei.Codegen.SystemVerilogV2  -- Reuse bus reconstruction

/-! ## Flattening Logic -/

/-- Wire remapping function type: maps old wire to new hierarchical wire -/
abbrev WireMap := Wire → Wire

/-- Create hierarchical wire name: prefix all wires with instance name -/
def prefixWireName (instName : String) (w : Wire) : Wire :=
  { name := s!"{instName}__{w.name}" }

/-- Recursively flatten a circuit by inlining all instances.
    Returns list of gates with hierarchically-named wires.

    Strategy:
    1. Keep all direct gates from this circuit
    2. For each instance:
       a. Look up the instance's circuit definition
       b. Create wire remapping: instance port → parent wire, internal → prefixed
       c. Recursively flatten the instance circuit
       d. Collect all resulting gates

    Note: This requires access to all circuit definitions (circuit registry).
    For now, we assume instances are NOT flattened (future work: circuit registry).
    Current implementation: just keeps direct gates (TODO: add registry lookup).
-/
partial def flattenCircuit (c : Circuit) : List Gate :=
  -- TODO Phase 6: Implement recursive instance inlining
  -- For now, just return direct gates (works for leaf modules)
  -- Future: Look up instance circuits and recursively inline
  c.gates

/-! ## Netlist Generation -/

/-- Generate flat netlist SystemVerilog.
    Produces single module with all instances inlined to gates. -/
def toSystemVerilogNetlist (c : Circuit) : String :=
  -- Step 1: Flatten circuit to gates only
  let flatGates := flattenCircuit c

  -- Step 2: Build context (detect clock/reset from original circuit)
  let clockWires := findClockWires c
  let resetWires := findResetWires c
  let isSeq := flatGates.any (fun g => g.gateType == GateType.DFF)

  -- Step 3: Auto-detect signal groups from wire patterns
  let allWires := (c.inputs ++ c.outputs ++ flatGates.map (·.output)).eraseDups
  let signalGroups := autoDetectSignalGroups allWires

  -- Step 4: Build wire→group mapping
  let wireToGroup := signalGroups.flatMap (fun sg =>
    sg.wires.map (fun w => (w, sg))
  )
  let wireToIndex := signalGroups.flatMap (fun sg =>
    sg.wires.enum.map (fun (idx, w) => (w, idx))
  )

  let _ctx : Context := {
    wireToGroup := wireToGroup
    wireToIndex := wireToIndex
    clockWires := clockWires
    resetWires := resetWires
    isSequential := isSeq
  }

  -- Step 5: Generate module header
  let header := s!"// Flat netlist generated from {c.name}\n"
              ++ s!"// {flatGates.length} gates (all instances inlined)\n"
              ++ s!"module {c.name}(\n"

  -- Step 6: Generate ports (using signal groups for buses)
  -- TODO: Implement port generation with bus types
  let ports := "  // TODO: Generate typed ports\n"

  -- Step 7: Generate internal wires
  let wires := "  // TODO: Generate internal wire declarations\n"

  -- Step 8: Generate gate assignments
  let assigns := "  // TODO: Generate continuous assignments\n"

  -- Step 9: Generate always_ff blocks for registers
  let registers := if isSeq then "  // TODO: Generate always_ff blocks\n" else ""

  -- Step 10: Close module
  let footer := "endmodule\n"

  header ++ ports ++ ");\n\n" ++ wires ++ "\n" ++ assigns ++ "\n" ++ registers ++ footer

end Shoumei.Codegen.SystemVerilogNetlist
