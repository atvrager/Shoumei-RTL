/-
Codegen/Common.lean - Shared Code Generation Utilities

Provides common functionality for code generators:
- String formatting and indentation
- Wire name sanitization
- Line joining and formatting helpers
-/

import Shoumei.DSL

namespace Shoumei.Codegen

-- Indent a string by a given number of spaces
def indent (n : Nat) (s : String) : String :=
  String.ofList (List.replicate n ' ') ++ s

-- Indent each line in a multiline string
def indentLines (n : Nat) (s : String) : String :=
  let lines := s.splitOn "\n"
  String.intercalate "\n" (lines.map (indent n))

-- Join strings with newlines
def joinLines (lines : List String) : String :=
  String.intercalate "\n" lines

-- Join strings with commas and spaces (for argument lists)
def joinCommas (items : List String) : String :=
  String.intercalate ", " items

-- Sanitize a wire name to ensure it's a valid identifier
-- For now, just use the wire name directly
-- TODO: Handle special characters, keywords, etc.
def sanitizeWireName (w : Wire) : String :=
  w.name

-- Convert wire list to comma-separated string
def wireListToString (wires : List Wire) : String :=
  joinCommas (wires.map sanitizeWireName)

-- Generate a unique internal wire name
-- TODO: Implement proper name generation with collision avoidance
def makeInternalWireName (pre : String) (idx : Nat) : String :=
  pre ++ "_" ++ toString idx

-- Comment generation (different for different languages)
def makeComment (lang : String) (comment : String) : String :=
  match lang with
  | "verilog" => s!"// {comment}"
  | "scala" => s!"// {comment}"
  | "chisel" => s!"// {comment}"
  | _ => s!"# {comment}"

-- Helper: find all clock wires (from DFF gates and instance connections)
-- Only returns wires that are actual circuit inputs (not internal derived wires)
def findClockWires (c : Circuit) : List Wire :=
  -- Find clocks from DFF gates
  let dffClocks := c.gates.filterMap (fun g =>
    if g.gateType == GateType.DFF then
      match g.inputs with
      | [_d, clk, _reset] => some clk
      | _ => none
    else
      none
  )
  -- Also find clocks from instance connections
  let instClocks := c.instances.filterMap (fun inst =>
    inst.portMap.filterMap (fun (portName, wire) =>
      if portName == "clock" then some wire else none
    ) |>.head?
  )
  -- Filter to only include actual circuit inputs (not internal wires)
  (dffClocks ++ instClocks).eraseDups.filter (fun w => c.inputs.any (fun i => i.name == w.name))

-- Helper: find all reset wires (from DFF gates and instance connections)
-- Only returns wires that are actual circuit inputs (not internal derived wires)
def findResetWires (c : Circuit) : List Wire :=
  -- Find resets from DFF gates
  let dffResets := c.gates.filterMap (fun g =>
    if g.gateType == GateType.DFF then
      match g.inputs with
      | [_d, _clk, reset] => some reset
      | _ => none
    else
      none
  )
  -- Also find resets from instance connections
  let instResets := c.instances.filterMap (fun inst =>
    inst.portMap.filterMap (fun (portName, wire) =>
      if portName == "reset" then some wire else none
    ) |>.head?
  )
  -- Filter to only include actual circuit inputs (not internal wires)
  (dffResets ++ instResets).eraseDups.filter (fun w => c.inputs.any (fun i => i.name == w.name))

end Shoumei.Codegen
