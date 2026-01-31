/-
Codegen/Common.lean - Shared Code Generation Utilities

Provides common functionality for code generators:
- String formatting and indentation
- Wire name sanitization
- Line joining and formatting helpers
-/

import ProvenRTL.DSL

namespace ProvenRTL.Codegen

-- Indent a string by a given number of spaces
def indent (n : Nat) (s : String) : String :=
  String.mk (List.replicate n ' ') ++ s

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

end ProvenRTL.Codegen
