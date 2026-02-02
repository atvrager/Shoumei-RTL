/-
  RISC-V Opcode Parser

  Parses riscv-opcodes instr_dict.json to generate InstructionDef instances.
  This runs at compile time to populate rv32i_instructions.
-/

import Lean.Data.Json
import Shoumei.RISCV.ISA
import Shoumei.RISCV.Config

namespace Shoumei.RISCV

open Lean (Json)

/-- Parse a hex string (e.g., "0x33") to UInt32 -/
def parseHex (s : String) : Option UInt32 :=
  if s.startsWith "0x" || s.startsWith "0X" then
    let hexStr := s.drop 2
    -- Parse hex string to Nat, then convert to UInt32
    match hexStr.foldl (fun acc c =>
      acc.bind fun n =>
        if c.isDigit then
          some (n * 16 + (c.toNat - '0'.toNat))
        else if 'a' ≤ c && c ≤ 'f' then
          some (n * 16 + (c.toNat - 'a'.toNat + 10))
        else if 'A' ≤ c && c ≤ 'F' then
          some (n * 16 + (c.toNat - 'A'.toNat + 10))
        else
          none
    ) (some 0) with
    | some n => some (UInt32.ofNat n)
    | none => none
  else
    none

/-- Parse variable_fields array from JSON -/
def parseVariableFields (json : Json) : Except String (List FieldType) := do
  let arr ← json.getArr?
  let fields ← arr.toList.mapM fun fieldJson => do
    let fieldStr ← fieldJson.getStr?
    match FieldType.fromString fieldStr with
    | some ft => pure ft
    | none => throw s!"Unknown field type: {fieldStr}"
  pure fields

/-- Parse extension array from JSON -/
def parseExtensions (json : Json) : Except String (List String) := do
  let arr ← json.getArr?
  arr.toList.mapM Json.getStr?

/-- Parse a single instruction definition from JSON object -/
def parseInstructionDef (name : String) (json : Json) : Except String InstructionDef := do
  -- Extract fields from JSON object using getObjValAs?
  let encoding ← json.getObjValAs? String "encoding"
  let matchStr ← json.getObjValAs? String "match"
  let maskStr ← json.getObjValAs? String "mask"

  -- Get variable_fields and extension as raw JSON
  let obj ← json.getObj?
  let variableFieldsJson ← match obj.get? "variable_fields" with
    | some j => pure j
    | none => throw "Missing 'variable_fields' field"

  let extensionJson ← match obj.get? "extension" with
    | some j => pure j
    | none => throw "Missing 'extension' field"

  -- Parse fields
  let variableFields ← parseVariableFields variableFieldsJson
  let extension ← parseExtensions extensionJson
  let matchVal ← match parseHex matchStr with
    | some v => pure v
    | none => throw s!"Invalid hex value for match: {matchStr}"
  let maskVal ← match parseHex maskStr with
    | some v => pure v
    | none => throw s!"Invalid hex value for mask: {maskStr}"

  -- Parse opType from name
  let opType ← match OpType.fromString name with
    | some ot => pure ot
    | none => throw s!"Unknown instruction: {name}"

  return {
    name := name
    opType := opType
    encoding := encoding
    variableFields := variableFields
    extension := extension
    matchBits := matchVal
    maskBits := maskVal
  }

/-- Parse the entire instr_dict.json file -/
def parseInstrDict (jsonStr : String) : Except String (List InstructionDef) := do
  -- Parse JSON
  let json ← match Json.parse jsonStr with
    | Except.ok j => pure j
    | Except.error e => throw s!"JSON parse error: {e}"

  -- Extract object
  let obj ← json.getObj?

  -- Parse each instruction using foldl (TreeMap.Raw API in Lean 4.27.0)
  obj.foldl (fun acc name instrJson =>
    acc.bind fun instrs => do
      let instrDef ← parseInstructionDef name instrJson
      pure (instrDef :: instrs)) (Except.ok [])

/-- Read and parse instr_dict.json from file system -/
def loadInstrDictFromFile (path : System.FilePath) : IO (List InstructionDef) := do
  -- Read file
  let jsonStr ← IO.FS.readFile path

  -- Parse
  match parseInstrDict jsonStr with
  | Except.ok defs => return defs
  | Except.error e => throw (IO.userError s!"Failed to parse {path}: {e}")

/-- Path to instr_dict.json (relative to project root) -/
def instrDictPath : System.FilePath :=
  "third_party/riscv-opcodes/instr_dict.json"

/-- Load instruction definitions filtered by a CPUConfig's enabled extensions.

    This is the primary config-aware entry point. It loads all instructions from
    the JSON file, then filters to only include instructions whose extension
    field matches at least one of the config's enabled extensions.

    Example:
    - rv32iConfig  → only instructions with extension containing "rv_i" or "rv32_i"
    - rv32imConfig → also includes instructions with extension containing "rv_m"
-/
def loadInstrDefsForConfig (config : CPUConfig) (path : System.FilePath := instrDictPath)
    : IO (List InstructionDef) := do
  let allDefs ← loadInstrDictFromFile path
  let enabled := config.enabledExtensions
  return allDefs.filter fun instrDef =>
    instrDef.extension.any (enabled.contains ·)

end Shoumei.RISCV
