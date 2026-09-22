/-
Verification/ProofManifest.lean - Lean-Native Proof Classification Engine

Inspects the Lean environment and classifies proofs into the 4-level
depth hierarchy:
- L0: Structural (gate/port counts, instance counts, wire connectivity)
- L1: Functional Truth (exhaustive truth tables, evalCircuit, compileCircuit)
- L2: Inductive Invariants (state machine bounds, queue FIFO, CAM snooping)
- L3: Temporal Refinement (TraceSpec, Refines, dual_compositional_refinement)
-/

import Lean
import Shoumei.DSL

namespace Shoumei.Verification.ProofManifest

open Lean

/-- Proof depth level in the hierarchy -/
inductive ProofLevel where
  | L0_Structural
  | L1_Functional
  | L2_Invariant
  | L3_Refinement
  | Helper
  deriving Repr, BEq, Inhabited

def ProofLevel.toString : ProofLevel → String
  | .L0_Structural => "L0_Structural"
  | .L1_Functional => "L1_Functional"
  | .L2_Invariant  => "L2_Invariant"
  | .L3_Refinement => "L3_Refinement"
  | .Helper        => "Helper"

/-- Metadata for a classified proof declaration -/
structure ProofEntry where
  name : String
  module : String
  component : String
  level : String
  kind : String
  deriving Repr

/-- Classify a declaration's module path into a hardware component name -/
def moduleToComponent (modStr : String) (nameStr : String) : String :=
  let s := if modStr.isEmpty then nameStr else modStr
  if s.contains "Examples.Adder" || s.contains "FullAdder" then "FullAdder"
  else if s.contains "RippleCarryAdder" then "RippleCarryAdder"
  else if s.contains "Subtractor" then "Subtractor"
  else if s.contains "Comparator" then "Comparator"
  else if s.contains "LogicUnit" then "LogicUnit"
  else if s.contains "Shifter" then "Shifter"
  else if s.contains "ALUBitVec" then "ALU-BitVec-Bridge"
  else if s.contains "ALU" then "ALU32"
  else if s.contains "Decoder" && s.contains "RISCV" then "RV32I-Decoder"
  else if s.contains "Decoder" then "Decoder"
  else if s.contains "MuxTree" then "MuxTree"
  else if s.contains "Arbiter" then "Arbiter"
  else if s.contains "DFF" then "DFlipFlop"
  else if s.contains "Register" then "Register"
  else if s.contains "Queue" then "Queue"
  else if s.contains "FreeList" then "FreeList"
  else if s.contains "RAT" then "RAT"
  else if s.contains "PhysRegFile" then "PhysRegFile"
  else if s.contains "RenameStage" then "RenameStage"
  else if s.contains "ReservationStation" then "ReservationStation"
  else if s.contains "Decoupled" then "Decoupled"
  else if s.contains "Verification" then "Verification-Framework"
  else if s.contains "Theorems" then "Core-Theorems"
  else if s.contains "DSL" || s.contains "Semantics" then "Core-DSL"
  else "Other"

/-- Classify a proof declaration based on its type term and declaration name -/
def classifyProof (nameStr : String) (typeStr : String) : ProofLevel :=
  if typeStr.contains "TraceSpec" || typeStr.contains "Refines" ||
     typeStr.contains "satisfiesTrace" || typeStr.contains "dual_compositional_refinement" ||
     typeStr.contains "RegisterSpec" || typeStr.contains "RegisterEnSpec" ||
     nameStr.contains "refinement" || nameStr.contains "temporal" || nameStr.contains "Trace" ||
     nameStr.contains "non_interference" || nameStr.contains "pipeline" || nameStr.contains "bisim" then
    .L3_Refinement
  else if typeStr.contains "never_exceeds" || typeStr.contains "QueueInvariant" ||
          typeStr.contains "queue_fifo" || typeStr.contains "preserves_order" ||
          typeStr.contains "onehot" || typeStr.contains "arbiter_" ||
          typeStr.contains "rs_" || typeStr.contains "RSState" ||
          typeStr.contains "FreeListState" || typeStr.contains "RATState" ||
          nameStr.contains "arbiter_" || nameStr.contains "onehot" ||
          nameStr.contains "rs_" || nameStr.contains "queue_fifo" ||
          nameStr.contains "invariant" || nameStr.contains "cover_all_bits" ||
          nameStr.contains "_synchronized" || nameStr.contains "_sec_" ||
          nameStr.contains "isolation" || nameStr.contains "nodup" ||
          typeStr.contains "Nodup" ||
          (typeStr.contains "preserves" && !typeStr.contains "length") then
    .L2_Invariant
  else if typeStr.contains "evalCircuit" || typeStr.contains "compileCircuit" ||
          typeStr.contains "evalGate" || typeStr.contains "evalCycle" ||
          typeStr.contains "aluSemantics" || typeStr.contains "checkRca4" ||
          typeStr.contains "checkCmp4" || typeStr.contains "truthTable" ||
          typeStr.contains "truth_table" || typeStr.contains "arithmetic_correct" ||
          typeStr.contains "functional_correct" || nameStr.contains "_correct" ||
          nameStr.contains "_arithmetic" || nameStr.contains "truthTable" ||
          nameStr.contains "truth_table" || nameStr.contains "semantics" ||
          nameStr.contains "registerEn" || nameStr.contains "evalMUX" then
    .L1_Functional
  else if typeStr.contains "Circuit.gates" || typeStr.contains "Circuit.inputs" ||
          typeStr.contains "Circuit.outputs" || typeStr.contains "Circuit.instances" ||
          nameStr.contains "_structure" || nameStr.contains "_ports" ||
          nameStr.contains "_gate_count" then
    .L0_Structural
  else
    .Helper

/-- Convert an olean path to Lean module Name -/
def pathToModuleName (p : System.FilePath) (baseDir : System.FilePath) : Option Name :=
  let pStr := p.toString
  let baseStr := baseDir.toString
  if pStr.startsWith baseStr && pStr.endsWith ".olean" then
    let rel := ((pStr.drop (baseStr.length + 1)).dropEnd 6).toString
    let parts := rel.splitOn "/"
    let name := parts.foldl (fun (acc : Name) part => Name.str acc part) Name.anonymous
    some name
  else
    none

/-- Recursively find all olean files in a directory -/
partial def findOleans (dir : System.FilePath) : IO (List System.FilePath) := do
  let mut res := []
  for entry in (← System.FilePath.readDir dir) do
    let path := entry.path
    if (← path.isDir) then
      res := res ++ (← findOleans path)
    else if path.extension == some "olean" then
      res := path :: res
  return res

/-- Generate JSON string representation of proof entries -/
def escapeJson (s : String) : String :=
  s.replace "\\" "\\\\" |>.replace "\"" "\\\"" |>.replace "\n" "\\n"

/-- Build proof manifest by reflecting on Lean environment -/
unsafe def generateProofManifest (outputPath : String) : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  let baseDir : System.FilePath := ".lake/build/lib/lean"
  let files ← findOleans baseDir
  let allMods := files.filterMap (pathToModuleName · baseDir)
  let modNames := allMods.filter (fun n => n.toString.startsWith "Shoumei")
  let mods := modNames.map (fun m => ({ module := m } : Import))
  let env ← Lean.importModules mods.toArray {}

  let mut entries : List ProofEntry := []
  let mut axioms : List ProofEntry := []
  let mut countL0 := 0
  let mut countL1 := 0
  let mut countL2 := 0
  let mut countL3 := 0
  let mut countHelper := 0

  for (name, cinfo) in env.constants do
    let nameStr := name.toString
    if nameStr.startsWith "Shoumei" && !nameStr.contains "proof_" && !nameStr.contains "aux" then
      let modStr := match env.getModuleIdxFor? name with
        | some idx =>
          if idx.toNat < env.header.moduleNames.size then
            env.header.moduleNames[idx.toNat]!.toString
          else ""
        | none => ""
      let comp := moduleToComponent modStr nameStr
      match cinfo with
      | .axiomInfo _ =>
        let entry : ProofEntry := {
          name := nameStr,
          module := modStr,
          component := comp,
          level := "Axiom",
          kind := "axiom"
        }
        axioms := entry :: axioms
      | .thmInfo val =>
        let typeStr := (format val.type).pretty
        let level := classifyProof nameStr typeStr
        match level with
        | .L0_Structural => countL0 := countL0 + 1
        | .L1_Functional => countL1 := countL1 + 1
        | .L2_Invariant  => countL2 := countL2 + 1
        | .L3_Refinement => countL3 := countL3 + 1
        | .Helper        => countHelper := countHelper + 1
        let entry : ProofEntry := {
          name := nameStr,
          module := modStr,
          component := comp,
          level := level.toString,
          kind := "theorem"
        }
        entries := entry :: entries
      | _ => pure ()

  let totalTheorems := entries.length
  let totalAxioms := axioms.length

  -- Emit JSON
  let mut json := "{\n"
  json := json ++ "  \"summary\": {\n"
  json := json ++ s!"    \"total_theorems\": {totalTheorems},\n"
  json := json ++ s!"    \"total_axioms\": {totalAxioms},\n"
  json := json ++ s!"    \"l0_structural\": {countL0},\n"
  json := json ++ s!"    \"l1_functional\": {countL1},\n"
  json := json ++ s!"    \"l2_invariant\": {countL2},\n"
  json := json ++ s!"    \"l3_refinement\": {countL3},\n"
  json := json ++ s!"    \"helper\": {countHelper}\n"
  json := json ++ "  },\n"

  json := json ++ "  \"declarations\": [\n"
  let allDecls := (entries ++ axioms).reverse
  let declCount := allDecls.length
  let mut idx := 0
  for d in allDecls do
    idx := idx + 1
    let comma := if idx < declCount then "," else ""
    let line := "    {\"name\": \"" ++ escapeJson d.name ++ "\", \"module\": \"" ++ escapeJson d.module ++ "\", \"component\": \"" ++ escapeJson d.component ++ "\", \"level\": \"" ++ d.level ++ "\", \"kind\": \"" ++ d.kind ++ "\"}" ++ comma ++ "\n"
    json := json ++ line
  json := json ++ "  ]\n"
  json := json ++ "}\n"

  IO.FS.writeFile outputPath json
  IO.println s!"✓ Exported proof manifest to {outputPath}"
  IO.println s!"  Theorems: {totalTheorems} (L0: {countL0}, L1: {countL1}, L2: {countL2}, L3: {countL3}, Helper: {countHelper})"
  IO.println s!"  Axioms: {totalAxioms}"

end Shoumei.Verification.ProofManifest
