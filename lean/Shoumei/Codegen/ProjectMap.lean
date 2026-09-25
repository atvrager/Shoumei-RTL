/-
Codegen/ProjectMap.lean - Native Lean generator for docs/project-map.md.

Derives the architecture subsystem composition graph, coverage table,
and mechanical gap list directly from Lean sources.
-/

import Std.Data.HashMap
import Std.Data.HashSet

namespace Shoumei.Codegen.ProjectMap

def knownGaps : List String := [
  "The `Circuit satisfies Behavior` atom exists (`Verification/Implements.lean`) " ++
  "and composes (`implements_compose`), but coverage is partial -- see the " ++
  "Refines column.  No RISC-V module carries one yet.",
  "Certificates are unverified pointers: `CompositionalCert.proofReference` is " ++
  "a `String` and the LEC script only checks that dependencies were verified.",
  "Widths are fixed to 64-bit for the RV64G core: `CPUConfig.xlen = 64` and " ++
  "`CPUConfig.flen = 64`. Parameterized width polymorphism across 32/64-bit " ++
  "is not yet abstracted into a single unified top-level circuit generator.",
  "The flat netlist emitter (`SystemVerilogNetlist.lean`) is " ++
  "combinational-only: it drops DFFs and clock/reset, and full instance " ++
  "inlining does not scale (8.7 MB for one module).",
  "The CPU top-level has no compositional certificate, so it is the dominant " ++
  "cost of a full LEC run."
]

/-- Check if a string is a valid identifier. -/
def isIdent (s : String) : Bool :=
  !s.isEmpty && s.toList.all (fun c => c.isAlphanum || c == '_')

/-- Recursively find all .lean files in a directory. -/
partial def findLeanFiles (dir : System.FilePath) : IO (List System.FilePath) := do
  let mut results : List System.FilePath := []
  for entry in ← dir.readDir do
    let path := entry.path
    if (← path.isDir) then
      results := results ++ (← findLeanFiles path)
    else if path.extension == some "lean" then
      results := results.concat path
  return results

/-- Extract circuit names defined via record syntax with name and inputs fields. -/
def findCircuitNames (text : String) : List String := Id.run do
  let mut names : List String := []
  let parts := text.splitOn "name"
  let mut prev := ""
  for p in parts do
    if prev != "" then
      let preTrim := prev.trimAscii.toString
      if preTrim.endsWith "{" then
        let afterTrim := p.trimAscii.toString
        if afterTrim.startsWith ":=" then
          let a2 := ((afterTrim.drop 2).toString).trimAscii.toString
          if a2.startsWith "\"" then
            let a3 := (a2.drop 1).toString
            let parts2 := a3.splitOn "\""
            match parts2 with
            | cName :: restParts =>
              if isIdent cName then
                let afterQuote := ("\"".intercalate restParts).trimAscii.toString
                let afterQuote := if afterQuote.startsWith "," then ((afterQuote.drop 1).toString).trimAscii.toString else afterQuote
                if afterQuote.startsWith "inputs" then
                  let afterInputs := ((afterQuote.drop 6).toString).trimAscii.toString
                  if afterInputs.startsWith ":=" then
                    names := names.concat cName
            | [] => ()
    prev := p
  return names

/-- Extract instance module names referenced via `moduleName := "X"`. -/
def findInstances (text : String) : Std.HashSet String := Id.run do
  let mut set : Std.HashSet String := {}
  let parts := text.splitOn "moduleName"
  for p in parts.drop 1 do
    let trimmed := p.trimAscii.toString
    if trimmed.startsWith ":=" then
      let a2 := ((trimmed.drop 2).toString).trimAscii.toString
      if a2.startsWith "\"" then
        let a3 := (a2.drop 1).toString
        let parts2 := a3.splitOn "\""
        match parts2 with
        | instName :: _ =>
          if isIdent instName then
            set := set.insert instName
        | [] => ()
  return set

/-- Check if file contains a leading doc comment block `/- ... -/`. -/
def hasDocComment (text : String) : Bool := Id.run do
  let parts := text.splitOn "/-"
  let mut found := false
  for p in parts.drop 1 do
    if !found then
      let endParts := p.splitOn "-/"
      match endParts with
      | body :: _ =>
        let lines := body.splitOn "\n"
        for line in lines do
          let s := line.trimAscii.toString
          let s := (s.dropWhile (fun c => c == '*' || c.isWhitespace)).toString.trimAscii.toString
          if !s.isEmpty then
            found := true
      | [] => ()
  return found

/-- Extract certificate module names from CompositionalCerts.lean. -/
def loadCerts (text : String) : Std.HashSet String := Id.run do
  let mut certs : Std.HashSet String := {}
  let parts := text.splitOn "CompositionalCert := {"
  for p in parts.drop 1 do
    let bodyParts := p.splitOn "}"
    match bodyParts with
    | body :: _ =>
      let mParts := body.splitOn "moduleName"
      for mp in mParts.drop 1 do
        let trimmed := mp.trimAscii.toString
        if trimmed.startsWith ":=" then
          let a2 := ((trimmed.drop 2).toString).trimAscii.toString
          if a2.startsWith "\"" then
            let a3 := (a2.drop 1).toString
            let parts2 := a3.splitOn "\""
            match parts2 with
            | modName :: _ =>
              if isIdent modName then
                certs := certs.insert modName
            | [] => ()
    | [] => ()
  return certs

/-- Extract refinement atom module names from Refinements.lean. -/
def loadRefinements (text : String) : Std.HashSet String := Id.run do
  let mut refs : Std.HashSet String := {}
  for tag in [".combinational", ".sequential"] do
    let parts := text.splitOn tag
    for p in parts.drop 1 do
      let trimmed := p.trimAscii.toString
      if trimmed.startsWith "\"" then
        let a := (trimmed.drop 1).toString
        let parts2 := a.splitOn "\""
        match parts2 with
        | cName :: rest =>
          if isIdent cName then
            let restTrimmed := ("\"".intercalate rest).trimAscii.toString
            if restTrimmed.startsWith "\"" then
              refs := refs.insert cName
        | [] => ()
  return refs

/-- Compute subsystem string from a relative Lean path. -/
def subsystem (path : System.FilePath) : String :=
  let s := path.toString
  let rawParts := s.splitOn "/"
  let parts := rawParts.filter (fun p => p != "lean" && p != ".")
  if parts.length <= 1 then
    "(root)"
  else
    "/".intercalate (parts.dropLast)

/-- Comparator for cross-subsystem edges: (-count, from_subsys, to_subsys). -/
def crossLess (e1 e2 : (String × String) × Nat) : Bool :=
  let ((a1, b1), n1) := e1
  let ((a2, b2), n2) := e2
  if n1 > n2 then true
  else if n1 < n2 then false
  else if a1 < a2 then true
  else if a1 > a2 then false
  else b1 < b2

/-- Generate docs/project-map.md directly from lean/ source tree. -/
def generate (outPath : System.FilePath := System.FilePath.mk "docs/project-map.md") : IO UInt32 := do
  let leanDir := System.FilePath.mk "lean"
  let leanFilesRaw ← findLeanFiles leanDir
  if leanFilesRaw.isEmpty then
    IO.eprintln "no Lean sources found"
    return 1
  let leanFiles := leanFilesRaw.toArray.qsort (fun a b => a.toString < b.toString) |>.toList

  let mut circuitFile : Std.HashMap String System.FilePath := {}
  let mut fileText : Std.HashMap String String := {}
  let mut circuitNamesList : List String := []

  for f in leanFiles do
    let text ← IO.FS.readFile f
    fileText := fileText.insert f.toString text
    let names := findCircuitNames text
    for name in names do
      if !circuitFile.contains name then
        circuitFile := circuitFile.insert name f
        circuitNamesList := circuitNamesList.concat name

  let mut instByFile : Std.HashMap String (Std.HashSet String) := {}
  for f in leanFiles do
    let text := fileText.getD f.toString ""
    instByFile := instByFile.insert f.toString (findInstances text)

  let certText := fileText.getD "lean/Shoumei/Verification/CompositionalCerts.lean" ""
  let certs := loadCerts certText

  let refText := fileText.getD "lean/Shoumei/Verification/Refinements.lean" ""
  let refinements := loadRefinements refText

  -- Composition edges
  let mut edges : Std.HashMap String (List String) := {}
  let mut subsysOf : Std.HashMap String String := {}
  for name in circuitNamesList do
    let f := circuitFile.getD name (System.FilePath.mk "")
    let sub := subsystem f
    subsysOf := subsysOf.insert name sub
    let insts := instByFile.getD f.toString {}
    let kids := (insts.filter (fun c => circuitFile.contains c && c != name)).toList.toArray.qsort (· < ·) |>.toList
    edges := edges.insert name kids

  -- Cross-subsystem edges
  let mut cross : Std.HashMap (String × String) Nat := {}
  let mut bySubsys : Std.HashMap String (List String) := {}
  for name in circuitNamesList do
    let sub := subsysOf.getD name ""
    bySubsys := bySubsys.insert sub (name :: bySubsys.getD sub [])
    let kids := edges.getD name []
    for kid in kids do
      let kidSub := subsysOf.getD kid ""
      if sub != kidSub then
        let key := (sub, kidSub)
        cross := cross.insert key (cross.getD key 0 + 1)

  -- Proofs
  let proofFiles := leanFiles.filter (fun f =>
    match f.fileName with
    | some fn => (fn.splitOn "Proofs.lean").length > 1 && fn.endsWith "Proofs.lean"
    | none => false)

  let mut provenNames : Std.HashSet String := {}
  for pf in proofFiles do
    let text := fileText.getD pf.toString ""
    for name in circuitNamesList do
      if (text.splitOn name).length > 1 then
        provenNames := provenNames.insert name

  let mut docs : Std.HashSet String := {}
  for name in circuitNamesList do
    let f := circuitFile.getD name (System.FilePath.mk "")
    let text := fileText.getD f.toString ""
    if hasDocComment text then
      docs := docs.insert name

  let mut out : List String := []
  out := out.concat "# Project Map"
  out := out.concat ""
  out := out.concat "Generated by `scripts/gen-project-map.py` from the source tree — do"
  out := out.concat "not edit by hand; re-run it.  Composition edges come from"
  out := out.concat "`moduleName :=` references between circuits, certificates from the"
  out := out.concat "Lean registry, docs from each file's leading comment block."
  out := out.concat ""
  out := out.concat s!"- Lean files: **{leanFiles.length}**"
  out := out.concat s!"- Circuits with a literal `name :=` (graph nodes): **{circuitNamesList.length}**"
  out := out.concat s!"- Compositional certificates (Lean registry): **{certs.size}**"
  out := out.concat s!"- Refinement atoms (Lean registry): **{refinements.size}**"
  out := out.concat s!"- Proof files: **{proofFiles.length}**"
  out := out.concat ""
  out := out.concat "Parameterised builders (`mkQueueNStructural`, `mkRegisterN`,"
  out := out.concat "`mkMuxTree`, `mkDecoder`, ...) construct their circuit names by"
  out := out.concat "interpolation, so those circuits cannot be recovered by scanning for a"
  out := out.concat "literal; they are enumerated in `GenerateAll.lean` and are not graph"
  out := out.concat "nodes here.  Everything below is derived from `lean/` alone, which is"
  out := out.concat "what lets `lint` assert the map is current."
  out := out.concat ""

  out := out.concat "## Subsystem composition"
  out := out.concat ""
  out := out.concat "Edges are circuit instantiations that cross a directory boundary; the"
  out := out.concat "label is how many distinct instantiations cross it."
  out := out.concat ""
  out := out.concat "```mermaid"
  out := out.concat "graph TD"
  let sortedSubsys := bySubsys.keys.toArray.qsort (· < ·) |>.toList
  for s in sortedSubsys do
    let short := s.replace "/" "_"
    let count := (bySubsys.getD s []).length
    out := out.concat s!"  {short}[\"{s}<br/>{count} circuits\"]"
  let sortedCross := cross.toList.toArray.qsort crossLess |>.toList
  for ((a, b), n) in sortedCross do
    let shortA := a.replace "/" "_"
    let shortB := b.replace "/" "_"
    out := out.concat s!"  {shortA} -->|{n}| {shortB}"
  out := out.concat "```"
  out := out.concat ""

  out := out.concat "## Coverage"
  out := out.concat ""
  out := out.concat "| Circuit | Subsystem | Inst. | Cert | Refines | Proofs | Doc |"
  out := out.concat "| :--- | :--- | ---: | :---: | :---: | :---: | :---: |"
  let sortedCircuits := circuitNamesList.toArray.qsort (· < ·) |>.toList
  for n in sortedCircuits do
    let s := subsysOf.getD n ""
    let i := (edges.getD n []).length
    let c := if certs.contains n then "yes" else ""
    let r := if refinements.contains n then "yes" else ""
    let p := if provenNames.contains n then "yes" else ""
    let d := if docs.contains n then "yes" else ""
    out := out.concat s!"| `{n}` | {s} | {i} | {c} | {r} | {p} | {d} |"
  out := out.concat ""

  out := out.concat "## Mechanical gaps"
  out := out.concat ""
  let noDoc := sortedCircuits.filter (fun n => !docs.contains n)
  let noRefine := sortedCircuits.filter (fun n => !refinements.contains n)
  let noProofs := sortedCircuits.filter (fun n => !provenNames.contains n)
  let leaves := sortedCircuits.filter (fun n => (edges.getD n []).isEmpty)
  let mut allKids : Std.HashSet String := {}
  for (_, kids) in edges.toList do
    for k in kids do
      allKids := allKids.insert k
  let rootLike := sortedCircuits.filter (fun n => !allKids.contains n)

  out := out.concat s!"- **{noDoc.length}** circuit files without a leading doc comment"
  out := out.concat s!"- **{noRefine.length}** circuits with no `Circuit satisfies Behavior` atom"
  out := out.concat s!"- **{noProofs.length}** circuits with no `*Proofs.lean` mentioning them"
  out := out.concat s!"- **{leaves.length}** circuits that instantiate nothing (leaves)"
  out := out.concat s!"- **{rootLike.length}** circuits nothing else instantiates (tops)"
  if !noDoc.isEmpty then
    out := out.concat ""
    out := out.concat "<details><summary>files without a doc comment</summary>"
    out := out.concat ""
    for n in noDoc do
      let f := circuitFile.getD n (System.FilePath.mk "")
      out := out.concat s!"- `{f}`"
    out := out.concat ""
    out := out.concat "</details>"
  out := out.concat ""

  out := out.concat "## Known gaps (hand-maintained)"
  out := out.concat ""
  out := out.concat "Not derivable from the tree; keep this list short and delete entries as"
  out := out.concat "they land."
  out := out.concat ""
  for g in knownGaps do
    out := out.concat s!"- {g}"
  out := out.concat ""

  if let some parent := outPath.parent then
    IO.FS.createDirAll parent
  let content := ("\n".intercalate out) ++ "\n"
  IO.FS.writeFile outPath content
  IO.println s!"wrote {outPath} ({out.length} lines): {circuitNamesList.length} circuits, {certs.size} certs, {noDoc.length} undocumented, {noProofs.length} unproven"
  return 0

end Shoumei.Codegen.ProjectMap
