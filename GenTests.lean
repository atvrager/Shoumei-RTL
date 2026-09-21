/-
  GenTests.lean - Test Generator Executable

  Emits the directed pattern corpus plus a batch of seeded random instruction
  streams into `testbench/tests/generated/`.

  Usage: lake exe gen_tests [--seed=N] [--count=N] [--length=N]
                            [--instr-dict=PATH] [--out=DIR]

  With no `--seed` the seed comes from OS entropy and is printed, so any run can
  be replayed.  `replaySeeds` in `TestGen.RandProgram` pins seeds promoted from
  runs that found a defect.
-/

import Shoumei.TestGen.Patterns
import Shoumei.TestGen.RandProgram
import Shoumei.RISCV.EncoderProofs

open Shoumei.RISCV Shoumei.TestGen

/-- Command-line options. -/
structure Options where
  seed : Option Nat := none
  count : Nat := batchSize
  length : Nat := payloadWords
  dictPath : System.FilePath := instrDictPath
  outDir : String := "testbench/tests/generated"

/-- `--name=value` parser; unknown arguments are ignored. -/
def parseArgs (args : List String) (o : Options := {}) : Options :=
  match args with
  | [] => o
  | a :: rest =>
    let o := parseArgs rest o
    if a.startsWith "--seed=" then { o with seed := some ((a.drop 7).toNat!) }
    else if a.startsWith "--count=" then { o with count := (a.drop 8).toNat! }
    else if a.startsWith "--length=" then { o with length := (a.drop 9).toNat! }
    else if a.startsWith "--instr-dict=" then { o with dictPath := (a.drop 13).toString }
    else if a.startsWith "--out=" then { o with outDir := (a.drop 6).toString }
    else o

/-- Zero-pad to four digits, for `rand_0007`. -/
def pad4 (n : Nat) : String :=
  let s := toString n
  String.ofList (List.replicate (4 - s.length) '0') ++ s

/-- Little-endian 64-bit seed from eight entropy bytes. -/
def seedOfBytes (b : ByteArray) : Nat :=
  (List.range 8).foldl (fun acc i => acc + (b.get! i).toNat * 256 ^ i) 0

/-- Split `seed` into `n` uncorrelated generators. -/
def deriveGens (seed : Nat) (n : Nat) : List StdGen :=
  (List.range n).foldl (fun (st : StdGen × List StdGen) _ =>
    let (a, b) := RandomGen.split st.1
    (a, st.2 ++ [b])) (mkStdGen seed, []) |>.2

/-- Emit a batch of random programs plus the replay seeds, and self-check every
    emitted word against the straight-line invariant. -/
def emitRandomBatch (opts : Options) (defs : List InstructionDef) (seed : Nat) : IO Unit := do
  let alphabet := decodedAlphabet defs
  let gens := deriveGens seed opts.count

  for i in List.range opts.count do
    let body := runRand (gens.getD i (mkStdGen 0))
      (buildProgram defs alphabet (dealtCover alphabet i) opts.length)
    -- The straight-line invariant, re-derived from each encoding.
    let mut prev : Option UInt32 := none
    for e in body do
      match checkWord defs e.1 e.2.1 prev with
      | .ok () => pure ()
      | .error msg => throw (IO.userError s!"rand_{pad4 i}: {msg}")
      prev := some e.2.1
    let name := s!"rand_{pad4 i}"
    IO.FS.writeFile s!"{opts.outDir}/{name}.S"
      (randProgramAsm defs name seed opts.length opts.count opts.dictPath.toString body)
    IO.println s!"  {name} seed={seed} words={body.length}"

  for rs in replaySeeds do
    let gs := deriveGens rs 1
    let body := runRand (gs.getD 0 (mkStdGen 0))
      (buildProgram defs alphabet (dealtCover alphabet 0) opts.length)
    IO.FS.writeFile s!"{opts.outDir}/rand_replay_{rs}.S"
      (randProgramAsm defs s!"rand_replay_{rs}" rs opts.length 1 opts.dictPath.toString body)

  -- Alphabet coverage: the dealt covers alone must reach every member.
  let covered := (List.range opts.count).flatMap fun i => dealtCover alphabet i
  let isDecoded (c : InstrClass) : Bool := match c with | .decoded _ => true | _ => false
  let decodedCount := (alphabet.filter isDecoded).length
  let zbCount := alphabet.length - decodedCount
  let coveredDecoded := (covered.filter isDecoded).eraseDups.length
  let coveredZb := (covered.filter (fun c => !isDecoded c)).eraseDups.length
  IO.println s!"alphabet coverage: {coveredDecoded}/{decodedCount} decoded + Zb* {coveredZb}/{zbCount}"
  let missing := alphabet.filter fun c => !covered.contains c
  unless missing.isEmpty do
    IO.println s!"alphabet members never dealt: {missing.length}"

def main (args : List String) : IO Unit := do
  let opts := parseArgs args
  IO.FS.createDirAll opts.outDir

  -- Directed patterns: unchanged corpus.
  let patterns := allPatterns ++ fpPatterns
  IO.println s!"Generating {patterns.length} test programs ({allPatterns.length} base + {fpPatterns.length} FP)..."
  for prog in patterns do
    IO.FS.writeFile s!"{opts.outDir}/{prog.name}.S" prog.toAsm

  -- The instruction dictionary is a submodule; a job without `make opcodes`
  -- still gets the directed corpus.
  let defsOpt : Option (List InstructionDef) ←
    try
      pure (some (← loadInstrDefsForConfig defaultCPUConfig opts.dictPath))
    catch _ =>
      IO.println s!"WARNING: {opts.dictPath} missing (run 'make opcodes'); skipping random batch"
      pure none
  match defsOpt with
  | none => IO.println "Done."
  | some defs => do
    runEncoderTests defs
    let seed ← match opts.seed with
      | some s => pure s
      | none => seedOfBytes <$> IO.getRandomBytes 8
    IO.println s!"random batch seed={seed}"
    emitRandomBatch opts defs seed
    IO.println "Done."
