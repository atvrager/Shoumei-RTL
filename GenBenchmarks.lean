/-
  GenBenchmarks.lean - Benchmark Generator Executable

  Generates one self-contained .S benchmark program per decoder instruction
  into testbench/tests/generated/bench/, plus the bench-programs.json manifest
  in output/bench/. The benchmark set is derived from the riscv-opcodes
  instruction table (the same table the CPU decoder is built from), never
  hand-written.

  Usage: lake exe gen_benchmarks [--short]

  --short emits a reduced-trip-count set into bench-short/ for lock-step
  cosimulation.  The measured regions are loops with an identical body every
  iteration, so running 256 trips proves nothing that a handful does - but in
  cosim it costs minutes of wall clock per program.
-/

import Shoumei.RISCV.BenchmarkSpecs

/-- Trip count for the cosim set.  256 -> 16 drops the sweep from ~20M
    simulated cycles to ~1.2M with no loss of instruction coverage. -/
def cosimIters : Nat := 16

structure Options where
  isShort : Bool := false
  iters : Option Nat := none
  asmDir : String := "testbench/tests/generated/bench"
  outDir : String := "output/bench"
  dictPath : System.FilePath := Shoumei.RISCV.instrDictPath

def parseArgs (args : List String) (o : Options := {}) : Options :=
  match args with
  | [] => o
  | a :: rest =>
    let o := parseArgs rest o
    if a == "--short" then { o with isShort := true }
    else if a.startsWith "--iters=" then { o with iters := some (a.drop 8).toNat! }
    else if a.startsWith "--asm-dir=" then { o with asmDir := (a.drop 10).toString }
    else if a.startsWith "--out-dir=" then { o with outDir := (a.drop 10).toString }
    else if a.startsWith "--out=" then { o with outDir := (a.drop 6).toString }
    else if a.startsWith "--instr-dict=" then { o with dictPath := (a.drop 13).toString }
    else o

def main (args : List String) : IO Unit := do
  let opts := parseArgs args
  let iters := match opts.iters with
    | some n => n
    | none => if opts.isShort then cosimIters else Shoumei.RISCV.BENCH_ITERS
  let defaultAsmDir := if opts.isShort then "testbench/tests/generated/bench-short" else "testbench/tests/generated/bench"
  let defaultOutDir := if opts.isShort then "output/bench-short" else "output/bench"
  let asmDir := if opts.asmDir != "testbench/tests/generated/bench" || !opts.isShort then opts.asmDir else defaultAsmDir
  let outDir := if opts.outDir != "output/bench" || !opts.isShort then opts.outDir else defaultOutDir
  Shoumei.RISCV.emitAll (iters := iters) (asmDir := asmDir) (outDir := outDir) (dictPath := opts.dictPath)
