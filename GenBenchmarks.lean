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

def main (args : List String) : IO Unit := do
  if args.contains "--short" then
    Shoumei.RISCV.emitAll (iters := cosimIters)
      (asmDir := "testbench/tests/generated/bench-short")
      (outDir := "output/bench-short")
  else
    Shoumei.RISCV.emitAll
