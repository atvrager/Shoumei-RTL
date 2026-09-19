/-
  GenBenchmarks.lean - Benchmark Generator Executable

  Generates one self-contained .S benchmark program per decoder instruction
  into testbench/tests/generated/bench/, plus the bench-programs.json manifest
  in output/bench/. The benchmark set is derived from the riscv-opcodes
  instruction table (the same table the CPU decoder is built from), never
  hand-written.

  Usage: lake exe gen_benchmarks
-/

import Shoumei.RISCV.BenchmarkSpecs

def main : IO Unit := do
  Shoumei.RISCV.emitAll