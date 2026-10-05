/-
GenerateVisuals.lean - Standalone CLI for generating architecture visuals.

Emits architecture diagrams, treemaps, sunbursts, 3D models, and benchmark plots.

Usage:
  lake exe generate_visuals [--visuals] [--treemap] [--soc-diagram] [--benchmarks]
-/

import Shoumei.CircuitRegistry
import Shoumei.Codegen.ArchitectureDiagram
import Shoumei.Codegen.ArchitectureVisuals
import Shoumei.Codegen.BenchmarkVisual
import Shoumei.Codegen.SoCDiagram
import Shoumei.RISCV.CPU
import Shoumei.RISCV.Config

open Shoumei.CircuitRegistry
open Shoumei.RISCV

def main (args : List String) : IO Unit := do
  let cpuCfg := defaultCPUConfig
  let top := CPU_W2.mkCPU_W2 cpuCfg

  if args.contains "--treemap" then
    Shoumei.Codegen.ArchitectureDiagram.generate allCircuits top
    return
  if args.contains "--soc-diagram" then
    Shoumei.Codegen.SoCDiagram.generate cpuCfg
    return
  if args.contains "--benchmarks" || args.contains "--benchmark-visual" then
    Shoumei.Codegen.BenchmarkVisual.generateBenchmarks
    return

  -- Default or --visuals: generate the complete visual suite
  Shoumei.Codegen.SoCDiagram.generate cpuCfg
  Shoumei.Codegen.BenchmarkVisual.generateBenchmarks
  Shoumei.Codegen.ArchitectureVisuals.generateAllVisuals allCircuits top
