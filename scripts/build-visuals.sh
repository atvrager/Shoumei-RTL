#!/usr/bin/env bash
# build-visuals.sh - synth both netlists (flat + hierarchical), compile the
# viewer and render the full visualization suite into output/architecture-visuals.
#
# Shared by the visuals publish job and the PR-side visuals-check; keeps the
# suite-building steps in one place.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

cd "$ROOT"

make synth-gf180
make synth-asap7

# Module-first cell charts need the unflattened netlists
FLATTEN=0 OUTPUT_DIR=syn_out_gf180_hier ./physical/run-yosys-gf180.sh
FLATTEN=0 OUTPUT_DIR=syn_out_asap7_hier ./physical/run-yosys-asap7.sh

npx -y -p typescript@5.5.4 tsc -p viewer/tsconfig.json

mkdir -p output/architecture-visuals
cp viewer/viewer.html viewer/dist/viewer.js viewer/dist/schema.gen.js output/architecture-visuals/
lake --no-ansi exe generate_all --visuals
# Benchmarks page is self-contained; falls back to a no-CPI table when the
# bench data artifacts (output/bench) are absent, so PR-side visuals-check
# does not need the RISC-V toolchain or a Verilator run.
python3 scripts/gen-benchmark-visual.py || true

echo "✓ visual suite ready in output/architecture-visuals"