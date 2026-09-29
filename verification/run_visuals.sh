#!/usr/bin/env bash
# verification/run_visuals.sh - Visual suite generator test under Bazel
set -euo pipefail

if [ $# -lt 1 ]; then
    echo "Usage: $0 <generate_all_bin>" >&2
    exit 1
fi

GENERATE_ALL_BIN="$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"

ROOT="${TEST_SRCDIR:-}/${TEST_WORKSPACE:-}"
if [ -z "${TEST_SRCDIR:-}" ] || [ ! -d "$ROOT/verification" ]; then
    ROOT="."
fi

WORK_DIR="${TEST_TMPDIR:-/tmp}/visuals_work"
rm -rf "$WORK_DIR"
mkdir -p "$WORK_DIR"

cd "$WORK_DIR"

echo "==> Running visual suite generation..."
"$GENERATE_ALL_BIN" --visuals

EXPECTED=(
    "output/architecture-visuals/soc-diagram.html"
    "output/architecture-visuals/index.html"
    "output/architecture-visuals/architecture-treemap.svg"
    "output/architecture-visuals/treemap-lean.svg"
    "output/architecture-visuals/sunburst-lean.svg"
    "output/architecture-visuals/city-lean.html"
    "output/architecture-visuals/tree-lean.html"
    "output/architecture-visuals/treemap-netlist.svg"
    "output/architecture-visuals/sunburst-netlist.svg"
    "output/architecture-visuals/city-netlist.html"
    "output/architecture-visuals/tree-netlist.html"
)

for f in "${EXPECTED[@]}"; do
    if [ ! -s "$f" ]; then
        echo "ERROR: Expected visual artifact missing or empty: $f" >&2
        exit 1
    fi
done

echo "✓ Visual suite generation passed (all 11 visual artifacts present and valid)"
