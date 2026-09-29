#!/usr/bin/env bash
set -euo pipefail

BUNDLE="$1"
TMP_DIR="${TEST_TMPDIR:-$(mktemp -d)}"
EXTRACT_DIR="$TMP_DIR/extracted"
mkdir -p "$EXTRACT_DIR"

tar -xzf "$BUNDLE" -C "$EXTRACT_DIR"

REQUIRED=(
    "index.html"
    "viewer.html"
    "viewer.js"
    "schema.gen.js"
    "soc-diagram.html"
    "architecture-treemap.svg"
    "treemap-lean.svg"
    "sunburst-lean.svg"
    "city-lean.html"
    "tree-lean.html"
    "treemap-netlist.svg"
    "sunburst-netlist.svg"
    "city-netlist.html"
    "tree-netlist.html"
)

for f in "${REQUIRED[@]}"; do
    if [ ! -s "$EXTRACT_DIR/$f" ]; then
        echo "ERROR: Required bundle artifact missing or empty: $f" >&2
        exit 1
    fi
done

echo "✓ Verified GitHub Pages publication bundle (${#REQUIRED[@]} artifacts verified)"
