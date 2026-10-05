#!/usr/bin/env bash
set -euo pipefail

YOSYS="$1"
VERILATOR="$2"
SV_DIR="$3"
ASAP7_DIR="$4"
GF180_DIR="$5"
SEC_DIR="$6"
CPP_SIM_DIR="$7"
GEN_ARG="$8"

# The pinned tools, not the ones on the host.
source verification/tool_path.sh
tool_path "$YOSYS"
tool_path "$VERILATOR"

ROOT="$(pwd)"
GEN="$(cd "$(dirname "$GEN_ARG")" && pwd)/$(basename "$GEN_ARG")"

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

for item in lean physical scripts verification testbench; do
    if [ -e "$item" ]; then
        ln -s "$ROOT/$item" "$TMP/$item"
    fi
done

mkdir -p "$TMP/output"
ln -s "$(cd "$SV_DIR" && pwd)" "$TMP/output/sv-from-lean"
ln -s "$(cd "$ASAP7_DIR" && pwd)" "$TMP/output/sv-asap7"
ln -s "$(cd "$GF180_DIR" && pwd)" "$TMP/output/sv-gf180"
ln -s "$(cd "$SEC_DIR" && pwd)" "$TMP/output/sv-sec"
ln -s "$(cd "$CPP_SIM_DIR" && pwd)" "$TMP/output/cpp_sim"

export SMOKE_ROOT="$TMP"
export GENERATOR="$GEN"
export VISUALS_GENERATOR="$GEN"
export SKIP_CACHE_CONFORMANCE=1

"$ROOT/verification/smoke-test.sh"
