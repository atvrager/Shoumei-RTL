#!/usr/bin/env bash
set -euo pipefail

YOSYS="$1"
GOLD_DIR="$2"
ASAP7_DIR="$3"
GF180_DIR="$4"
CELL_MODELS="$5"
shift 5

# The pinned yosys, not the one on the host.
source verification/tool_path.sh
tool_path "$YOSYS"

./verification/techmap-equiv.sh \
    --gold-dir "$GOLD_DIR" \
    --asap7-dir "$ASAP7_DIR" \
    --gf180-dir "$GF180_DIR" \
    --cell-models "$CELL_MODELS" \
    "$@"
