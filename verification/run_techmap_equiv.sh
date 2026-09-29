#!/usr/bin/env bash
set -euo pipefail

GOLD_DIR="$1"
ASAP7_DIR="$2"
GF180_DIR="$3"
CELL_MODELS="$4"
shift 4

./verification/techmap-equiv.sh \
    --gold-dir "$GOLD_DIR" \
    --asap7-dir "$ASAP7_DIR" \
    --gf180-dir "$GF180_DIR" \
    --cell-models "$CELL_MODELS" \
    "$@"
