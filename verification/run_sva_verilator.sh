#!/usr/bin/env bash
set -euo pipefail

SV_DIR="$1"

verilator --assert --lint-only \
    "$SV_DIR/Register64.sv" \
    "$SV_DIR/Register32.sv" \
    "$SV_DIR/Register160.sv" \
    --top-module Register160

verilator --assert --lint-only \
    "$SV_DIR/LogicUnit32.sv" \
    --top-module LogicUnit32

verilator -I"$SV_DIR" --assert --lint-only \
    "$SV_DIR/Mux4x32.sv" \
    "$SV_DIR/Mux8x32.sv" \
    --top-module Mux8x32

verilator --assert --lint-only \
    "$SV_DIR/Popcount8.sv" \
    --top-module Popcount8

echo "PASS: Verilator SVA assertions compiled and verified"
