#!/usr/bin/env bash
set -euo pipefail

SV_DIR="$1"
CACHE_TEST_CPP="$2"
SRAM_DPI_C="$3"

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

verilator --cc --build -j "$(nproc)" --Mdir "$TMP/obj" \
    -Wno-fatal -O3 --top-module L1DCache --exe \
    "$SV_DIR/L1DCache.sv" \
    "$SV_DIR/Decoder6.sv" \
    "$SV_DIR/EqualityComparator20.sv" \
    "$SV_DIR/Mux64x20.sv" \
    "$SV_DIR/Mux16x32.sv" \
    "$SV_DIR/Mux8x32.sv" \
    "$SV_DIR/Mux4x32.sv" \
    "$SV_DIR/PLRU4.sv" \
    "$SV_DIR/Register20.sv" \
    -CFLAGS "-std=c++17 -O2" \
    -o "$TMP/cache_test" \
    "$CACHE_TEST_CPP" \
    "$SRAM_DPI_C"

"$TMP/cache_test" --cycles 2000
