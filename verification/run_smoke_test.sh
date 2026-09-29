#!/usr/bin/env bash
set -euo pipefail

SV_DIR="$1"
ASAP7_DIR="$2"
GF180_DIR="$3"
SEC_DIR="$4"
CPP_SIM_DIR="$5"
GEN_ARG="$6"

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
export SKIP_CACHE_CONFORMANCE=1

"$ROOT/verification/smoke-test.sh"
