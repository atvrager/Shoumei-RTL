#!/usr/bin/env bash
set -euo pipefail

SV_DIR="$1"
GEN_ARG="$2"
GEN="$(cd "$(dirname "$GEN_ARG")" && pwd)/$(basename "$GEN_ARG")"

export GENERATOR="$GEN"
./verification/dc-lint.sh "$SV_DIR"
