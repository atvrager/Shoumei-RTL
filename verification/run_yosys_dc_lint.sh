#!/usr/bin/env bash
set -euo pipefail

YOSYS="$1"
SV_DIR="$2"
GEN_ARG="$3"
GEN="$(cd "$(dirname "$GEN_ARG")" && pwd)/$(basename "$GEN_ARG")"

# The pinned yosys, not the one on the host.
source verification/tool_path.sh
tool_path "$YOSYS"

export GENERATOR="$GEN"
./verification/dc-lint.sh "$SV_DIR"
