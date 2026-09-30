#!/usr/bin/env bash
set -euo pipefail

YOSYS="$1"
SV_DIR="$2"

# The pinned yosys, not the one on the host.
source verification/tool_path.sh
tool_path "$YOSYS"

./verification/validate-sv.sh "$SV_DIR"
