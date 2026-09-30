#!/usr/bin/env bash
set -euo pipefail

YOSYS="$1"
SEC_DIR="$2"
SV_DIR="$3"

# The pinned yosys, not the one on the host.
source verification/tool_path.sh
tool_path "$YOSYS"

./verification/sec-verify.sh --yosys --sec-dir "$SEC_DIR" --sv-dir "$SV_DIR"
