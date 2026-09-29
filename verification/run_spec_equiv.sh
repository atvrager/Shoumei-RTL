#!/usr/bin/env bash
set -euo pipefail

SV_DIR="$1"
shift
export SV_DIR="$SV_DIR"

python3 scripts/spec-equiv.py --sv-dir "$SV_DIR" "$@"
