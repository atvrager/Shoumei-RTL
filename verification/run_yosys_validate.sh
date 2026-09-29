#!/usr/bin/env bash
set -euo pipefail

SV_DIR="$1"
./verification/validate-sv.sh "$SV_DIR"
