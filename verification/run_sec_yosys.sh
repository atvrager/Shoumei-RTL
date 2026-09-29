#!/usr/bin/env bash
set -euo pipefail

SEC_DIR="$1"
SV_DIR="$2"

./verification/sec-verify.sh --yosys --sec-dir "$SEC_DIR" --sv-dir "$SV_DIR"
