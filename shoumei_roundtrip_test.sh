#!/usr/bin/env bash
set -euo pipefail

GEN_ARG="$1"
GEN="$(cd "$(dirname "$GEN_ARG")" && pwd)/$(basename "$GEN_ARG")"

cd "$TEST_TMPDIR"
"$GEN"
echo "PASS: shoumei roundtrip verified"
