#!/usr/bin/env bash
set -euo pipefail

FST_INSPECT="$1"

OUTPUT="$("$FST_INSPECT" --help 2>&1 || true)"
if echo "$OUTPUT" | grep -q "Cannot open FST file"; then
    echo "✓ fst_inspect invocation verified"
else
    echo "Unexpected output: $OUTPUT" >&2
    exit 1
fi
