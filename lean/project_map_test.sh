#!/usr/bin/env bash
set -euo pipefail

GEN="$1"
OUT="$TEST_TMPDIR/project-map.md"
"$GEN" --project-map --out="$OUT"
diff -u docs/project-map.md "$OUT"
echo "PASS: docs/project-map.md is current"
