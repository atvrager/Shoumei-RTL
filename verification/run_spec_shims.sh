#!/usr/bin/env bash
# verification/run_spec_shims.sh - Spec shims generator test under Bazel
set -euo pipefail

ROOT="${TEST_SRCDIR:-}/${TEST_WORKSPACE:-}"
if [ -z "${TEST_SRCDIR:-}" ] || [ ! -d "$ROOT/scripts" ]; then
    ROOT="."
fi

SV_DIR="${1:-$ROOT/output/sv-from-lean}"

python3 "$ROOT/scripts/gen-spec-shims.py" \
    --sv-dir="$SV_DIR" \
    --spec-dir="$ROOT/verification/specs" \
    --dual-rtl="$ROOT/lean/Shoumei/Verification/DualRTL.lean" \
    --dry
echo "✓ Spec shims validation passed"
