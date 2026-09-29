#!/usr/bin/env bash
# verification/run_spec_shims.sh - Spec shims generator test under Bazel
set -euo pipefail

ROOT="${TEST_SRCDIR:-}/${TEST_WORKSPACE:-}"
if [ -z "${TEST_SRCDIR:-}" ] || [ ! -d "$ROOT/scripts" ]; then
    ROOT="."
fi

python3 "$ROOT/scripts/gen-spec-shims.py" --dry
echo "✓ Spec shims validation passed"
