#!/usr/bin/env bash
# run_lean_lint.sh - the Shoumei style linter over the Lean sources.
set -euo pipefail

LINT="$(realpath "$1")"

ROOT="${TEST_SRCDIR}/${TEST_WORKSPACE}"
if [ ! -d "$ROOT/lean" ]; then
    ROOT="."
fi

cd "$ROOT"

"$LINT" lean generators
