#!/usr/bin/env bash
# run_ruff.sh - lint and format check for every Python file in the workspace.
set -euo pipefail

RUFF="$1"
CONFIG="$2"

ROOT="${TEST_SRCDIR}/${TEST_WORKSPACE}"
if [ ! -d "$ROOT/verification" ]; then
    ROOT="."
fi

cd "$ROOT"

"$RUFF" check --config "$ROOT/$CONFIG" .
"$RUFF" format --check --config "$ROOT/$CONFIG" .
