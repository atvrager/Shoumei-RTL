#!/usr/bin/env bash
# run_ty.sh - type check every Python file in the workspace.
set -euo pipefail

TY="$1"

ROOT="${TEST_SRCDIR}/${TEST_WORKSPACE}"
if [ ! -d "$ROOT/verification" ]; then
    ROOT="."
fi

cd "$ROOT"

"$TY" check .
