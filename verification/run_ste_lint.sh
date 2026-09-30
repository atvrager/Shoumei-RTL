#!/usr/bin/env bash
# run_ste_lint.sh - the ASD-STE100 prose check.
#
# Runs the rule regression tests, then lints the Markdown tree that is in the
# runfiles.  A prose error fails the test.
set -euo pipefail

LINT="$1"
UNIT="$2"

ROOT="${TEST_SRCDIR}/${TEST_WORKSPACE}"
if [ ! -d "$ROOT/docs" ]; then
    ROOT="."
fi

python3 "$ROOT/$UNIT"
python3 "$ROOT/$LINT" "$ROOT"/docs "$ROOT"/*.md
