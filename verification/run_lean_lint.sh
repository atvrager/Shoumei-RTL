#!/usr/bin/env bash
# run_lean_lint.sh - the Shoumei style linter over the Lean sources, plus the
# rule fixtures.
set -euo pipefail

LINT="$(realpath "$1")"

ROOT="${TEST_SRCDIR}/${TEST_WORKSPACE}"
if [ ! -d "$ROOT/lean" ]; then
    ROOT="."
fi

cd "$ROOT"

# The rule fixtures: each one names a finding the linter must report.
FIXTURES="${TEST_TMPDIR:-/tmp}/lean-lint-fixtures"
rm -rf "$FIXTURES"
mkdir -p "$FIXTURES"

printf 'def f : Nat := sorry\n' > "$FIXTURES/sorry.lean"
printf 'axiom g : Nat\n' > "$FIXTURES/axiom.lean"
printf '#eval 1 + 1\n' > "$FIXTURES/debug.lean"
printf 'def h : Nat := 1 \ndef i : Nat := 2\n' > "$FIXTURES/trailing.lean"
printf 'def clean : Nat := 1\n-- sorry, admit and #eval in a comment are fine\n' \
    > "$FIXTURES/clean.lean"

# Count the reported findings.  The linter exits 1 on a finding, so the call
# must not stop the script.
report_count() {
    local out
    out="$("$LINT" --baseline "$FIXTURES/absent-baseline.txt" "$1" 2>&1 || true)"
    printf '%s\n' "$out" | grep -c ': error:' || true
}

fail=0
for name in sorry axiom debug trailing; do
    count="$(report_count "$FIXTURES/$name.lean")"
    if [ "$count" -gt 0 ]; then
        echo "fixture $name: reported"
    else
        echo "fixture $name: no finding, the rule is broken" >&2
        fail=1
    fi
done

if [ "$(report_count "$FIXTURES/clean.lean")" -eq 0 ]; then
    echo "fixture clean: no finding"
else
    echo "fixture clean: reported a finding for clean input" >&2
    fail=1
fi

if [ "$fail" -ne 0 ]; then
    exit 1
fi

"$LINT" lean generators
