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

# The fixer fixtures: a reflow must not split a string literal.  Each long
# line holds a space that an incorrect scan takes for code.
A60="$(head -c 60 /dev/zero | tr '\0' a)"
printf 'def j : String := s!"{String.intercalate ", " ["%s", "b"]} c"\n' "$A60" \
    > "$FIXTURES/interp.lean"
printf 'def k : String := r"C:\\" ++ "%s b c d e f g h i j k l m n o p q"\n' "$A60" \
    > "$FIXTURES/raw.lean"

# The text of the literal that must come out of the reflow whole.
check_whole() {
    local name="$1" literal="$2" out
    out="$("$LINT" --print-fix "$FIXTURES/$name.lean" 2>&1 || true)"
    if printf '%s\n' "$out" | grep -qF -- "$literal"; then
        echo "fixer $name: literal kept whole"
    else
        echo "fixer $name: the reflow split a string literal:" >&2
        printf '%s\n' "$out" >&2
        fail=1
    fi
}
check_whole interp '", "'
check_whole raw "\"$A60 b c d e f g h i j k l m n o p q\""

# --fix rewrites files in place, so it must refuse unless git shows every
# Lean file under the roots as committed.  The fixture tree is not a git
# work tree, so git cannot vouch for it.
cp "$FIXTURES/raw.lean" "$FIXTURES/dirty.lean"
cp "$FIXTURES/raw.lean" "$FIXTURES/dirty.orig"
if "$LINT" --fix --baseline "$FIXTURES/absent-baseline.txt" "$FIXTURES/dirty.lean" \
    > "$FIXTURES/dirty.out" 2>&1; then
    echo "fixer dirty: --fix ran outside a clean git tree" >&2
    fail=1
elif ! cmp -s "$FIXTURES/dirty.lean" "$FIXTURES/dirty.orig"; then
    echo "fixer dirty: --fix changed a file it did not vouch for" >&2
    fail=1
else
    echo "fixer dirty: refused"
fi

if [ "$fail" -ne 0 ]; then
    exit 1
fi

"$LINT" lean generators
