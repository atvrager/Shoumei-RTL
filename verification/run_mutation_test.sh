#!/usr/bin/env bash
# verification/run_mutation_test.sh - Hermetic runner for mutation_test under Bazel
set -euo pipefail

ROOT="${TEST_SRCDIR}/${TEST_WORKSPACE}"
if [ ! -d "$ROOT/lean/Shoumei" ]; then
    ROOT="."
fi

for elan_cand in \
    "/usr/local/google/home/atv/.elan/toolchains/leanprover--lean4---v4.34.1/bin" \
    "$HOME/.elan/toolchains/leanprover--lean4---v4.34.1/bin" \
    "$HOME/.elan/bin" "$HOME/bin" \
    "/usr/local/google/home/atv/.elan/bin" "/usr/local/google/home/atv/bin"; do
    if [ -d "$elan_cand" ]; then
        export PATH="$elan_cand:$PATH"
    fi
done

if [ -d "/usr/local/google/home/atv/.elan" ] && [ ! -d "${HOME}/.elan" ]; then
    export ELAN_HOME="/usr/local/google/home/atv/.elan"
fi

WS="${TEST_TMPDIR:-/tmp}/mutation_ws"
mkdir -p "$WS"
cp -rL "$ROOT/lean" "$WS/"
cp -L "$ROOT/lakefile.lean" "$WS/"
cp -L "$ROOT/lean-toolchain" "$WS/"
if [ -f "$ROOT/lake-manifest.json" ]; then
    cp -L "$ROOT/lake-manifest.json" "$WS/"
fi
mkdir -p "$WS/verification"
cp -L "$ROOT/verification/mutation-test.sh" "$WS/verification/"

export PROJECT_ROOT="$WS"
export REPORT_DIR="${TEST_TMPDIR:-$WS/output/mutation-test}"

cd "$WS"
exec bash "$WS/verification/mutation-test.sh"
