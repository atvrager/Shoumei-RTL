#!/usr/bin/env bash
# run_mutation_test.sh - Hermetic runner for mutation_test under Bazel
#
# The Lean compiler comes from the toolchain. The library oleans come from the
# runfiles. The test reads nothing from the host.
set -euo pipefail

LEAN_BIN="$1"

ROOT="${TEST_SRCDIR}/${TEST_WORKSPACE}"
if [ ! -d "$ROOT/lean/Shoumei" ]; then
    ROOT="."
fi

# shellcheck source=verification/lean_env.sh
. "$ROOT/verification/lean_env.sh"
lean_env "$LEAN_BIN" "$ROOT"

WS="${TEST_TMPDIR:-/tmp}/mutation_ws"
mkdir -p "$WS"
cp -rL "$ROOT/lean" "$WS/"
if [ -f "$ROOT/lean-toolchain" ]; then
    cp -L "$ROOT/lean-toolchain" "$WS/"
fi
mkdir -p "$WS/verification"
cp -L "$ROOT/verification/mutation-test.sh" "$WS/verification/"

export PROJECT_ROOT="$WS"
export REPORT_DIR="${TEST_TMPDIR:-$WS/output/mutation-test}"
export LEAN_PATH="$LIB_LEAN_PATH"

cd "$WS"
exec bash "$WS/verification/mutation-test.sh"
