#!/usr/bin/env bash
# verification/run_proof_coverage.sh - Hermetic runner for proof_coverage_test under Bazel
set -euo pipefail

ROOT="${TEST_SRCDIR}/${TEST_WORKSPACE}"
if [ ! -d "$ROOT/lean/Shoumei" ]; then
    ROOT="."
fi

export PROJECT_ROOT="$ROOT"
export LEAN_DIR="$ROOT/lean/Shoumei"
export REPORT_DIR="${TEST_TMPDIR:-$ROOT/output/proof-coverage}"
export STRICT=1

exec bash "$ROOT/verification/proof-coverage.sh"
