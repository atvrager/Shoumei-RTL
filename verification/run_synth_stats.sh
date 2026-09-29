#!/usr/bin/env bash
# verification/run_synth_stats.sh - Synthesis statistics extractor test under Bazel
set -euo pipefail

ROOT="${TEST_SRCDIR:-}/${TEST_WORKSPACE:-}"
if [ -z "${TEST_SRCDIR:-}" ] || [ ! -d "$ROOT/scripts" ]; then
    ROOT="."
fi

WORK_DIR="${TEST_TMPDIR:-/tmp}/synth_stats_work"
rm -rf "$WORK_DIR"
mkdir -p "$WORK_DIR"

python3 "$ROOT/scripts/extract-synth-stats.py" --root "$WORK_DIR" --markdown
python3 "$ROOT/scripts/extract-synth-stats.py" --root "$WORK_DIR" --json

echo "✓ Synthesis stats extractor test passed"
