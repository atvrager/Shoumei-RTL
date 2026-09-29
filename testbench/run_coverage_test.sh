#!/usr/bin/env bash
set -euo pipefail

SIM_COV="$1"
shift

TMP_DIR="${TEST_TMPDIR:-$(mktemp -d)}"
COV_DIR="$TMP_DIR/cov_data"
mkdir -p "$COV_DIR"

echo "==> Running coverage-instrumented simulation..."
for elf in "$@"; do
    name="$(basename "$elf")"
    dat="$COV_DIR/${name}.dat"
    "$SIM_COV" +elf="$elf" +timeout=50000 "+cov_file=$dat" >/dev/null 2>&1 || {
        echo "Failed to execute $elf under coverage simulation" >&2
        exit 1
    }
    if [ ! -s "$dat" ]; then
        echo "ERROR: Coverage data file empty: $dat" >&2
        exit 1
    fi
done

MERGED_DAT="$TMP_DIR/coverage_merged.dat"
MERGED_INFO="$TMP_DIR/coverage_merged.info"

echo "==> Merging coverage reports with verilator_coverage..."
verilator_coverage --write "$MERGED_DAT" "$COV_DIR"/*.dat
verilator_coverage --write-info "$MERGED_INFO" "$MERGED_DAT"

if [ ! -s "$MERGED_INFO" ]; then
    echo "ERROR: Merged coverage info file missing or empty" >&2
    exit 1
fi

TOTAL_LINES=$(grep -c '^DA:' "$MERGED_INFO" || true)
COVERED_LINES=$(grep '^DA:' "$MERGED_INFO" | grep -c -v ',0$' || true)

echo "Coverage summary:"
echo "  Total instrumentation points: $TOTAL_LINES"
echo "  Covered points:               $COVERED_LINES"

if [ "$COVERED_LINES" -eq 0 ]; then
    echo "ERROR: Zero coverage points recorded!" >&2
    exit 1
fi

echo "✓ Hardware coverage verification passed ($COVERED_LINES points covered)"
