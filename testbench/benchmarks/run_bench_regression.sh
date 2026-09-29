#!/usr/bin/env bash
set -euo pipefail

SIM_BIN="$1"; shift
BENCH_REGRESSION="$1"; shift
BASELINE="$1"; shift
MANIFEST="$1"; shift

TMP_DIR="${TEST_TMPDIR:-$(mktemp -d)}"
METRICS_CSV="$TMP_DIR/bench-metrics.csv"
echo "name,peak_ipc_milli,dependent_ipc_milli" > "$METRICS_CSV"

for elf in "$@"; do
    output=$("$SIM_BIN" +elf="$elf" +timeout=200000 2>&1)
    echo "$output" | grep '^BENCH ' | sed 's/^BENCH //; s/ /,/g' >> "$METRICS_CSV"
done

echo "Extracted metrics:"
cat "$METRICS_CSV"

python3 "$BENCH_REGRESSION" \
    --metrics "$METRICS_CSV" \
    --baseline "$BASELINE" \
    --only add,mul,fadd_s,fmul_s,ld,sd,beq,jal

echo "✓ Benchmark regression check passed"
