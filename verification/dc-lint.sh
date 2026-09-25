#!/usr/bin/env bash
# DC-NXT-style lint for emitted SystemVerilog, proxied with Yosys.
#
# Synopsys DC NXT is not publicly runnable here, so each LINT-* class is
# mimicked with an aggressive Yosys pass that FAILS on the first pop:
#
#   LINT-1  inferred latches          -> read_verilog -nolatches + $dlatch assert
#   LINT-2  combinational loops       -> check -assert (cyclic net detection)
#   LINT-3  multiple drivers          -> hierarchy -check
#   LINT-4  undriven / unconnected    -> hierarchy -check + check -assert
#   LINT-5  width mismatches          -> read_verilog warnings (fatal here)
#   LINT-7  tristate/unexpected cells -> select -assert-none t:$tribuf
#   LINT-11 latch-y always_comb       -> proc + $dlatch assert
#
# Usage: verification/dc-lint.sh [sv_dir]
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
SV_DIR="${1:-${PROJECT_ROOT}/output/sv-from-lean}"

if ! command -v yosys > /dev/null 2>&1; then
    echo "ERROR: yosys not found"
    exit 1
fi
if [[ ! -d "$SV_DIR" ]]; then
    echo "ERROR: no SV dir: $SV_DIR (run make codegen first)"
    exit 1
fi

LOG=$(mktemp); trap 'rm -f "$LOG"' EXIT

echo "==> DC-NXT-style lint (Yosys proxy): $SV_DIR"

# A synthesis flow never sees the DPI simulation models: it selects the
# `SHOUMEI_SRAM_MACROS` branch and binds real macros.  Mirror that here -
# define the macro and read behavioural stubs for exactly the geometries the
# RTL instantiates - so the lint exercises the same RTL that is synthesised.
# (Yosys cannot parse `import "DPI-C"`, which is simulation-only syntax.)
STUB_DIR=$(mktemp -d); trap 'rm -rf "$STUB_DIR"' EXIT
"$PROJECT_ROOT/scripts/gen-sram-macros.sh" --stub --out "$STUB_DIR" > /dev/null

# Build the aggressive Yosys script
SCRIPT=$(mktemp); trap 'rm -f "$SCRIPT"' EXIT
{
  find "$STUB_DIR" -maxdepth 1 -name '*.sv' -type f | sort | while read -r f; do
    echo "read_verilog -sv -nolatches \"$f\""
  done
  find "$SV_DIR" -maxdepth 1 -name '*.sv' -type f | sort | while read -r f; do
    echo "read_verilog -sv -nolatches -DSHOUMEI_SRAM_MACROS \"$f\""
  done
  echo "hierarchy -auto-top -check"
  echo "proc; opt"
  echo "select -assert-none t:\$dlatch"
  echo "check -assert"
  echo "select -assert-none t:\$tribuf"
} > "$SCRIPT"

set +e
yosys -q -s "$SCRIPT" > "$LOG" 2>&1
RC=$?
set -e

# Lint pops: any yosys Warning/ERROR in read/elab is treated as a DC-LINT hit.
LINT_HITS=$(grep -nE "Warning:.*(width|Width|latch|multiple driver|driven by|unused|does not match|unsized|unexpected|non-constant)|ERROR:|Assertion.*fail|assert.*failed" "$LOG" || true)

if [[ $RC -ne 0 ]] || [[ -n "$LINT_HITS" ]]; then
    echo "✗ LINT FAILURES:"
    grep -nE "Warning:|ERROR:|Assert|assert" "$LOG" | head -40 || true
    exit 1
fi

echo "==> LINT-31/32/33 structural check (double-connects, undriven, ties)..."
lake --no-ansi exe generate_all --lint-structural --sv-dir="$SV_DIR"

echo "✓ LINT clean (no latches, no comb loops, no width/undriven/multi-driver pops)"
exit 0