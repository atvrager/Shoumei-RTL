#!/usr/bin/env bash
# Run Yosys synthesis targeting GlobalFoundries GF180MCU standard cells
#
# Usage:
#   ./physical/run-yosys-gf180.sh                                                # RV64 CPU at 64 MHz (15.625 ns, default)
#   ./physical/run-yosys-gf180.sh CPU_RV64IMAFD_Zicsr_Zifencei_Microcoded_synth 20.0    # 50 MHz conservative target
#   ./physical/run-yosys-gf180.sh ALU64 10.0                                     # Subsystem
#
# Environment variables:
#   DESIGN_NAME       - Top-level module name
#   CLK_PERIOD_NS     - Clock period in nanoseconds (default: 15.625 -> 64 MHz)
#   TRACK_OPTION      - 9t (default) or 7t
#   VOLTAGE_OPTION    - 5v0 (default), 3v3, or 1v8
#   OUTPUT_DIR        - Directory for output artifacts (default: syn_out_gf180)

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

cd "$PROJECT_ROOT"

# Check prerequisites
if ! command -v yosys > /dev/null 2>&1; then
    echo "ERROR: yosys not found. Please install Yosys."
    exit 1
fi

# Parse positional arguments
if [ -n "${1:-}" ]; then
    DESIGN_NAME="$1"
else
    DESIGN_NAME="${DESIGN_NAME:-CPU_RV64IMAFD_Zicsr_Zifencei_Microcoded_synth}"
fi

if [ -n "${2:-}" ]; then
    CLK_PERIOD_NS="$2"
else
    CLK_PERIOD_NS="${CLK_PERIOD_NS:-15.625}"
fi

TRACK_OPTION="${TRACK_OPTION:-9t}"
VOLTAGE_OPTION="${VOLTAGE_OPTION:-5v0}"
OUTPUT_DIR="${OUTPUT_DIR:-syn_out_gf180}"

# Check generated SystemVerilog exists
SV_DIR="$PROJECT_ROOT/output/sv-from-lean"
if [ ! -d "$SV_DIR" ] || [ -z "$(find "$SV_DIR" -maxdepth 1 -name "*.sv" -print -quit 2>/dev/null)" ]; then
    echo "ERROR: Generated SystemVerilog not found under $SV_DIR."
    echo "Run: make codegen"
    exit 1
fi

# Target library resolution
VOLT_SUFFIX="${VOLTAGE_OPTION}0"
LIB_PATH="$PROJECT_ROOT/third_party/orfs/flow/platforms/gf180/lib/gf180mcu_fd_sc_mcu${TRACK_OPTION}${VOLTAGE_OPTION}__tt_025C_${VOLT_SUFFIX}.lib.gz"
if [ ! -f "$LIB_PATH" ]; then
    echo "ERROR: GF180MCU liberty library not found: $LIB_PATH"
    exit 1
fi

FREQ_MHZ=$(awk "BEGIN {printf \"%.1f\", 1000.0 / $CLK_PERIOD_NS}")

echo "========================================"
echo "  Shoumei RTL - GF180MCU Yosys Synthesis"
echo "========================================"
echo "  Design:        $DESIGN_NAME"
echo "  Clock target:  ${CLK_PERIOD_NS} ns (${FREQ_MHZ} MHz)"
echo "  Track option:  $TRACK_OPTION"
echo "  Voltage:       $VOLTAGE_OPTION"
echo "  Output dir:    $OUTPUT_DIR"
echo "  Target lib:    $LIB_PATH"
echo "========================================"
echo ""

mkdir -p "$OUTPUT_DIR"

# Decompress liberty file to output dir if gzipped (required for older Yosys like 0.33 on Ubuntu)
if [[ "$LIB_PATH" == *.gz ]]; then
    LIB_BASENAME="$(basename "$LIB_PATH" .gz)"
    UNCOMPRESSED_LIB="$OUTPUT_DIR/$LIB_BASENAME"
    if [ ! -f "$UNCOMPRESSED_LIB" ]; then
        echo "==> Decompressing GF180MCU liberty file..."
        gunzip -c "$LIB_PATH" > "$UNCOMPRESSED_LIB"
    fi
    TARGET_LIB="$UNCOMPRESSED_LIB"
else
    TARGET_LIB="$LIB_PATH"
fi

export PLATFORM="gf180"
export DESIGN_NAME
export CLK_PERIOD_NS
export TRACK_OPTION
export VOLTAGE_OPTION
export OUTPUT_DIR
export TARGET_LIBRARY="$TARGET_LIB"
export DFF_LIBRARY="$TARGET_LIB"
export IGNORE_MISS_FUNC=1
export ABC_DRIVER_CELL="gf180mcu_fd_sc_mcu${TRACK_OPTION}${VOLTAGE_OPTION}__buf_4"
export ABC_LOAD_IN_FF="13.43"

LOG_FILE="$OUTPUT_DIR/synth.log"
VERBOSE="${VERBOSE:-0}"

echo "==> Running Yosys synthesis (log: $LOG_FILE, verbose: $VERBOSE)..."

START_TIME=$(date +%s)
SYNTH_STATUS=0
if [ "$VERBOSE" -eq 1 ]; then
    yosys -c "$SCRIPT_DIR/run-yosys.tcl" 2>&1 | tee "$LOG_FILE" || SYNTH_STATUS=$?
else
    yosys -c "$SCRIPT_DIR/run-yosys.tcl" > "$LOG_FILE" 2>&1 || SYNTH_STATUS=$?
fi

if [ "$SYNTH_STATUS" -eq 0 ]; then
    END_TIME=$(date +%s)
    ELAPSED=$((END_TIME - START_TIME))

    echo ""
    echo "========================================"
    echo "✓ GF180MCU synthesis complete in ${ELAPSED}s"
    echo "========================================"
    echo "Netlist: $OUTPUT_DIR/netlist/${DESIGN_NAME}.v"
    echo "SDC:     $OUTPUT_DIR/netlist/${DESIGN_NAME}.sdc"
    echo "Area:    $OUTPUT_DIR/reports/area.rpt"
    echo "Check:   $OUTPUT_DIR/reports/check_design.rpt"
    echo ""

    if [ -f "$OUTPUT_DIR/reports/area.rpt" ]; then
        echo "Summary from area report:"
        grep -E "(Chip area for top module|wires|cells|used for sequential elements)" "$OUTPUT_DIR/reports/area.rpt" | tail -n 6 || true
    fi

    # Aggressive lint pop (DC NXT LINT-* mimic): elaboration-stage linty
    # warnings are fatal even when synthesis "succeeds".
    LINT_HITS=$(grep -nE "multiple driv|Width of|width.*does not match|unsized|inferred latch|\\\$dlatch|comb loop|combinational|is used but never|never driven|tristate" "$LOG_FILE" || true)
    if [ -n "$LINT_HITS" ]; then
        echo ""
        echo "ERROR: lint-style warnings in elaboration (mimicking DC NXT LINT-*):"
        echo "$LINT_HITS" | head -30
        exit 1
    fi
else
    echo ""
    echo "ERROR: Yosys synthesis failed. Last 50 lines of $LOG_FILE:"
    tail -n 50 "$LOG_FILE"
    exit 1
fi
