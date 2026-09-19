#!/usr/bin/env bash
# Run Yosys synthesis targeting ASAP7 7.5T RVT Predictive standard cells
#
# Usage:
#   ./physical/run-yosys-asap7.sh                                                # RV64 CPU at 1.0 GHz (1.000 ns, default)
#   ./physical/run-yosys-asap7.sh CPU_RV64IMAFD_Zicsr_Zifencei_Microcoded_synth 1.333   # 750 MHz matching GF12 baseline
#   ./physical/run-yosys-asap7.sh ALU64 1.0                                      # Subsystem
#
# Environment variables:
#   DESIGN_NAME       - Top-level module name
#   CLK_PERIOD_NS     - Clock period in nanoseconds (default: 1.0 -> 1.0 GHz)
#   OUTPUT_DIR        - Directory for output artifacts (default: syn_out_asap7)

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
    CLK_PERIOD_NS="${CLK_PERIOD_NS:-1.0}"
fi

OUTPUT_DIR="${OUTPUT_DIR:-syn_out_asap7}"

# Check generated SystemVerilog exists
SV_DIR="$PROJECT_ROOT/output/sv-from-lean"
if [ ! -d "$SV_DIR" ] || [ -z "$(find "$SV_DIR" -maxdepth 1 -name "*.sv" -print -quit 2>/dev/null)" ]; then
    echo "ERROR: Generated SystemVerilog not found under $SV_DIR."
    echo "Run: make codegen"
    exit 1
fi

# ASAP7 library directory
ASAP7_DIR="$PROJECT_ROOT/third_party/orfs/flow/platforms/asap7"
ASAP7_NLDM="$ASAP7_DIR/lib/NLDM"
DFF_LIB="$ASAP7_NLDM/asap7sc7p5t_SEQ_RVT_TT_nldm_220123.lib"

if [ ! -f "$DFF_LIB" ]; then
    echo "ERROR: ASAP7 sequential library not found: $DFF_LIB"
    exit 1
fi

mkdir -p "$OUTPUT_DIR"

# Auto-merge combinational ASAP7 Liberty libraries for ABC if needed
MERGED_COMB_LIB="$OUTPUT_DIR/asap7_comb_merged.lib"
COMB_LIBS=(
    "$ASAP7_NLDM/asap7sc7p5t_INVBUF_RVT_TT_nldm_220122.lib.gz"
    "$ASAP7_NLDM/asap7sc7p5t_SIMPLE_RVT_TT_nldm_211120.lib.gz"
    "$ASAP7_NLDM/asap7sc7p5t_OA_RVT_TT_nldm_211120.lib.gz"
    "$ASAP7_NLDM/asap7sc7p5t_AO_RVT_TT_nldm_211120.lib.gz"
)

for lib in "${COMB_LIBS[@]}"; do
    if [ ! -f "$lib" ]; then
        echo "ERROR: Required ASAP7 library not found: $lib"
        exit 1
    fi
done

if [ ! -f "$MERGED_COMB_LIB" ]; then
    echo "==> Preparing merged ASAP7 combinational cell library..."
    python3 -c '
import gzip, sys

files = [
    sys.argv[1],
    sys.argv[2],
    sys.argv[3],
    sys.argv[4],
]
out_path = sys.argv[5]

cells = []
header = None
for idx, f in enumerate(files):
    with gzip.open(f, "rt", encoding="utf-8") as fp:
        content = fp.read()
    cell_idx = content.find("cell (")
    if cell_idx != -1:
        if idx == 0:
            header = content[:cell_idx]
        last_brace = content.rfind("}")
        cells.append(content[cell_idx:last_brace])

if header is not None:
    merged = header + "\n" + "\n".join(cells) + "\n}\n"
    with open(out_path, "w", encoding="utf-8") as out:
        out.write(merged)
' "${COMB_LIBS[@]}" "$MERGED_COMB_LIB"
    echo "✓ Merged ASAP7 library generated at $MERGED_COMB_LIB"
fi

FREQ_MHZ=$(awk "BEGIN {printf \"%.1f\", 1000.0 / $CLK_PERIOD_NS}")

echo "========================================"
echo "  Shoumei RTL - ASAP7 Yosys Synthesis"
echo "========================================"
echo "  Design:        $DESIGN_NAME"
echo "  Clock target:  ${CLK_PERIOD_NS} ns (${FREQ_MHZ} MHz)"
echo "  Standard cell: 7.5T RVT (NLDM)"
echo "  Output dir:    $OUTPUT_DIR"
echo "  Comb lib:      $MERGED_COMB_LIB"
echo "  DFF lib:       $DFF_LIB"
echo "========================================"
echo ""

export PLATFORM="asap7"
export DESIGN_NAME
export CLK_PERIOD_NS
export OUTPUT_DIR
export TARGET_LIBRARY="$MERGED_COMB_LIB"
export DFF_LIBRARY="$DFF_LIB"
export IGNORE_MISS_FUNC=0
export ABC_DRIVER_CELL="BUFx2_ASAP7_75t_R"
export ABC_LOAD_IN_FF="3.898"

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
    echo "✓ ASAP7 synthesis complete in ${ELAPSED}s"
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

    # Aggressive lint pop (DC NXT LINT-* mimic)
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
