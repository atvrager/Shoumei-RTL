#!/usr/bin/env bash
# verification/run_yosys_synth.sh - Hermetic physical synthesis test under Bazel
set -euo pipefail

if [ $# -lt 4 ]; then
    echo "Usage: $0 <platform> <design_name> <clk_period_ns> <sv_dir>" >&2
    exit 1
fi

PLATFORM="$1"
DESIGN_NAME="$2"
CLK_PERIOD_NS="$3"
SV_DIR_ARG="$(cd "$4" && pwd)"

ROOT="${TEST_SRCDIR:-}/${TEST_WORKSPACE:-}"
if [ -z "${TEST_SRCDIR:-}" ] || [ ! -d "$ROOT/physical" ]; then
    ROOT="."
fi

WORK_DIR="${TEST_TMPDIR:-/tmp}/synth_${PLATFORM}_${DESIGN_NAME}"
rm -rf "$WORK_DIR"
mkdir -p "$WORK_DIR"

PLATFORMS_DIR=""
for cand in \
    "$ROOT/third_party/orfs/flow/platforms" \
    "${TEST_SRCDIR:-}/_main/external/+pdk_ext+orfs_pdk/platforms" \
    "${RUNFILES_DIR:-}/_main/external/+pdk_ext+orfs_pdk/platforms" \
    "${TEST_SRCDIR:-}/orfs_pdk/platforms" \
    "${RUNFILES_DIR:-}/orfs_pdk/platforms" \
    $(find "${TEST_SRCDIR:-/nonexistent}" -type d -name "platforms" 2>/dev/null || true); do
    if [ -d "$cand/gf180" ] && [ -d "$cand/asap7" ]; then
        PLATFORMS_DIR="$cand"
        break
    fi
done

if [ -z "$PLATFORMS_DIR" ]; then
    echo "ERROR: Could not locate ORFS platforms directory in workspace or runfiles." >&2
    exit 1
fi

if [ "$PLATFORM" = "gf180" ]; then
    LIB_GZ="$PLATFORMS_DIR/gf180/lib/gf180mcu_fd_sc_mcu9t5v0__tt_025C_5v00.lib.gz"
    if [ ! -f "$LIB_GZ" ]; then
        echo "ERROR: GF180 liberty file not found: $LIB_GZ" >&2
        exit 1
    fi
    gunzip -c "$LIB_GZ" > "$WORK_DIR/target.lib"
    TARGET_LIB="$WORK_DIR/target.lib"
    DFF_LIB="$TARGET_LIB"
    export ABC_DRIVER_CELL="gf180mcu_fd_sc_mcu9t5v0__buf_4"
    export ABC_LOAD_IN_FF="13.43"
elif [ "$PLATFORM" = "asap7" ]; then
    ASAP7_DIR="$PLATFORMS_DIR/asap7"
    ASAP7_NLDM="$ASAP7_DIR/lib/NLDM"
    DFF_LIB="$ASAP7_NLDM/asap7sc7p5t_SEQ_RVT_TT_nldm_220123.lib"
    if [ ! -f "$DFF_LIB" ]; then
        echo "ERROR: ASAP7 DFF library not found: $DFF_LIB" >&2
        exit 1
    fi
    COMB_LIBS=(
        "$ASAP7_NLDM/asap7sc7p5t_INVBUF_RVT_TT_nldm_220122.lib.gz"
        "$ASAP7_NLDM/asap7sc7p5t_SIMPLE_RVT_TT_nldm_211120.lib.gz"
        "$ASAP7_NLDM/asap7sc7p5t_OA_RVT_TT_nldm_211120.lib.gz"
        "$ASAP7_NLDM/asap7sc7p5t_AO_RVT_TT_nldm_211120.lib.gz"
    )
    for lib in "${COMB_LIBS[@]}"; do
        if [ ! -f "$lib" ]; then
            echo "ERROR: Required ASAP7 library not found: $lib" >&2
            exit 1
        fi
    done
    python3 -c '
import gzip, sys
files = sys.argv[1:-1]
out_path = sys.argv[-1]
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
' "${COMB_LIBS[@]}" "$WORK_DIR/asap7_comb_merged.lib"
    TARGET_LIB="$WORK_DIR/asap7_comb_merged.lib"
else
    echo "ERROR: Unsupported platform: $PLATFORM" >&2
    exit 1
fi

export PLATFORM
export DESIGN_NAME
export CLK_PERIOD_NS
export OUTPUT_DIR="$WORK_DIR/syn_out_${PLATFORM}"
export TARGET_LIBRARY="$TARGET_LIB"
export DFF_LIBRARY="$DFF_LIB"
export RTL_DIR="$SV_DIR_ARG"
export IGNORE_MISS_FUNC=1
export SYNTH_WRAPPER=""
if [ -f "$ROOT/physical/${DESIGN_NAME}.sv" ]; then
    export SYNTH_WRAPPER="$ROOT/physical/${DESIGN_NAME}.sv"
fi

mkdir -p "$OUTPUT_DIR/reports"
mkdir -p "$OUTPUT_DIR/netlist"

echo "==> Running Yosys synthesis for $DESIGN_NAME on $PLATFORM (${CLK_PERIOD_NS} ns)..."
yosys -c "$ROOT/physical/run-yosys.tcl" > "$OUTPUT_DIR/synth.log" 2>&1 || {
    echo "ERROR: Yosys synthesis failed! Log:" >&2
    cat "$OUTPUT_DIR/synth.log" >&2
    exit 1
}

NETLIST="$OUTPUT_DIR/netlist/${DESIGN_NAME}.v"
SDC="$OUTPUT_DIR/netlist/${DESIGN_NAME}.sdc"
AREA_RPT="$OUTPUT_DIR/reports/area.rpt"
CHECK_RPT="$OUTPUT_DIR/reports/check_design.rpt"

for f in "$NETLIST" "$SDC" "$AREA_RPT" "$CHECK_RPT"; do
    if [ ! -s "$f" ]; then
        echo "ERROR: Expected non-empty synthesis output missing: $f" >&2
        exit 1
    fi
done

CELL_COUNT=$(grep -E 'Number of cells:\s+[0-9]+' "$AREA_RPT" | head -n 1 | awk '{print $NF}' || echo "0")
echo "✓ Synthesis passed for $DESIGN_NAME on $PLATFORM ($CELL_COUNT cells)"
