#!/bin/bash
# Export physical design artifacts from ORFS flow directory
# Usage: ./physical/export-artifacts.sh [target-dir]
#   target-dir defaults to /tmp/<design-name>-<timestamp>

set -euo pipefail

FLOW_DIR="$(git rev-parse --show-toplevel)/third_party/orfs/flow"
DESIGN="${DESIGN_NAME:-CPU_RV32IMF_Zicsr_Zifencei_synth}"
PLATFORM="${PLATFORM:-asap7}"
BASE="${PLATFORM}/${DESIGN}/base"

if [ -n "${1:-}" ]; then
    TARGET="$1"
else
    TARGET="/tmp/${DESIGN}-$(date +%Y%m%d-%H%M%S)"
fi

mkdir -p "$TARGET"

for dir in logs reports results objects; do
    src="${FLOW_DIR}/${dir}/${BASE}"
    if [ -d "$src" ]; then
        echo "Copying ${dir}/ ..."
        mkdir -p "${TARGET}/${dir}"
        cp -a "$src"/. "${TARGET}/${dir}/"
    else
        echo "Skipping ${dir}/ (not found: $src)"
    fi
done

echo ""

# Generate layout images if GDS exists
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
GDS="${FLOW_DIR}/results/${BASE}/6_final.gds"
if [ -f "$GDS" ]; then
    echo "Generating layout images..."
    "${SCRIPT_DIR}/export-layout-png.py" "$GDS" "${TARGET}/layout-layers.png" 2>&1 || echo "  (layer image failed)"
    "${SCRIPT_DIR}/export-layout-png.py" --mode modules "$GDS" "${TARGET}/layout-modules.png" 2>&1 || echo "  (module image failed)"
else
    echo "No GDS found at $GDS — skipping image generation"
fi

echo ""
echo "Exported to: $TARGET"
du -sh "$TARGET"
