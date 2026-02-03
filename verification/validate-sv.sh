#!/usr/bin/env bash
# Validate SystemVerilog modules using Yosys
# Usage: ./validate-sv.sh <sv_directory>

set -euo pipefail

# Script directory
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

# Color codes for output
GREEN='\033[0;32m'
RED='\033[0;31m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Check if yosys is available
if ! command -v yosys &> /dev/null; then
    echo -e "${RED}Error: yosys not found. Please install Yosys.${NC}"
    exit 1
fi

# Get SV directory from argument or use default
SV_DIR="${1:-${PROJECT_ROOT}/output/sv-from-lean}"

if [[ ! -d "$SV_DIR" ]]; then
    echo -e "${RED}Error: Directory not found: $SV_DIR${NC}"
    exit 1
fi

# Count SV files
SV_COUNT=$(find "$SV_DIR" -maxdepth 1 -name "*.sv" -type f 2>/dev/null | wc -l)

if [[ "$SV_COUNT" -eq 0 ]]; then
    echo -e "${YELLOW}Warning: No .sv files found in $SV_DIR${NC}"
    exit 0
fi

echo -e "${GREEN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo -e "${GREEN}SystemVerilog Validation${NC}"
echo -e "${GREEN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo "Directory: $SV_DIR"
echo "Modules: $SV_COUNT"
echo ""

# Temporary file for Yosys script
YOSYS_SCRIPT=$(mktemp)
trap 'rm -f "$YOSYS_SCRIPT"' EXIT

# Generate Yosys script to read all SV files
echo "# Auto-generated Yosys validation script" > "$YOSYS_SCRIPT"

# Find all SV files and add read commands
find "$SV_DIR" -maxdepth 1 -name "*.sv" -type f | sort | while read -r sv_file; do
    echo "read_verilog -sv \"$sv_file\"" >> "$YOSYS_SCRIPT"
done

# Add hierarchy check (without top module requirement)
echo "hierarchy -auto-top" >> "$YOSYS_SCRIPT"

# Run Yosys validation
echo -n "Running Yosys validation... "

# Capture output
YOSYS_OUTPUT=$(mktemp)
trap 'rm -f "$YOSYS_SCRIPT" "$YOSYS_OUTPUT"' EXIT

if yosys -q -s "$YOSYS_SCRIPT" 2>&1 | tee "$YOSYS_OUTPUT" | grep -E "(ERROR|Error)" > /dev/null; then
    echo -e "${RED}FAILED${NC}"
    echo ""
    echo -e "${RED}Validation errors found:${NC}"
    grep -E "(ERROR|Error)" "$YOSYS_OUTPUT" || true
    exit 1
else
    echo -e "${GREEN}PASSED${NC}"

    # Count and display all warnings
    WARNING_COUNT=$(grep "Warning:" "$YOSYS_OUTPUT" | wc -l || true)
    IMPLICIT_COUNT=$(grep "implicitly declared" "$YOSYS_OUTPUT" | wc -l || true)

    if [[ $WARNING_COUNT -gt 0 ]]; then
        echo ""
        echo -e "${YELLOW}Warnings ($WARNING_COUNT total):${NC}"

        if [[ $IMPLICIT_COUNT -gt 0 ]]; then
            echo -e "${YELLOW}  Implicit declarations: $IMPLICIT_COUNT${NC}"
            grep "implicitly declared" "$YOSYS_OUTPUT" | head -20 || true
            if [[ $IMPLICIT_COUNT -gt 20 ]]; then
                echo -e "${YELLOW}  ... and $((IMPLICIT_COUNT - 20)) more${NC}"
            fi
        fi

        OTHER_WARNINGS=$((WARNING_COUNT - IMPLICIT_COUNT))
        if [[ $OTHER_WARNINGS -gt 0 ]]; then
            echo ""
            echo -e "${YELLOW}  Other warnings: $OTHER_WARNINGS${NC}"
            grep "Warning:" "$YOSYS_OUTPUT" | grep -v "implicitly declared" || true
        fi
    fi

    echo ""
    echo -e "${GREEN}✓ All $SV_COUNT SystemVerilog modules validated successfully${NC}"
fi

exit 0
