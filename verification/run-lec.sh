#!/bin/bash
# Logical Equivalence Checking with Yosys
# Provides detailed diagnostics on success or failure

set -e

LEAN_DIR="${1:-output/sv-from-lean}"
CHISEL_DIR="${2:-output/sv-from-chisel}"

# Colors
GREEN='\033[0;32m'
RED='\033[0;31m'
YELLOW='\033[1;33m'
NC='\033[0m'

echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "  証明 Shoumei RTL - LEC with Yosys"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

# Find all LEAN-generated modules
LEAN_MODULES=$(find "$LEAN_DIR" -maxdepth 1 \( -name "*.sv" -o -name "*.v" \) 2>/dev/null | sort)

if [ -z "$LEAN_MODULES" ]; then
    echo -e "${RED}✗ No LEAN-generated modules found in $LEAN_DIR${NC}"
    exit 1
fi

# Count modules and show what we'll verify
MODULE_COUNT=$(echo "$LEAN_MODULES" | wc -l)
echo "Found $MODULE_COUNT module(s) to verify:"
echo "$LEAN_MODULES" | while read -r file; do
    echo "  - $(basename "$file" .sv)"
done
echo ""

# Track overall success
ALL_PASSED=1

# Create temporary working directory
TMPDIR=$(mktemp -d)
trap 'rm -rf "$TMPDIR"' EXIT

# Function to verify a single module
verify_module() {
    local LEAN_FILE="$1"
    local MODULE_NAME
    MODULE_NAME=$(basename "$LEAN_FILE" .sv)
    MODULE_NAME=$(basename "$MODULE_NAME" .v)

    local CHISEL_FILE="$CHISEL_DIR/${MODULE_NAME}.sv"

    # Check if corresponding Chisel file exists
    if [ ! -f "$CHISEL_FILE" ]; then
        echo -e "${RED}✗ No Chisel output found for $MODULE_NAME${NC}"
        echo "  Expected: $CHISEL_FILE"
        return 1
    fi

    echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
    echo "  Verifying: $MODULE_NAME"
    echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
    echo "  LEAN:   $LEAN_FILE"
    echo "  Chisel: $CHISEL_FILE"
    echo ""

    # Strip CIRCT verification layers from Chisel output and remove 'automatic' keyword
    # (Yosys has limited support for automatic variables in always blocks)
    sed '/^\/\/ ----- 8< -----/,$d' "$CHISEL_FILE" | \
        sed 's/\bautomatic\s\+/ /g' > "$TMPDIR/chisel_clean_${MODULE_NAME}.sv"

    # Check if this is a sequential circuit (contains always @)
    local IS_SEQUENTIAL=0
    if grep -q "always @" "$LEAN_FILE"; then
        IS_SEQUENTIAL=1
        echo "  Type: Sequential circuit (using SEC)"
    else
        echo "  Type: Combinational circuit (using CEC)"
    fi
    echo ""

    # Create Yosys script for equivalence checking
    if [ $IS_SEQUENTIAL -eq 1 ]; then
        # Sequential Equivalence Checking (SEC)
        cat > "$TMPDIR/lec_${MODULE_NAME}.ys" <<'YOSYS_EOF'
# Read and prepare LEAN design (gold reference)
read_verilog -sv LEAN_FILE
hierarchy -check -top MODULE_NAME
proc; memory; opt
rename MODULE_NAME gold

# Stash gold design
design -stash gold

# Read and prepare Chisel design (gate implementation)
read_verilog -sv CHISEL_FILE
hierarchy -check -top MODULE_NAME
proc; memory; opt
rename MODULE_NAME gate

# Stash gate design
design -stash gate

# Copy both into main design for comparison
design -copy-from gold -as gold gold
design -copy-from gate -as gate gate

# Build equivalence circuit (don't flatten - preserve state elements)
equiv_make gold gate equiv
prep -top equiv

# Show statistics
stat

# Perform sequential equivalence check with induction
equiv_simple -undef
equiv_induct -undef
equiv_status -assert
YOSYS_EOF
    else
        # Combinational Equivalence Checking (CEC)
        cat > "$TMPDIR/lec_${MODULE_NAME}.ys" <<'YOSYS_EOF'
# Read and prepare LEAN design (gold reference)
read_verilog -sv LEAN_FILE
hierarchy -check -top MODULE_NAME
proc; opt; memory; opt; flatten
rename MODULE_NAME gold

# Stash gold design
design -stash gold

# Read and prepare Chisel design (gate implementation)
read_verilog -sv CHISEL_FILE
hierarchy -check -top MODULE_NAME
proc; opt; memory; opt; flatten
rename MODULE_NAME gate

# Stash gate design
design -stash gate

# Copy both into main design for comparison
design -copy-from gold -as gold gold
design -copy-from gate -as gate gate

# Build miter circuit for equivalence check
miter -equiv -flatten -make_outputs gold gate miter
hierarchy -top miter

# Show statistics
stat

# Run SAT solver to prove equivalence
sat -verify -prove-asserts -show-ports miter
YOSYS_EOF
    fi

    # Substitute file paths and module name
    sed -i "s|LEAN_FILE|$LEAN_FILE|g" "$TMPDIR/lec_${MODULE_NAME}.ys"
    sed -i "s|CHISEL_FILE|$TMPDIR/chisel_clean_${MODULE_NAME}.sv|g" "$TMPDIR/lec_${MODULE_NAME}.ys"
    sed -i "s|MODULE_NAME|$MODULE_NAME|g" "$TMPDIR/lec_${MODULE_NAME}.ys"

    # Run Yosys and capture output
    local YOSYS_OUTPUT="$TMPDIR/yosys_output_${MODULE_NAME}.txt"
    local YOSYS_SUCCESS=0
    if yosys -s "$TMPDIR/lec_${MODULE_NAME}.ys" > "$YOSYS_OUTPUT" 2>&1; then
        YOSYS_SUCCESS=1
    fi

    # Analyze results (quiet mode - don't show full yosys output unless failure)

    # Check for successful verification (different for CEC vs SEC)
    local VERIFICATION_SUCCESS=0
    if [ $IS_SEQUENTIAL -eq 1 ]; then
        # SEC: Check for equiv_status success
        if [ $YOSYS_SUCCESS -eq 1 ] && grep -q "Equivalence successfully proven" "$YOSYS_OUTPUT"; then
            VERIFICATION_SUCCESS=1
        fi
    else
        # CEC: Check for SAT success
        if [ $YOSYS_SUCCESS -eq 1 ] && (grep -q "SAT proof finished - no model found: SUCCESS" "$YOSYS_OUTPUT" || grep -q "Solving finished" "$YOSYS_OUTPUT"); then
            VERIFICATION_SUCCESS=1
        fi
    fi

    if [ $VERIFICATION_SUCCESS -eq 1 ]; then
        # Check for any failed assertions
        if grep -q "FAILED" "$YOSYS_OUTPUT"; then
            echo -e "${RED}✗ NOT EQUIVALENT${NC}"
            echo ""
            echo "Failed assertions:"
            grep "FAILED" "$YOSYS_OUTPUT" | head -5
            echo ""
            return 1
        else
            echo -e "${GREEN}✓ EQUIVALENT${NC}"
            # Show key statistics
            grep -A 1 "Solving problem with" "$YOSYS_OUTPUT" | sed 's/^/  /' || true
            echo ""
            return 0
        fi
    else
        echo -e "${YELLOW}⚠ VERIFICATION INCOMPLETE${NC}"
        echo ""
        echo "Last 20 lines of Yosys output:"
        tail -20 "$YOSYS_OUTPUT"
        echo ""
        return 1
    fi
}

# Main loop: verify each module
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "  Running LEC on all modules"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

while IFS= read -r LEAN_FILE; do
    if ! verify_module "$LEAN_FILE"; then
        ALL_PASSED=0
    fi
done <<< "$LEAN_MODULES"

# Final summary
echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "  Summary"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

if [ $ALL_PASSED -eq 1 ]; then
    echo -e "${GREEN}✓ All modules verified successfully${NC}"
    echo ""
    exit 0
else
    echo -e "${RED}✗ Some modules failed verification${NC}"
    echo ""
    exit 1
fi
