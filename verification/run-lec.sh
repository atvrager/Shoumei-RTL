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

LEAN_FILES=$(find "$LEAN_DIR" -name "*.sv" -o -name "*.v" 2>/dev/null)
CHISEL_FILES=$(find "$CHISEL_DIR" -name "*.sv" -o -name "*.v" 2>/dev/null)

if [ -z "$LEAN_FILES" ] || [ -z "$CHISEL_FILES" ]; then
    echo -e "${RED}✗ Missing input files${NC}"
    exit 1
fi

LEAN_FILE=$(echo "$LEAN_FILES" | head -1)
CHISEL_FILE=$(echo "$CHISEL_FILES" | head -1)

# Extract module name from filename (e.g., FullAdder.sv -> FullAdder)
MODULE_NAME=$(basename "$LEAN_FILE" .sv)
MODULE_NAME=$(basename "$MODULE_NAME" .v)

echo "Comparing:"
echo "  LEAN:   $LEAN_FILE"
echo "  Chisel: $CHISEL_FILE"
echo "  Module: $MODULE_NAME"
echo ""

# Create temporary working directory
TMPDIR=$(mktemp -d)
trap 'rm -rf "$TMPDIR"' EXIT

# Strip CIRCT verification layers from Chisel output
sed '/^\/\/ ----- 8< -----/,$d' "$CHISEL_FILE" > "$TMPDIR/chisel_clean.sv"

echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "  Phase 1: Parse and Synthesize Designs"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

# Create Yosys script for equivalence checking
cat > "$TMPDIR/lec.ys" <<'YOSYS_EOF'
# Read and prepare LEAN design (gold reference)
read_verilog LEAN_FILE
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

# Substitute file paths and module name
sed -i "s|LEAN_FILE|$LEAN_FILE|g" "$TMPDIR/lec.ys"
sed -i "s|CHISEL_FILE|$TMPDIR/chisel_clean.sv|g" "$TMPDIR/lec.ys"
sed -i "s|MODULE_NAME|$MODULE_NAME|g" "$TMPDIR/lec.ys"

# Run Yosys and capture output
YOSYS_OUTPUT="$TMPDIR/yosys_output.txt"
if yosys -s "$TMPDIR/lec.ys" > "$YOSYS_OUTPUT" 2>&1; then
    YOSYS_SUCCESS=1
else
    YOSYS_SUCCESS=0
fi

# Display output
cat "$YOSYS_OUTPUT"
echo ""

# Analyze results
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "  Phase 2: Analyze Results"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

if [ $YOSYS_SUCCESS -eq 1 ] && (grep -q "SAT proof finished - no model found: SUCCESS" "$YOSYS_OUTPUT" || grep -q "Solving finished" "$YOSYS_OUTPUT"); then
    # Check for any failed assertions
    if grep -q "FAILED" "$YOSYS_OUTPUT"; then
        echo -e "${RED}✗ NOT EQUIVALENT${NC}"
        echo ""
        echo "The SAT solver found a counterexample where the circuits differ."
        echo ""
        echo "Failed assertions:"
        grep "FAILED" "$YOSYS_OUTPUT" | head -10
        exit 1
    else
        echo -e "${GREEN}✓ EQUIVALENT${NC}"
        echo ""
        echo "Formal proof completed: LEAN and Chisel generators produce"
        echo "logically equivalent circuits for $MODULE_NAME."
        echo ""
        # Show key statistics and SAT results
        echo "SAT Solver Results:"
        grep -A 1 "Solving problem with" "$YOSYS_OUTPUT" | sed 's/^/  /' || true
        echo ""
        echo "Circuit Statistics:"
        grep "Number of cells:" "$YOSYS_OUTPUT" | head -2 | sed 's/^/  /' || true
        exit 0
    fi
else
    echo -e "${YELLOW}⚠ VERIFICATION INCOMPLETE${NC}"
    echo ""
    echo "Could not complete formal verification."
    echo ""
    echo "Common issues:"
    echo "  - Port name mismatches (check with: grep 'module.*(' files)"
    echo "  - Different module hierarchies"
    echo "  - Yosys parsing errors"
    echo ""
    echo "Last 20 lines of output:"
    tail -20 "$YOSYS_OUTPUT"
    exit 1
fi
