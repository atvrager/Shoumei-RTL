#!/bin/bash
# Yosys-based equivalence checking
# Uses Yosys directly (simpler than eqy for combinational circuits)

set -e

LEAN_FILE="$1"
CHISEL_FILE="$2"

if [ -z "$LEAN_FILE" ] || [ -z "$CHISEL_FILE" ]; then
    echo "Usage: $0 <lean-verilog> <chisel-verilog>"
    exit 1
fi

echo "Yosys Equivalence Checking"
echo "=========================="
echo ""
echo "LEAN:   $LEAN_FILE"
echo "Chisel: $CHISEL_FILE"
echo ""

# Create temporary directory
TMPDIR=$(mktemp -d)
trap "rm -rf $TMPDIR" EXIT

# Strip verification layers from Chisel output (after "// ----- 8< -----")
sed '/^\/\/ ----- 8< -----/,$d' "$CHISEL_FILE" > "$TMPDIR/chisel_clean.sv"

# Yosys script for equivalence checking using equiv_make
cat > "$TMPDIR/equiv.ys" <<'YOSYS_SCRIPT'
# Read gold design (LEAN)
read_verilog LEAN_FILE
prep -top FullAdder

# Store gold
design -stash gold

# Read gate design (Chisel)
read_verilog -sv CHISEL_CLEAN_FILE
prep -top FullAdder

# Store gate
design -stash gate

# Set up equivalence checking
design -copy-from gate -as gate FullAdder
design -copy-from gold -as gold FullAdder

# Use equiv_make for combinational equivalence
equiv_make gold gate equiv

# Prepare and check
hierarchy -check -top equiv
proc; opt
flatten
opt

# Use SAT to prove equivalence
sat -set-def-inputs -seq 1 -tempinduct -prove-asserts -show-ports equiv

YOSYS_SCRIPT

# Substitute file paths (do CHISEL_CLEAN_FILE first to avoid partial replacement)
sed -i "s|CHISEL_CLEAN_FILE|$TMPDIR/chisel_clean.sv|g" "$TMPDIR/equiv.ys"
sed -i "s|LEAN_FILE|$LEAN_FILE|g" "$TMPDIR/equiv.ys"

echo "Running Yosys equivalence check..."
echo ""

if yosys -q -s "$TMPDIR/equiv.ys" 2>&1 | tee "$TMPDIR/output.txt"; then
    if grep -q "SUCCESS" "$TMPDIR/output.txt" || grep -q "Solving finished" "$TMPDIR/output.txt"; then
        echo ""
        echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
        echo "✓ EQUIVALENT"
        echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
        echo ""
        echo "Yosys proved that LEAN and Chisel generate equivalent circuits!"
        exit 0
    fi
fi

echo "⚠ Equivalence check did not complete successfully"
cat "$TMPDIR/output.txt"
exit 1
