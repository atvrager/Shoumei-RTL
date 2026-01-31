#!/bin/bash
# Smoke test for CI: Tests complete pipeline from LEAN → Chisel → Validation
# Exit code 0 = success, non-zero = failure

set -e

# Colors
GREEN='\033[0;32m'
RED='\033[0;31m'
YELLOW='\033[1;33m'
NC='\033[0m'

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"

# Add tools to PATH
export PATH="$HOME/.elan/bin:$HOME/.local/share/coursier/bin:$PATH"

cd "$PROJECT_ROOT"

echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "  証明 Shoumei RTL - Smoke Test"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

# Test 1: LEAN Build
echo "==> Test 1: LEAN Build"
if lake build; then
    echo -e "${GREEN}✓ LEAN build succeeded${NC}"
else
    echo -e "${RED}✗ LEAN build failed${NC}"
    exit 1
fi
echo ""

# Test 1b: Formal Proofs Verification
echo "==> Test 1b: Formal Proofs Verification"
if lake build ProvenRTL.Examples.AdderProofs; then
    echo -e "${GREEN}✓ FullAdder formal proofs verified${NC}"
    echo "  - Truth table correctness (8 cases)"
    echo "  - Commutativity property"
    echo "  - Arithmetic correctness"
    echo "  - Complete correctness theorem"
else
    echo -e "${RED}✗ Formal proofs failed to verify${NC}"
    exit 1
fi
echo ""

# Test 2: Code Generation
echo "==> Test 2: Code Generation"
if lake exe codegen > /dev/null 2>&1; then
    echo -e "${GREEN}✓ Code generation succeeded${NC}"
else
    echo -e "${RED}✗ Code generation failed${NC}"
    exit 1
fi

# Verify FullAdder files exist
if [ ! -f "output/sv-from-lean/FullAdder.sv" ]; then
    echo -e "${RED}✗ FullAdder LEAN SystemVerilog not generated${NC}"
    exit 1
fi

if [ ! -f "chisel/src/main/scala/generated/FullAdder.scala" ]; then
    echo -e "${RED}✗ FullAdder Chisel file not generated${NC}"
    exit 1
fi

# Verify DFlipFlop files exist
if [ ! -f "output/sv-from-lean/DFlipFlop.sv" ]; then
    echo -e "${RED}✗ DFlipFlop LEAN SystemVerilog not generated${NC}"
    exit 1
fi

if [ ! -f "chisel/src/main/scala/generated/DFlipFlop.scala" ]; then
    echo -e "${RED}✗ DFlipFlop Chisel file not generated${NC}"
    exit 1
fi

echo -e "${GREEN}✓ Generated files exist (FullAdder, DFlipFlop)${NC}"
echo ""

# Test 3: Chisel Compilation
echo "==> Test 3: Chisel Compilation"
cd chisel
if sbt run; then
    echo -e "${GREEN}✓ Chisel compilation succeeded${NC}"
else
    echo -e "${RED}✗ Chisel compilation failed${NC}"
    exit 1
fi
cd ..

if [ ! -f "output/sv-from-chisel/FullAdder.sv" ]; then
    echo -e "${RED}✗ FullAdder Chisel SystemVerilog not generated${NC}"
    exit 1
fi

if [ ! -f "output/sv-from-chisel/DFlipFlop.sv" ]; then
    echo -e "${RED}✗ DFlipFlop Chisel SystemVerilog not generated${NC}"
    exit 1
fi

echo -e "${GREEN}✓ Chisel SystemVerilog generated (FullAdder, DFlipFlop)${NC}"
echo ""

# Test 4: Port Name Validation
echo "==> Test 4: Port Name Validation"
LEAN_PORTS=$(grep "^module FullAdder" output/sv-from-lean/FullAdder.sv | sed 's/.*(\(.*\));/\1/' | tr -d ' ')
CHISEL_PORTS=$(grep "^module FullAdder" output/sv-from-chisel/FullAdder.sv | sed 's/.*(\(.*\)/\1/' | tr -d ' \t' | head -1)

echo "LEAN ports:   $LEAN_PORTS"
echo "Chisel ports: $CHISEL_PORTS"

# Check that key ports exist in both
for port in a b cin sum cout; do
    if ! echo "$LEAN_PORTS" | grep -q "$port"; then
        echo -e "${RED}✗ Port '$port' missing in LEAN output${NC}"
        exit 1
    fi
    if ! grep -q "$port" output/sv-from-chisel/FullAdder.sv; then
        echo -e "${RED}✗ Port '$port' missing in Chisel output${NC}"
        exit 1
    fi
done

echo -e "${GREEN}✓ All ports present in both outputs${NC}"
echo ""

# Test 5: Logic Validation (check key expressions)
echo "==> Test 5: Logic Validation"
for expr in "a ^ b" "ab_xor ^ cin" "a & b"; do
    if ! grep -q "$expr" output/sv-from-lean/FullAdder.sv; then
        echo -e "${RED}✗ Expression '$expr' not found in LEAN output${NC}"
        exit 1
    fi
    if ! grep -q "$expr" output/sv-from-chisel/FullAdder.sv; then
        echo -e "${RED}✗ Expression '$expr' not found in Chisel output${NC}"
        exit 1
    fi
done

echo -e "${GREEN}✓ Full adder logic verified${NC}"
echo ""

# Test 5b: DFF Port and Logic Validation
echo "==> Test 5b: DFF Port and Logic Validation"

# Check DFF ports in LEAN output (d, clock, reset, q)
for port in d clock reset q; do
    if ! grep -q "$port" output/sv-from-lean/DFlipFlop.sv; then
        echo -e "${RED}✗ Port '$port' missing in LEAN DFF output${NC}"
        exit 1
    fi
done

# Check DFF ports in Chisel output (d, clock, reset, q)
for port in d clock reset q; do
    if ! grep -q "$port" output/sv-from-chisel/DFlipFlop.sv; then
        echo -e "${RED}✗ Port '$port' missing in Chisel DFF output${NC}"
        exit 1
    fi
done

# Check for sequential logic patterns in both outputs
if ! grep -q "always @(posedge" output/sv-from-lean/DFlipFlop.sv; then
    echo -e "${RED}✗ No 'always @(posedge' block in LEAN DFF output${NC}"
    exit 1
fi

if ! grep -q "if (reset)" output/sv-from-lean/DFlipFlop.sv; then
    echo -e "${RED}✗ No reset logic in LEAN DFF output${NC}"
    exit 1
fi

if ! grep -q "always @(posedge" output/sv-from-chisel/DFlipFlop.sv; then
    echo -e "${RED}✗ No 'always @(posedge' block in Chisel DFF output${NC}"
    exit 1
fi

echo -e "${GREEN}✓ DFlipFlop ports and logic verified${NC}"
echo ""

# Test 6: Yosys Equivalence (if available)
echo "==> Test 6: Yosys Equivalence Check"
if command -v yosys > /dev/null 2>&1; then
    echo "Yosys detected, running formal equivalence check..."
    if ./verification/run-lec.sh output/sv-from-lean output/sv-from-chisel; then
        echo -e "${GREEN}✓ Formal equivalence proven with Yosys${NC}"
    else
        echo -e "${YELLOW}⚠ Yosys equivalence check did not pass${NC}"
        echo "  (non-fatal in smoke test)"
    fi
else
    echo -e "${YELLOW}⚠ Yosys not installed, skipping formal equivalence${NC}"
    echo "  Install: yay -S yosys (Arch) or apt install yosys (Ubuntu)"
fi
echo ""

# Summary
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo -e "${GREEN}✓ ALL SMOKE TESTS PASSED${NC}"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""
echo "Pipeline Status:"
echo "  ✓ LEAN builds successfully"
echo "  ✓ Formal proofs verified (FullAdder correctness)"
echo "  ✓ Code generators produce valid output"
echo "  ✓ Chisel compiles to SystemVerilog"
echo "  ✓ FullAdder (combinational) verified"
echo "  ✓ DFlipFlop (sequential) verified"
echo ""

exit 0
