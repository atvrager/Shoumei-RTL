#!/bin/bash
# Smoke test: Validates pipeline outputs are structurally correct
# Assumes builds have already run (via 'make smoke-test' or CI steps)
# Exit code 0 = all passed, non-zero = failure count

set -e

GREEN='\033[0;32m'
RED='\033[0;31m'
YELLOW='\033[1;33m'
NC='\033[0m'

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"

cd "$PROJECT_ROOT"

PASS=0
FAIL=0

pass() { printf '%b  ✓ %s%b\n' "$GREEN" "$1" "$NC"; PASS=$((PASS + 1)); }
fail() { printf '%b  ✗ %s%b\n' "$RED" "$1" "$NC"; FAIL=$((FAIL + 1)); }

echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "  Shoumei RTL - Smoke Test"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

# Pre-flight: verify codegen has been run
if ! ls output/sv-from-lean/*.sv >/dev/null 2>&1; then
    printf '%bNo generated SV files found. Run make codegen chisel first.%b\n' "$RED" "$NC"
    exit 1
fi

# --- Test 1: Generated file existence ---
echo "==> Test 1: Generated Files"

for mod in FullAdder DFlipFlop Queue1_8 Queue1_32; do
    if [ -f "output/sv-from-lean/${mod}.sv" ]; then
        pass "Lean SV: ${mod}.sv"
    else
        fail "Lean SV: ${mod}.sv missing"
    fi
    if [ -f "chisel/src/main/scala/generated/${mod}.scala" ]; then
        pass "Chisel src: ${mod}.scala"
    else
        fail "Chisel src: ${mod}.scala missing"
    fi
    if [ -f "output/sv-from-chisel/${mod}.sv" ]; then
        pass "Chisel SV: ${mod}.sv"
    else
        fail "Chisel SV: ${mod}.sv missing"
    fi
done

# RV32I/RV32IM decoders (optional, depends on third_party/riscv-opcodes submodule)
for mod in RV32IDecoder RV32IMDecoder; do
    if [ -f "output/sv-from-lean/${mod}.sv" ]; then
        pass "${mod} generated"
        if [ -f "chisel/src/main/scala/generated/${mod}.scala" ]; then
            pass "Chisel src: ${mod}.scala"
        fi
        if [ -f "output/sv-from-chisel/${mod}.sv" ]; then
            pass "Chisel SV: ${mod}.sv"
        fi
    fi
done
echo ""

# --- Test 2: C++ simulation output ---
echo "==> Test 2: C++ Simulation Output"

SC_H_COUNT=0
if [ -d "output/cpp_sim" ]; then
    SC_H_COUNT=$(find output/cpp_sim -name "*.h" 2>/dev/null | wc -l)
fi

if [ "$SC_H_COUNT" -gt 0 ]; then
    pass "C++ simulation headers generated (${SC_H_COUNT} files)"
    for mod in FullAdder DFlipFlop; do
        if [ -f "output/cpp_sim/${mod}.h" ] && [ -f "output/cpp_sim/${mod}.cpp" ]; then
            pass "C++ sim: ${mod}.h + ${mod}.cpp"
        else
            fail "C++ sim: ${mod} files missing"
        fi
    done
else
    printf '%b  ⚠ No C++ simulation output (run make codegen to generate)%b\n' "$YELLOW" "$NC"
fi
echo ""

# --- Test 3: Port validation ---
echo "==> Test 3: Port Validation"

# FullAdder
for port in a b cin sum cout; do
    if grep -q "$port" output/sv-from-lean/FullAdder.sv 2>/dev/null && \
       grep -q "$port" output/sv-from-chisel/FullAdder.sv 2>/dev/null; then
        pass "FullAdder port '${port}'"
    else
        fail "FullAdder port '${port}' mismatch"
    fi
done

# DFlipFlop
for port in d clock reset q; do
    if grep -q "$port" output/sv-from-lean/DFlipFlop.sv 2>/dev/null && \
       grep -q "$port" output/sv-from-chisel/DFlipFlop.sv 2>/dev/null; then
        pass "DFlipFlop port '${port}'"
    else
        fail "DFlipFlop port '${port}' mismatch"
    fi
done

# Queue (enq_data is bus-grouped: input logic [7:0] enq_data)
for port in enq_data enq_valid enq_ready; do
    if grep -q "$port" output/sv-from-lean/Queue1_8.sv 2>/dev/null; then
        pass "Queue1_8 port '${port}'"
    else
        fail "Queue1_8 port '${port}' missing"
    fi
done

# RV32IDecoder (conditional - requires third_party/riscv-opcodes submodule)
if [ -f "output/sv-from-lean/RV32IDecoder.sv" ]; then
    for port in io_instr io_optype io_rd io_rs1 io_rs2 io_imm io_valid; do
        if grep -q "$port" output/sv-from-lean/RV32IDecoder.sv 2>/dev/null && \
           grep -q "$port" output/sv-from-chisel/RV32IDecoder.sv 2>/dev/null; then
            pass "RV32IDecoder port '${port}'"
        else
            fail "RV32IDecoder port '${port}' mismatch"
        fi
    done
fi
echo ""

# --- Test 4: Logic validation ---
echo "==> Test 4: Logic Validation"

# FullAdder gate expressions
for expr in "a ^ b" "ab_xor ^ cin" "a & b"; do
    if grep -q "$expr" output/sv-from-lean/FullAdder.sv 2>/dev/null; then
        pass "FullAdder expr '${expr}'"
    else
        fail "FullAdder expr '${expr}' missing"
    fi
done

# DFF sequential logic (always_ff is IEEE 1800-2005+ syntax)
if grep -qE "always(_ff)? @\(posedge" output/sv-from-lean/DFlipFlop.sv 2>/dev/null; then
    pass "DFlipFlop sequential block"
else
    fail "DFlipFlop missing always @(posedge block"
fi

if grep -q "if (reset)" output/sv-from-lean/DFlipFlop.sv 2>/dev/null; then
    pass "DFlipFlop reset logic"
else
    fail "DFlipFlop missing reset logic"
fi

# Queue sequential logic
if grep -qE "always(_ff)? @\(posedge" output/sv-from-lean/Queue1_8.sv 2>/dev/null; then
    pass "Queue1_8 sequential block"
else
    fail "Queue1_8 missing always @(posedge block"
fi

# Decoder immediate extraction (conditional)
if [ -f "output/sv-from-lean/RV32IDecoder.sv" ]; then
    if grep -qE "imm_i|imm_s|imm_b" output/sv-from-lean/RV32IDecoder.sv 2>/dev/null; then
        pass "RV32IDecoder immediate extraction"
    else
        fail "RV32IDecoder missing immediate extraction"
    fi
fi
echo ""

# --- Summary ---
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
TOTAL=$((PASS + FAIL))
if [ "$FAIL" -eq 0 ]; then
    printf '%b✓ ALL SMOKE TESTS PASSED (%d checks)%b\n' "$GREEN" "$TOTAL" "$NC"
else
    printf '%b✗ %d FAILURES (%d/%d passed)%b\n' "$RED" "$FAIL" "$PASS" "$TOTAL" "$NC"
fi
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

exit "$FAIL"
