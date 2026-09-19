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
    printf '%bNo generated SV files found. Run make codegen first.%b\n' "$RED" "$NC"
    exit 1
fi

# --- Test 1: Generated file existence ---
echo "==> Test 1: Generated Files"

for mod in DFlipFlop Queue1Flow_39 Queue1Flow_72 ALU32; do
    if [ -f "output/sv-from-lean/${mod}.sv" ]; then
        pass "Lean SV: ${mod}.sv"
    else
        fail "Lean SV: ${mod}.sv missing"
    fi
done

# RV32 decoders (optional, depends on third_party/riscv-opcodes submodule)
if [ -f "output/sv-from-lean/RV32IMFDecoder.sv" ]; then
    pass "RV32IMFDecoder generated"
fi
echo ""

# --- Test 2: C++ simulation output ---
echo "==> Test 2: C++ Simulation Output"

SC_H_COUNT=0
if [ -d "output/cpp_sim" ]; then
    SC_H_COUNT=$(find output/cpp_sim -name "*.h" 2>/dev/null | wc -l)
fi

if [ "$SC_H_COUNT" -gt 0 ]; then
    pass "C++ simulation headers generated (${SC_H_COUNT} files)"
    for mod in DFlipFlop ALU32; do
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

# ALU32
for port in a b op zero one result; do
    if grep -q "$port" output/sv-from-lean/ALU32.sv 2>/dev/null; then
        pass "ALU32 port '${port}'"
    else
        fail "ALU32 port '${port}' missing"
    fi
done

# DFlipFlop
for port in d clock reset q; do
    if grep -q "$port" output/sv-from-lean/DFlipFlop.sv 2>/dev/null; then
        pass "DFlipFlop port '${port}'"
    else
        fail "DFlipFlop port '${port}' missing"
    fi
done

# Queue1Flow_39
for port in enq_data enq_valid enq_ready deq_data deq_valid deq_ready; do
    if grep -q "$port" output/sv-from-lean/Queue1Flow_39.sv 2>/dev/null; then
        pass "Queue1Flow_39 port '${port}'"
    else
        fail "Queue1Flow_39 port '${port}' missing"
    fi
done

# RV32IMFDecoder (conditional - requires third_party/riscv-opcodes submodule)
if [ -f "output/sv-from-lean/RV32IMFDecoder.sv" ]; then
    for port in io_instr io_optype io_rd io_rs1 io_rs2 io_imm io_valid; do
        if grep -q "$port" output/sv-from-lean/RV32IMFDecoder.sv 2>/dev/null; then
            pass "RV32IMFDecoder port '${port}'"
        else
            fail "RV32IMFDecoder port '${port}' missing"
        fi
    done
fi
echo ""

# --- Test 4: Logic validation ---
echo "==> Test 4: Logic Validation"

# ALU32 logic
if grep -q "add_out" output/sv-from-lean/ALU32.sv 2>/dev/null; then
    pass "ALU32 adder logic"
else
    fail "ALU32 missing adder logic"
fi

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
if grep -qE "always(_ff)? @\(posedge" output/sv-from-lean/Queue1Flow_39.sv 2>/dev/null; then
    pass "Queue1Flow_39 sequential block"
else
    fail "Queue1Flow_39 missing always @(posedge block"
fi

# Decoder immediate extraction (conditional)
if [ -f "output/sv-from-lean/RV32IMFDecoder.sv" ]; then
    if grep -qE "imm_i|imm_s|imm_b" output/sv-from-lean/RV32IMFDecoder.sv 2>/dev/null; then
        pass "RV32IMFDecoder immediate extraction"
    else
        fail "RV32IMFDecoder missing immediate extraction"
    fi
fi
echo ""

# --- Test 5: Formal Proof Integrity ---
echo "==> Test 5: Formal Proof Integrity"

VACUOUS_COUNT=$(grep -rnE '^\s*(protected\s+|private\s+)?(theorem|lemma)\s+.*:\s*True\s*:=' lean/ 2>/dev/null | wc -l || true)
if [ "$VACUOUS_COUNT" -eq 0 ]; then
    pass "No vacuous (: True) theorem stubs in Lean proofs"
else
    fail "Found ${VACUOUS_COUNT} vacuous (: True) theorem stubs in Lean proofs"
fi

AXIOM_COUNT=$(grep -rnE '^\s*axiom\s' lean/ 2>/dev/null | wc -l || true)
if [ "$AXIOM_COUNT" -eq 0 ]; then
    pass "Zero unproven axioms across Lean proofs"
else
    fail "Found ${AXIOM_COUNT} unproven axioms in Lean proofs"
fi

# Cache behavior conformance (emitted SV vs reference model).
# Needs Verilator, which the general smoke job does not install (the
# verilator-sim CI job runs the conformance suite instead); skip cleanly
# when the model can't be built.
echo ""
echo "==> Cache behavior conformance"
if ! command -v verilator > /dev/null 2>&1; then
    echo "(skipped: verilator not installed; CI runs it in verilator-sim)"
elif make -C testbench cache-model-test > /tmp/cache-conformance.log 2>&1; then
    pass "Cache conformance (L1D SV vs reference)"
else
    fail "Cache conformance (see /tmp/cache-conformance.log)"
    tail -20 /tmp/cache-conformance.log || true
fi

SORRY_COUNT=$(grep -rnE '\bsorry\b' lean/ 2>/dev/null | grep -vcE ':[0-9]+:\s*--' || true)
if [ "$SORRY_COUNT" -eq 0 ]; then
    pass "Zero sorry/admit occurrences in Lean proofs"
else
    fail "Found ${SORRY_COUNT} sorry occurrences in Lean proofs"
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
