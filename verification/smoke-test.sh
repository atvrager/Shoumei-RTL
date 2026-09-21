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

for mod in DFlipFlop Queue1Flow_39 Queue1Flow_72 ALU32 Shoumei_SoC ResetSync TLXbar8 UART GPIO ACLINT APLIC BootROM SRAM; do
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

# Shoumei_SoC
for port in clock reset_n uart_rx uart_tx rob_empty mem_req_valid mem_resp_valid; do
    if grep -q "$port" output/sv-from-lean/Shoumei_SoC.sv 2>/dev/null; then
        pass "Shoumei_SoC port '${port}'"
    else
        fail "Shoumei_SoC port '${port}' missing"
    fi
done
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
# Shoumei_SoC integration logic
for inst in u_rst_sync u_cached_cpu u_tl_xbar u_uart u_gpio u_aclint u_aplic u_bootrom u_sram; do
    if grep -q "$inst" output/sv-from-lean/Shoumei_SoC.sv 2>/dev/null; then
        pass "Shoumei_SoC instance '${inst}'"
    else
        fail "Shoumei_SoC instance '${inst}' missing"
    fi
done

# Physical synthesis wrapper
if [ -f "physical/Shoumei_SoC_synth.sv" ]; then
    pass "ASIC synthesis wrapper: Shoumei_SoC_synth.sv"
else
    fail "ASIC synthesis wrapper: Shoumei_SoC_synth.sv missing"
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

# --- PDK technology mapping ---
echo ""
echo "==> PDK technology mapping"

for pdk_dir in output/sv-asap7 output/sv-gf180; do
    mapped_count=$(find "$pdk_dir" -maxdepth 1 -name '*.sv' 2>/dev/null | wc -l | tr -d ' ')
    if [ "$mapped_count" -gt 0 ]; then
        pass "Tech-mapped SV present: $pdk_dir ($mapped_count modules)"
    else
        fail "Tech-mapped SV missing: $pdk_dir"
    fi
done

# Prefix merge cell: AO21 on ASAP7, AOI21+INV on GF180.
if grep -q "AO21x1_ASAP7_75t_R" output/sv-asap7/KoggeStoneAdder64NoCin.sv 2>/dev/null; then
    pass "ASAP7 prefix merge maps to AO21x1_ASAP7_75t_R"
else
    fail "ASAP7 prefix merge did not use AO21"
fi

if grep -q "gf180mcu_fd_sc_mcu9t5v0__aoi21_1" output/sv-gf180/KoggeStoneAdder64NoCin.sv 2>/dev/null; then
    pass "GF180 prefix merge maps to aoi21_1 + inv"
else
    fail "GF180 prefix merge did not use aoi21"
fi

# ASAP7 has no mux cell: the mapper must fall back to `assign`.  GF180 has one.
if grep -qE "^  assign .* \? .* : .*;" output/sv-asap7/CarrySelectAdder32.sv 2>/dev/null \
   && ! grep -qE "MUX[0-9]?x[0-9]_ASAP7" output/sv-asap7/CarrySelectAdder32.sv 2>/dev/null; then
    pass "ASAP7 mux falls back to assign (no mux cell in library)"
else
    fail "ASAP7 mux emission unexpected"
fi

if grep -q "gf180mcu_fd_sc_mcu9t5v0__mux2_" output/sv-gf180/CarrySelectAdder32.sv 2>/dev/null; then
    pass "GF180 mux maps to a real mux2 cell"
else
    fail "GF180 mux did not map to a mux2 cell"
fi

if python3 scripts/check-cell-tables.py > /tmp/cell-tables.log 2>&1; then
    pass "Cell tables match PDK Liberty functions"
else
    fail "Cell table / Liberty mismatch (see /tmp/cell-tables.log)"
    tail -5 /tmp/cell-tables.log || true
fi

SORRY_COUNT=$(grep -rnE '\bsorry\b' lean/ 2>/dev/null | grep -vcE ':[0-9]+:\s*--' || true)
if [ "$SORRY_COUNT" -eq 0 ]; then
    pass "Zero sorry/admit occurrences in Lean proofs"
else
    fail "Found ${SORRY_COUNT} sorry occurrences in Lean proofs"
fi
echo ""

# --- SEC & SVA Formal Verification ---
echo "==> SEC & SVA Verification"

for sec_artifact in output/sv-sec/Register160_sec_miter.sv \
                    output/sv-sec/Register160_yosys.tcl \
                    output/sv-sec/Register160_sva_formal.tcl \
                    output/sv-sec/RegisterEn64_sva_formal.tcl; do
    if [ -f "$sec_artifact" ]; then
        pass "SEC/SVA artifact: $(basename "$sec_artifact")"
    else
        fail "SEC/SVA artifact missing: $sec_artifact"
    fi
done

if command -v yosys >/dev/null 2>&1; then
    if ./verification/sec-verify.sh --yosys > /tmp/sec-smoke.log 2>&1; then
        pass "Sequential Equivalence Checking (Yosys SAT miter)"
    else
        fail "Sequential Equivalence Checking failed (see /tmp/sec-smoke.log)"
        tail -20 /tmp/sec-smoke.log || true
    fi
else
    echo "(skipped: yosys not installed)"
fi

if command -v slang >/dev/null 2>&1 || python3 -c "import pyslang" >/dev/null 2>&1; then
    if python3 verification/slang-lint.py output/sv-sec > /tmp/sva-slang.log 2>&1; then
        pass "SVA miter elaboration (slang)"
    else
        fail "SVA miter elaboration failed (see /tmp/sva-slang.log)"
        tail -20 /tmp/sva-slang.log || true
    fi
else
    echo "(skipped: slang/pyslang not installed)"
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
