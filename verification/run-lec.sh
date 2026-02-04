#!/bin/bash
# Logical Equivalence Checking with Yosys
# Provides detailed diagnostics on success or failure
#
# Usage:
#   ./run-lec.sh                    # Verify all modules
#   ./run-lec.sh -m ROB16           # Verify ROB16 + its dependencies only
#   ./run-lec.sh -m ROB16 -m RAT_32x6  # Verify multiple targets + deps
#   ./run-lec.sh --use-slang        # Force use of yosys-slang (errors if not available)
#   ./run-lec.sh --no-slang         # Force use of $READ_CMD

set -e

LEAN_DIR="output/sv-from-lean"
CHISEL_DIR="output/sv-from-chisel"
declare -a TARGET_MODULES=()
USE_SLANG="auto"  # auto, yes, no

while [[ $# -gt 0 ]]; do
    case $1 in
        -m|--module)
            TARGET_MODULES+=("$2")
            shift 2
            ;;
        --use-slang)
            USE_SLANG="yes"
            shift
            ;;
        --no-slang)
            USE_SLANG="no"
            shift
            ;;
        *)
            # Legacy positional args: first is LEAN_DIR, second is CHISEL_DIR
            if [ -z "${_POS_1+x}" ]; then
                LEAN_DIR="$1"; _POS_1=1
            else
                CHISEL_DIR="$1"
            fi
            shift
            ;;
    esac
done

# Colors
GREEN='\033[0;32m'
RED='\033[0;31m'
YELLOW='\033[1;33m'
NC='\033[0m'

# Detect slang availability
SLANG_AVAILABLE=0
if yosys -m slang -p "help read_slang" >/dev/null 2>&1; then
    SLANG_AVAILABLE=1
fi

# Determine read command based on slang availability and user preference
READ_CMD="read_verilog -sv"
if [ "$USE_SLANG" = "yes" ]; then
    if [ $SLANG_AVAILABLE -eq 1 ]; then
        READ_CMD="read_slang"
    else
        echo -e "${RED}ERROR: --use-slang specified but yosys-slang is not available${NC}"
        echo "Install yosys-slang plugin or remove --use-slang flag"
        exit 1
    fi
elif [ "$USE_SLANG" = "auto" ] && [ $SLANG_AVAILABLE -eq 1 ]; then
    READ_CMD="read_slang"
fi

echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "  証明 Shoumei RTL - LEC with Yosys"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

# Show which read command is being used
if [ "$READ_CMD" = "read_slang" ]; then
    echo -e "${GREEN}Using yosys-slang for SystemVerilog parsing${NC}"
else
    echo "Using $READ_CMD for SystemVerilog parsing"
    if [ $SLANG_AVAILABLE -eq 1 ]; then
        echo "(yosys-slang available but not selected, use --use-slang to enable)"
    fi
fi
echo ""

# Find all LEAN-generated modules
# Find all modules first
ALL_LEAN_MODULES=$(find "$LEAN_DIR" -maxdepth 1 \( -name "*.sv" -o -name "*.v" \) 2>/dev/null)

if [ -z "$ALL_LEAN_MODULES" ]; then
    echo -e "${RED}✗ No LEAN-generated modules found in $LEAN_DIR${NC}"
    exit 1
fi

# Track overall success
ALL_PASSED=1

# Track verified modules for hierarchical checking
VERIFIED_MODULES_FILE=$(mktemp)
COMPOSITIONAL_MODULES_FILE=$(mktemp)

# Load compositional verification certificates from Lean
declare -A COMPOSITIONAL_CERTS
echo "Loading compositional verification certificates from Lean..."
while IFS='|' read -r module deps proof; do
    # Skip empty lines
    [[ -z "$module" ]] && continue
    # Trim whitespace
    module=$(echo "$module" | xargs)
    deps=$(echo "$deps" | xargs)
    proof=$(echo "$proof" | xargs)
    # Store module in associative array
    COMPOSITIONAL_CERTS["$module"]="$deps|$proof"
done < <(lake exe export_verification_certs 2>/dev/null || true)
echo "Loaded ${#COMPOSITIONAL_CERTS[@]} compositional certificate(s)"
echo ""

# Topological sort modules based on dependencies
echo "Sorting modules in topological order..."
TOPO_SORTED_MODULES=$(
    # Build dependency graph
    for file in $ALL_LEAN_MODULES; do
        module=$(basename "$file" .sv)
        module=$(basename "$module" .v)
        # Get dependencies from compositional cert if it exists
        if [ -n "${COMPOSITIONAL_CERTS[$module]}" ]; then
            IFS='|' read -r deps proof <<< "${COMPOSITIONAL_CERTS[$module]}"
            # Print: module depends_on dep1 dep2 ...
            echo "$module $deps" | tr ',' ' '
        else
            # No dependencies
            echo "$module"
        fi
    done | \
    # Simple topological sort using tsort
    awk '{
        module = $1
        modules[module] = 1
        for (i = 2; i <= NF; i++) {
            if ($i != "") {
                print $i " " module
                modules[$i] = 1
            }
        }
    }
    END {
        for (m in modules) print m " " m
    }' | tsort 2>/dev/null
)

# Map sorted module names back to file paths
LEAN_MODULES=""
for module in $TOPO_SORTED_MODULES; do
    for file in $ALL_LEAN_MODULES; do
        if [[ $(basename "$file" .sv) == "$module" ]] || [[ $(basename "$file" .v) == "$module" ]]; then
            LEAN_MODULES="$LEAN_MODULES"$'\n'"$file"
            break
        fi
    done
done
LEAN_MODULES=$(echo "$LEAN_MODULES" | sed '/^$/d')  # Remove empty lines

# If -m flag given, filter to only target modules + transitive dependencies
if [ ${#TARGET_MODULES[@]} -gt 0 ]; then
    echo "Target module(s): ${TARGET_MODULES[*]}"
    echo "Resolving transitive dependencies..."

    # Collect all required modules (targets + transitive deps)
    declare -A REQUIRED_MODULES
    declare -a QUEUE=("${TARGET_MODULES[@]}")
    while [ ${#QUEUE[@]} -gt 0 ]; do
        current="${QUEUE[0]}"
        QUEUE=("${QUEUE[@]:1}")
        [ -n "${REQUIRED_MODULES[$current]+x}" ] && continue
        REQUIRED_MODULES["$current"]=1
        # Add its dependencies to the queue
        if [ -n "${COMPOSITIONAL_CERTS[$current]}" ]; then
            IFS='|' read -r deps _proof <<< "${COMPOSITIONAL_CERTS[$current]}"
            IFS=',' read -ra DEP_ARRAY <<< "$deps"
            for dep in "${DEP_ARRAY[@]}"; do
                dep=$(echo "$dep" | xargs)
                [ -n "$dep" ] && QUEUE+=("$dep")
            done
        fi
    done

    # Filter LEAN_MODULES to only required modules (preserving topo order)
    FILTERED=""
    while IFS= read -r file; do
        mod=$(basename "$file" .sv)
        mod=$(basename "$mod" .v)
        if [ -n "${REQUIRED_MODULES[$mod]+x}" ]; then
            FILTERED="$FILTERED"$'\n'"$file"
        fi
    done <<< "$LEAN_MODULES"
    LEAN_MODULES=$(echo "$FILTERED" | sed '/^$/d')
    echo "  ${#REQUIRED_MODULES[@]} module(s) to verify (including dependencies)"
    echo ""
fi

MODULE_COUNT=$(echo "$LEAN_MODULES" | wc -l)
echo "Sorted $MODULE_COUNT modules in dependency order"
echo "Verification order:"
echo "$LEAN_MODULES" | head -10 | while read -r file; do
    echo "  - $(basename "$file" .sv)"
done
if [ "$MODULE_COUNT" -gt 10 ]; then
    echo "  ... and $((MODULE_COUNT - 10)) more"
fi
echo ""

# Create temporary working directory
TMPDIR=$(mktemp -d)
trap 'rm -rf "$TMPDIR" "$VERIFIED_MODULES_FILE" "$COMPOSITIONAL_MODULES_FILE"' EXIT

# Clean all Chisel files upfront for hierarchical support
CLEAN_CHISEL_DIR="$TMPDIR/chisel_clean"
mkdir -p "$CLEAN_CHISEL_DIR"
echo "Cleaning Chisel output files for Yosys compatibility..."
for f in "$CHISEL_DIR"/*.sv; do
    bn=$(basename "$f")
    # 1. Remove CIRCT verification blocks
    # 2. Convert 'automatic logic x = y;' to 'logic x; x = y;'
    # 3. Remove remaining 'automatic' keywords
    sed '/^\/\/ ----- 8< -----/,$d' "$f" | \
        sed -E 's/([[:space:]])automatic logic\s+([a-zA-Z0-9_]+)\s*=\s*(.+);/\1logic \2;\n\1\2 = \3;/g' | \
        sed 's/[[:space:]]*automatic[[:space:]]\+/ /g' > "$CLEAN_CHISEL_DIR/$bn"
done
echo "Cleaning complete."
echo ""

# Function to check if a module has submodule instances
has_submodules() {
    local file="$1"
    grep -qE "^\s*[A-Za-z0-9_]+\s+[a-z_][a-zA-Z0-9_]*\s*\(" "$file"
}

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

    # Check if this module is compositionally verified FIRST (skip LEC if so)
    if [ -n "${COMPOSITIONAL_CERTS[$MODULE_NAME]}" ]; then
        echo "  Method: Compositional (Lean proof)"
        echo ""
        IFS='|' read -r deps proof <<< "${COMPOSITIONAL_CERTS[$MODULE_NAME]}"

        # Check that all dependencies are verified
        local ALL_DEPS_VERIFIED=1
        local MISSING_DEPS=""
        IFS=',' read -ra DEP_ARRAY <<< "$deps"
        for dep in "${DEP_ARRAY[@]}"; do
            dep=$(echo "$dep" | xargs)  # trim whitespace
            if ! grep -q "^${dep}$" "$VERIFIED_MODULES_FILE" 2>/dev/null; then
                ALL_DEPS_VERIFIED=0
                MISSING_DEPS="$MISSING_DEPS $dep"
            fi
        done

        if [ $ALL_DEPS_VERIFIED -eq 1 ]; then
            echo -e "${GREEN}✓ COMPOSITIONALLY VERIFIED${NC}"
            echo ""
            echo "  Dependencies: $deps"
            echo "  All dependencies verified: ✓"
            echo "  Lean proof: $proof"
            echo "  Note: Skipping full LEC (verified by compositional reasoning)"
            echo ""
            # Record as compositionally verified
            echo "$MODULE_NAME" >> "$COMPOSITIONAL_MODULES_FILE"
            echo "$MODULE_NAME" >> "$VERIFIED_MODULES_FILE"
            return 0
        else
            echo -e "${YELLOW}⚠ COMPOSITIONAL VERIFICATION INCOMPLETE${NC}"
            echo "  Missing dependencies:$MISSING_DEPS"
            echo "  Attempting full LEC instead..."
            echo ""
        fi
    fi

    # Check if this is a sequential circuit
    # Detection: always block OR clock/reset inputs
    local IS_SEQUENTIAL=0
    if grep -qE "always @|input .*clock|input .*reset" "$LEAN_FILE"; then
        IS_SEQUENTIAL=1
    fi

    # Check if this module has hierarchical submodules
    local HAS_HIERARCHY=0
    if has_submodules "$LEAN_FILE"; then
        HAS_HIERARCHY=1
    fi

    if [ $IS_SEQUENTIAL -eq 1 ]; then
        if [ $HAS_HIERARCHY -eq 1 ]; then
            echo "  Type: Sequential circuit with hierarchy (using hierarchical SEC)"
        else
            echo "  Type: Sequential circuit (using flat SEC)"
        fi
    else
        echo "  Type: Combinational circuit (using CEC)"
    fi
    echo ""

    # Create Yosys script for equivalence checking
    if [ $IS_SEQUENTIAL -eq 1 ]; then
        if [ $HAS_HIERARCHY -eq 1 ]; then
            # Hierarchical Sequential Equivalence Checking
            # Strategy: Flatten and use standard induction depth
            local INDUCT_DEPTH=3

            cat > "$TMPDIR/lec_${MODULE_NAME}.ys" <<YOSYS_EOF
# Read and prepare LEAN design (gold reference)
$READ_CMD $LEAN_DIR/*.sv
hierarchy -check -top $MODULE_NAME
proc; memory; opt; flatten
rename $MODULE_NAME gold

# Stash gold design
design -stash gold

# Reset Verilog frontend
design -reset-vlog

# Read and prepare Chisel design (gate implementation)
$READ_CMD $CLEAN_CHISEL_DIR/*.sv
hierarchy -check -top $MODULE_NAME
proc; memory; opt; flatten
rename $MODULE_NAME gate

# Stash gate design
design -stash gate

# Copy both into main design for comparison
design -copy-from gold -as gold gold
design -copy-from gate -as gate gate

# Build equivalence circuit
equiv_make gold gate equiv
prep -top equiv
async2sync

# Show statistics
stat

# For hierarchical designs, use limited induction depth
equiv_simple -undef
equiv_induct -undef -seq $INDUCT_DEPTH
equiv_status -assert
YOSYS_EOF
        else
            # Flat Sequential Equivalence Checking (for leaf modules)
            cat > "$TMPDIR/lec_${MODULE_NAME}.ys" <<YOSYS_EOF
# Read and prepare LEAN design (gold reference)
$READ_CMD $LEAN_DIR/*.sv
hierarchy -check -top $MODULE_NAME
proc; memory; opt; flatten
rename $MODULE_NAME gold

# Stash gold design
design -stash gold

# Reset Verilog frontend
design -reset-vlog

# Read and prepare Chisel design (gate implementation)
$READ_CMD $CLEAN_CHISEL_DIR/*.sv
hierarchy -check -top $MODULE_NAME
proc; memory; opt; flatten
rename $MODULE_NAME gate

# Stash gate design
design -stash gate

# Copy both into main design for comparison
design -copy-from gold -as gold gold
design -copy-from gate -as gate gate

# Build equivalence circuit (preserve state elements)
equiv_make gold gate equiv
prep -top equiv
async2sync

# Show statistics
stat

# Perform sequential equivalence check with induction
equiv_simple -undef
equiv_induct -undef
equiv_status -assert
YOSYS_EOF
        fi
    else
        # Combinational Equivalence Checking (CEC)
        cat > "$TMPDIR/lec_${MODULE_NAME}.ys" <<YOSYS_EOF
# Read and prepare LEAN design (gold reference)
$READ_CMD $LEAN_DIR/*.sv
hierarchy -check -top $MODULE_NAME
proc; opt; memory; opt; flatten
rename $MODULE_NAME gold

# Stash gold design
design -stash gold

# Reset Verilog frontend
design -reset-vlog

# Read and prepare Chisel design (gate implementation)
$READ_CMD $CLEAN_CHISEL_DIR/*.sv
hierarchy -check -top $MODULE_NAME
proc; opt; memory; opt; flatten
rename $MODULE_NAME gate

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

    # Run Yosys and capture output
    local YOSYS_OUTPUT="$TMPDIR/yosys_output_${MODULE_NAME}.txt"
    local YOSYS_SUCCESS=0
    if yosys -s "$TMPDIR/lec_${MODULE_NAME}.ys" > "$YOSYS_OUTPUT" 2>&1; then
        YOSYS_SUCCESS=1
    fi

    # Analyze results
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
            # Record this module as verified for hierarchical checking
            echo "$MODULE_NAME" >> "$VERIFIED_MODULES_FILE"
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
echo "  Verification Summary"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

VERIFIED_COUNT=$(wc -l < "$VERIFIED_MODULES_FILE")
COMPOSITIONAL_COUNT=$(wc -l < "$COMPOSITIONAL_MODULES_FILE" 2>/dev/null || echo "0")
LEC_COUNT=$((VERIFIED_COUNT - COMPOSITIONAL_COUNT))

echo "Total modules: $MODULE_COUNT"
echo "  ✓ LEC verified: $LEC_COUNT"
echo "  ✓ Compositionally verified (Lean): $COMPOSITIONAL_COUNT"
echo "  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "  Total verified: $VERIFIED_COUNT"
echo ""

if [ "$COMPOSITIONAL_COUNT" -gt 0 ]; then
    echo "Compositionally verified modules:"
    while IFS= read -r module; do
        echo "  • $module (via Lean compositional proof)"
    done < "$COMPOSITIONAL_MODULES_FILE"
    echo ""
fi

if [ $ALL_PASSED -eq 1 ]; then
    COVERAGE=$((VERIFIED_COUNT * 100 / MODULE_COUNT))
    echo -e "${GREEN}✓ All modules verified successfully (${COVERAGE}% coverage)${NC}"
    echo ""
    echo "Verification combines:"
    echo "  • Direct LEC (Yosys SAT/induction)"
    echo "  • Compositional proofs (Lean theorem proving)"
    echo ""
    exit 0
else
    COVERAGE=$((VERIFIED_COUNT * 100 / MODULE_COUNT))
    echo -e "${RED}✗ Some modules failed verification (${COVERAGE}% coverage)${NC}"
    echo ""
    exit 1
fi
