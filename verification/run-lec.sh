#!/bin/bash
# Logical Equivalence Checking with Yosys
# Provides detailed diagnostics on success or failure
#
# Usage:
#   ./run-lec.sh                    # Verify all modules
#   ./run-lec.sh -m ROB16           # Verify ROB16 + its dependencies only
#   ./run-lec.sh -m ROB16 -m RAT_32x6  # Verify multiple targets + deps
#   ./run-lec.sh -j 8               # Parallel LEC with 8 jobs per dependency level
#   ./run-lec.sh --force            # Ignore cache, re-verify everything
#   ./run-lec.sh --use-slang        # Force use of yosys-slang (errors if not available)
#   ./run-lec.sh --no-slang         # Force use of $READ_CMD

set -e

LEAN_DIR="output/sv-from-lean"
CHISEL_DIR="output/sv-from-chisel"
declare -a TARGET_MODULES=()
USE_SLANG="auto"  # auto, yes, no
PARALLEL_JOBS=$(( $(nproc) - 1 ))  # -j N for parallel LEC within dependency levels
[ "$PARALLEL_JOBS" -lt 1 ] && PARALLEL_JOBS=1
FORCE_RERUN=0      # --force to ignore cache
LEC_CACHE_DIR=".lec-cache"

while [[ $# -gt 0 ]]; do
    case $1 in
        -m|--module)
            TARGET_MODULES+=("$2")
            shift 2
            ;;
        -j|--jobs)
            PARALLEL_JOBS="$2"
            shift 2
            ;;
        --force)
            FORCE_RERUN=1
            shift
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

# Determine the project root (directory containing this script's parent)
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"
CERTS_FILE="$PROJECT_ROOT/verification/compositional-certs.txt"

# Try sources in order: pre-generated file (from make codegen) > built binary > lake exe
CERT_SOURCE=""
if [ -f "$CERTS_FILE" ] && [ -s "$CERTS_FILE" ]; then
    CERT_SOURCE="$CERTS_FILE"
    echo "  Reading from $CERTS_FILE"
fi

if [ -n "$CERT_SOURCE" ]; then
    while IFS='|' read -r module deps proof; do
        [[ -z "$module" ]] && continue
        module=$(echo "$module" | xargs)
        deps=$(echo "$deps" | xargs)
        proof=$(echo "$proof" | xargs)
        COMPOSITIONAL_CERTS["$module"]="$deps|$proof"
    done < "$CERT_SOURCE"
else
    echo "  No pre-generated certs file found, trying to export from Lean..."
    while IFS='|' read -r module deps proof; do
        [[ -z "$module" ]] && continue
        module=$(echo "$module" | xargs)
        deps=$(echo "$deps" | xargs)
        proof=$(echo "$proof" | xargs)
        COMPOSITIONAL_CERTS["$module"]="$deps|$proof"
    done < <(.lake/build/bin/export_verification_certs 2>/dev/null || \
        lake exe export_verification_certs 2>/dev/null || \
        "$HOME/.elan/bin/lake" exe export_verification_certs 2>/dev/null || \
        true)
fi

echo "Loaded ${#COMPOSITIONAL_CERTS[@]} compositional certificate(s)"
if [ ${#COMPOSITIONAL_CERTS[@]} -eq 0 ]; then
    echo -e "${YELLOW}⚠ No compositional certificates loaded. Large hierarchical modules may fail LEC.${NC}"
    echo "  Run 'make codegen' first, or ensure 'lake build export_verification_certs' succeeds."
fi
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
mkdir -p "$LEC_CACHE_DIR"
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

    # Cache check: skip if sources haven't changed since last successful LEC
    local CACHE_STAMP="$LEC_CACHE_DIR/$MODULE_NAME.ok"
    local CERT_FILE="verification/compositional-certs.txt"
    if [ "$FORCE_RERUN" -eq 0 ] && [ -f "$CACHE_STAMP" ]; then
        local stale=0
        # Re-run if Lean SV, Chisel SV, or certs file changed
        if [ "$LEAN_FILE" -nt "$CACHE_STAMP" ]; then stale=1; fi
        if [ -f "$CHISEL_FILE" ] && [ "$CHISEL_FILE" -nt "$CACHE_STAMP" ]; then stale=1; fi
        if [ -f "$CERT_FILE" ] && [ "$CERT_FILE" -nt "$CACHE_STAMP" ]; then stale=1; fi
        if [ "$stale" -eq 0 ]; then
            echo -e "  ${GREEN}✓ $MODULE_NAME${NC} (cached)"
            echo "$MODULE_NAME" >> "$VERIFIED_MODULES_FILE"
            # Also record compositional if applicable
            if [ -n "${COMPOSITIONAL_CERTS[$MODULE_NAME]}" ]; then
                echo "$MODULE_NAME" >> "$COMPOSITIONAL_MODULES_FILE"
            fi
            return 0
        fi
    fi

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
            touch "$CACHE_STAMP"
            return 0
        else
            echo -e "${YELLOW}⚠ COMPOSITIONAL VERIFICATION INCOMPLETE${NC}"
            echo "  Missing dependencies:$MISSING_DEPS"
            echo "  Attempting full LEC instead..."
            echo ""
        fi
    fi

    # Check if corresponding Chisel file exists (needed for direct LEC)
    if [ ! -f "$CHISEL_FILE" ]; then
        echo -e "${RED}✗ No Chisel output found for $MODULE_NAME${NC}"
        echo "  Expected: $CHISEL_FILE"
        return 1
    fi

    echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
    echo "  Verifying: $MODULE_NAME (direct LEC)"
    echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
    echo "  LEAN:   $LEAN_FILE"
    echo "  Chisel: $CHISEL_FILE"
    echo ""

    # Check if this is a sequential circuit
    # Detection: always block OR clock/reset inputs
    local IS_SEQUENTIAL=0
    if grep -qE "always(_ff)? @|input .*clock|input .*reset" "$LEAN_FILE"; then
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

    # Plugin loading command (if using slang)
    local PLUGIN_CMD=""
    if [ "$READ_CMD" = "read_slang" ]; then
        PLUGIN_CMD="plugin -i slang"
    fi

    # Extract module dependencies from a SystemVerilog file
    # Returns list of instantiated module names (one per line)
    get_module_dependencies() {
        local svfile="$1"
        # Pattern: ModuleName instance_name (
        grep -oE '^\s*[A-Z][a-zA-Z0-9_]*\s+[a-z_][a-zA-Z0-9_]*\s*\(' "$svfile" | \
            awk '{print $1}' | sort -u
    }

    # Generate read commands for a specific module + its dependencies
    # For slang: reads only the module and its deps (not all files)
    # For built-in: still reads all files (wildcards work fine)
    # Collect transitive dependencies for a module
    collect_transitive_deps() {
        local dir="$1"
        shift
        local -a queue=("$@")
        local -A visited=()
        local -a all_files=()

        while [ ${#queue[@]} -gt 0 ]; do
            local mod="${queue[0]}"
            queue=("${queue[@]:1}")
            if [ -n "${visited[$mod]+x}" ]; then continue; fi
            visited[$mod]=1

            local mod_file="$dir/${mod}.sv"
            if [ -f "$mod_file" ] || [ -L "$mod_file" ]; then
                all_files+=("$mod_file")
                local deps
                deps=$(get_module_dependencies "$mod_file")
                for dep in $deps; do
                    if [ -z "${visited[$dep]+x}" ]; then
                        queue+=("$dep")
                    fi
                done
            fi
        done
        echo "${all_files[*]}"
    }

    generate_read_commands_for_module() {
        local module_name="$1"
        local dir="$2"

        if [ "$READ_CMD" = "read_slang" ]; then
            # For slang, collect module + transitive dependencies
            local files
            files=$(collect_transitive_deps "$dir" "$module_name")
            echo "$READ_CMD $files"
        else
            # Built-in parser can handle wildcards
            echo "$READ_CMD $dir/*.sv"
        fi
    }

    # Get read commands for this specific module
    LEAN_READ_CMDS=$(generate_read_commands_for_module "$MODULE_NAME" "$LEAN_DIR")
    CHISEL_READ_CMDS=$(generate_read_commands_for_module "$MODULE_NAME" "$CLEAN_CHISEL_DIR")

    # Create Yosys script for equivalence checking
    if [ $IS_SEQUENTIAL -eq 1 ]; then
        if [ $HAS_HIERARCHY -eq 1 ]; then
            # Hierarchical Sequential Equivalence Checking
            # Strategy: Flatten and use standard induction depth
            local INDUCT_DEPTH=3

            cat > "$TMPDIR/lec_${MODULE_NAME}.ys" <<YOSYS_EOF
# Load slang plugin if needed
$PLUGIN_CMD

# Read and prepare LEAN design (gold reference)
$LEAN_READ_CMDS
hierarchy -check -top $MODULE_NAME
proc; memory; opt; setattr -mod -unset keep_hierarchy; flatten
rename $MODULE_NAME gold

# Stash gold design
design -stash gold

# Full reset (needed for slang - reset-vlog not sufficient)
design -reset

# Read and prepare Chisel design (gate implementation)
$CHISEL_READ_CMDS
hierarchy -check -top $MODULE_NAME
proc; memory; opt; setattr -mod -unset keep_hierarchy; flatten
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
# Load slang plugin if needed
$PLUGIN_CMD

# Read and prepare LEAN design (gold reference)
$LEAN_READ_CMDS
hierarchy -check -top $MODULE_NAME
proc; memory; opt; setattr -mod -unset keep_hierarchy; flatten
rename $MODULE_NAME gold

# Stash gold design
design -stash gold

# Full reset (needed for slang - reset-vlog not sufficient)
design -reset

# Read and prepare Chisel design (gate implementation)
$CHISEL_READ_CMDS
hierarchy -check -top $MODULE_NAME
proc; memory; opt; setattr -mod -unset keep_hierarchy; flatten
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
# Load slang plugin if needed
$PLUGIN_CMD

# Read and prepare LEAN design (gold reference)
$LEAN_READ_CMDS
hierarchy -check -top $MODULE_NAME
proc; opt; memory; opt; setattr -mod -unset keep_hierarchy; flatten
rename $MODULE_NAME gold

# Stash gold design
design -stash gold

# Full reset (needed for slang - reset-vlog not sufficient)
design -reset

# Read and prepare Chisel design (gate implementation)
$CHISEL_READ_CMDS
hierarchy -check -top $MODULE_NAME
proc; opt; memory; opt; setattr -mod -unset keep_hierarchy; flatten
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
            touch "$CACHE_STAMP"
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
echo "  Running LEC on all modules (jobs=$PARALLEL_JOBS)"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

if [ "$PARALLEL_JOBS" -le 1 ]; then
    # Serial mode (original behavior)
    while IFS= read -r LEAN_FILE; do
        if ! verify_module "$LEAN_FILE"; then
            ALL_PASSED=0
        fi
    done <<< "$LEAN_MODULES"
else
    # Parallel mode: compute dependency levels, run each level in parallel
    # Build dependency depth map using compositional certs
    declare -A MODULE_DEPTH

    # First pass: initialize depths
    while IFS= read -r file; do
        mod=$(basename "$file" .sv)
        mod=$(basename "$mod" .v)
        MODULE_DEPTH[$mod]=0
    done <<< "$LEAN_MODULES"

    # Iteratively compute depths from compositional cert dependencies
    changed=1
    while [ "$changed" -eq 1 ]; do
        changed=0
        for mod in "${!MODULE_DEPTH[@]}"; do
            if [ -n "${COMPOSITIONAL_CERTS[$mod]}" ]; then
                IFS='|' read -r deps _proof <<< "${COMPOSITIONAL_CERTS[$mod]}"
                IFS=',' read -ra DEP_ARRAY <<< "$deps"
                max_dep=0
                for dep in "${DEP_ARRAY[@]}"; do
                    dep=$(echo "$dep" | xargs)
                    dep_d=${MODULE_DEPTH[$dep]:-0}
                    if [ "$dep_d" -gt "$max_dep" ]; then
                        max_dep=$dep_d
                    fi
                done
                new_depth=$((max_dep + 1))
                if [ "$new_depth" -gt "${MODULE_DEPTH[$mod]}" ]; then
                    MODULE_DEPTH[$mod]=$new_depth
                    changed=1
                fi
            fi
        done
    done

    # Find max depth
    max_level=0
    for mod in "${!MODULE_DEPTH[@]}"; do
        if [ "${MODULE_DEPTH[$mod]}" -gt "$max_level" ]; then
            max_level=${MODULE_DEPTH[$mod]}
        fi
    done

    echo "Dependency levels: 0..$max_level (parallel within each level)"
    echo ""

    # Process each level
    FAIL_FILE=$(mktemp)
    echo "0" > "$FAIL_FILE"
    PARALLEL_LOG_DIR=$(mktemp -d)

    for level in $(seq 0 "$max_level"); do
        # Collect modules at this level (preserving topo order)
        LEVEL_FILES=""
        while IFS= read -r file; do
            mod=$(basename "$file" .sv)
            mod=$(basename "$mod" .v)
            if [ "${MODULE_DEPTH[$mod]}" -eq "$level" ]; then
                LEVEL_FILES="$LEVEL_FILES"$'\n'"$file"
            fi
        done <<< "$LEAN_MODULES"
        LEVEL_FILES=$(echo "$LEVEL_FILES" | sed '/^$/d')

        if [ -z "$LEVEL_FILES" ]; then continue; fi
        LEVEL_COUNT=$(echo "$LEVEL_FILES" | wc -l)
        echo "── Level $level ($LEVEL_COUNT modules) ──"

        # Run modules at this level in parallel via background jobs
        pids=()
        running=0
        while IFS= read -r LEAN_FILE; do
            if [ "$running" -ge "$PARALLEL_JOBS" ]; then
                wait -n 2>/dev/null || true
                running=$((running - 1))
            fi
            mod=$(basename "$LEAN_FILE" .sv)
            mod=$(basename "$mod" .v)
            (
                if ! verify_module "$LEAN_FILE" > "$PARALLEL_LOG_DIR/$mod.log" 2>&1; then
                    echo "1" > "$FAIL_FILE"
                fi
            ) &
            pids+=($!)
            running=$((running + 1))
        done <<< "$LEVEL_FILES"

        # Wait for all jobs in this level to complete
        for pid in "${pids[@]}"; do
            wait "$pid" 2>/dev/null || true
        done

        # Print collected output in order
        while IFS= read -r file; do
            mod=$(basename "$file" .sv)
            mod=$(basename "$mod" .v)
            if [ -f "$PARALLEL_LOG_DIR/$mod.log" ]; then
                cat "$PARALLEL_LOG_DIR/$mod.log"
                rm -f "$PARALLEL_LOG_DIR/$mod.log"
            fi
        done <<< "$LEVEL_FILES"
    done

    if [ "$(cat "$FAIL_FILE")" = "1" ]; then
        ALL_PASSED=0
    fi
    rm -f "$FAIL_FILE"
    rm -rf "$PARALLEL_LOG_DIR"
fi

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
