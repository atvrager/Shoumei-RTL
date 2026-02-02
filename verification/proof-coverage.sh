#!/bin/bash
# Proof Coverage Analysis for Shoumei RTL
#
# Scans Lean 4 source files and produces a coverage report:
#   - sorry/admit count (incomplete proofs)
#   - axiom count (unproven assumptions)
#   - theorem/lemma counts per component
#   - component x property coverage matrix
#
# Exit code: ALWAYS 0 (informational only)
# Output: Terminal report + optional markdown for CI

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"
LEAN_DIR="$PROJECT_ROOT/lean/Shoumei"
REPORT_DIR="$PROJECT_ROOT/output/proof-coverage"

# Colors (disabled if not a terminal or if NO_COLOR is set)
if [ -t 1 ] && [ -z "${NO_COLOR:-}" ]; then
    GREEN='\033[0;32m'
    RED='\033[0;31m'
    YELLOW='\033[1;33m'
    BOLD='\033[1m'
    DIM='\033[2m'
    NC='\033[0m'
else
    GREEN='' RED='' YELLOW='' BOLD='' DIM='' NC=''
fi

mkdir -p "$REPORT_DIR"

# ─── Counters ───────────────────────────────────────────────

TOTAL_THEOREMS=0
TOTAL_LEMMAS=0
TOTAL_AXIOMS=0
TOTAL_SORRY=0
TOTAL_ADMIT=0
TOTAL_PROVEN=0

# Associative arrays for per-component tracking
declare -A COMP_THEOREMS
declare -A COMP_AXIOMS
declare -A COMP_SORRY
declare -A COMP_PROVEN

# ─── Helpers ────────────────────────────────────────────────

# Map a Lean file path to a component name
file_to_component() {
    local f="$1"
    local prefix="$LEAN_DIR/"
    # shellcheck disable=SC2295
    local rel="${f#"$prefix"}"

    case "$rel" in
        Examples/Adder*.lean)           echo "FullAdder" ;;
        Circuits/Combinational/RippleCarryAdder*.lean) echo "RippleCarryAdder" ;;
        Circuits/Combinational/Subtractor*.lean)       echo "Subtractor" ;;
        Circuits/Combinational/Comparator*.lean)       echo "Comparator" ;;
        Circuits/Combinational/LogicUnit*.lean)        echo "LogicUnit" ;;
        Circuits/Combinational/Shifter*.lean)          echo "Shifter" ;;
        Circuits/Combinational/ALUBitVec*.lean)        echo "ALU-BitVec-Bridge" ;;
        Circuits/Combinational/ALU*.lean)              echo "ALU32" ;;
        Circuits/Combinational/Decoder*.lean)          echo "Decoder" ;;
        Circuits/Combinational/MuxTree*.lean)          echo "MuxTree" ;;
        Circuits/Combinational/Arbiter*.lean)          echo "Arbiter" ;;
        Circuits/Sequential/DFF*.lean)                 echo "DFlipFlop" ;;
        Circuits/Sequential/Register*.lean)            echo "Register" ;;
        Circuits/Sequential/Queue*.lean)               echo "Queue" ;;
        RISCV/Decoder*.lean)                           echo "RV32I-Decoder" ;;
        RISCV/Renaming/FreeList*.lean)                 echo "FreeList" ;;
        RISCV/Renaming/RAT*.lean)                      echo "RAT" ;;
        RISCV/Renaming/PhysRegFile*.lean)              echo "PhysRegFile" ;;
        RISCV/Renaming/RenameStage*.lean)              echo "RenameStage" ;;
        RISCV/Execution/ReservationStation*.lean)      echo "ReservationStation" ;;
        DSL/Decoupled*.lean)                           echo "Decoupled" ;;
        Verification/*.lean)                           echo "Verification-Framework" ;;
        Theorems.lean)                                 echo "Core-Theorems" ;;
        Codegen/*.lean)                                echo "Codegen" ;;
        DSL.lean|Semantics.lean)                       echo "Core-DSL" ;;
        *)                                             echo "Other" ;;
    esac
}

# No helper needed — associative array increments are inlined to avoid
# nameref-related linter warnings.

# ─── Scan ───────────────────────────────────────────────────

echo ""
echo -e "${BOLD}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo -e "${BOLD}  Proof Coverage Analysis${NC}"
echo -e "${BOLD}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo ""

# Collect all Lean files
LEAN_FILES=()
while IFS= read -r -d '' f; do
    LEAN_FILES+=("$f")
done < <(find "$LEAN_DIR" -name "*.lean" -type f -print0 | sort -z)

TOTAL_FILES=${#LEAN_FILES[@]}

# Detailed sorry/admit locations for the report
SORRY_LOCATIONS=()
AXIOM_LOCATIONS=()

PROJECT_PREFIX="$PROJECT_ROOT/"
for f in "${LEAN_FILES[@]}"; do
    comp=$(file_to_component "$f")
    # shellcheck disable=SC2295
    rel="${f#"$PROJECT_PREFIX"}"

    # Count theorems and lemmas (proven declarations)
    thm_count=$(grep -cE '^\s*(theorem|protected theorem|private theorem)\s' "$f" 2>/dev/null || true)
    lem_count=$(grep -cE '^\s*(lemma|protected lemma|private lemma)\s' "$f" 2>/dev/null || true)
    TOTAL_THEOREMS=$((TOTAL_THEOREMS + thm_count))
    TOTAL_LEMMAS=$((TOTAL_LEMMAS + lem_count))
    COMP_THEOREMS["$comp"]=$(( ${COMP_THEOREMS[$comp]:-0} + thm_count + lem_count ))

    # Count axioms
    ax_count=$(grep -cE '^\s*axiom\s' "$f" 2>/dev/null || true)
    TOTAL_AXIOMS=$((TOTAL_AXIOMS + ax_count))
    COMP_AXIOMS["$comp"]=$(( ${COMP_AXIOMS[$comp]:-0} + ax_count ))

    # Record axiom locations
    while IFS= read -r line; do
        if [ -n "$line" ]; then
            AXIOM_LOCATIONS+=("$rel:$line")
        fi
    done < <(grep -nE '^\s*axiom\s' "$f" 2>/dev/null | head -50 || true)

    # Count sorry occurrences (inside proofs)
    sorry_count=$(grep -cE '\bsorry\b' "$f" 2>/dev/null || true)
    # Exclude comments containing sorry
    sorry_comment=$(grep -cE '^\s*--.*\bsorry\b' "$f" 2>/dev/null || true)
    sorry_count=$((sorry_count - sorry_comment))
    if [ "$sorry_count" -lt 0 ]; then sorry_count=0; fi
    TOTAL_SORRY=$((TOTAL_SORRY + sorry_count))
    COMP_SORRY["$comp"]=$(( ${COMP_SORRY[$comp]:-0} + sorry_count ))

    # Record sorry locations
    while IFS= read -r line; do
        # Skip comment-only lines
        if [[ "$line" =~ ^[[:space:]]*[0-9]+[:-][[:space:]]*-- ]]; then
            continue
        fi
        if [ -n "$line" ]; then
            SORRY_LOCATIONS+=("$rel:$line")
        fi
    done < <(grep -nE '\bsorry\b' "$f" 2>/dev/null | head -50 || true)

    # Count admit occurrences
    admit_count=$(grep -cE '\badmit\b' "$f" 2>/dev/null || true)
    admit_comment=$(grep -cE '^\s*--.*\badmit\b' "$f" 2>/dev/null || true)
    admit_count=$((admit_count - admit_comment))
    if [ "$admit_count" -lt 0 ]; then admit_count=0; fi
    TOTAL_ADMIT=$((TOTAL_ADMIT + admit_count))
done

# Calculate proven counts per component
COMPONENTS=()
for comp in "${!COMP_THEOREMS[@]}"; do
    COMPONENTS+=("$comp")
done
# Add components that only have axioms
for comp in "${!COMP_AXIOMS[@]}"; do
    if [ -z "${COMP_THEOREMS[$comp]:-}" ]; then
        COMPONENTS+=("$comp")
        COMP_THEOREMS["$comp"]=0
    fi
done

# Sort components
mapfile -t COMPONENTS < <(printf '%s\n' "${COMPONENTS[@]}" | sort)

for comp in "${COMPONENTS[@]}"; do
    local_thm=${COMP_THEOREMS[$comp]:-0}
    local_ax=${COMP_AXIOMS[$comp]:-0}
    local_sorry=${COMP_SORRY[$comp]:-0}
    # Proven = theorems that don't rely on sorry (approximate: total - sorry)
    proven=$((local_thm - local_sorry))
    if [ "$proven" -lt 0 ]; then proven=0; fi
    COMP_PROVEN["$comp"]=$proven
    TOTAL_PROVEN=$((TOTAL_PROVEN + proven))
done

TOTAL_DECLS=$((TOTAL_THEOREMS + TOTAL_LEMMAS + TOTAL_AXIOMS))
TOTAL_INCOMPLETE=$((TOTAL_AXIOMS + TOTAL_SORRY + TOTAL_ADMIT))

if [ "$TOTAL_DECLS" -gt 0 ]; then
    COVERAGE_PCT=$(( (TOTAL_PROVEN * 100) / TOTAL_DECLS ))
else
    COVERAGE_PCT=0
fi

# ─── Terminal Report ────────────────────────────────────────

echo -e "${BOLD}1. Summary${NC}"
echo ""
printf "  %-28s %s\n" "Lean files scanned:" "$TOTAL_FILES"
printf "  %-28s %s\n" "Theorems + Lemmas:" "$((TOTAL_THEOREMS + TOTAL_LEMMAS))"
printf "  %-28s %s\n" "Axioms (unproven):" "$TOTAL_AXIOMS"
printf "  %-28s %s\n" "Sorry occurrences:" "$TOTAL_SORRY"
printf "  %-28s %s\n" "Admit occurrences:" "$TOTAL_ADMIT"
printf "  %-28s %s\n" "Proven (no sorry/axiom):" "$TOTAL_PROVEN"
printf "  %-28s %s\n" "Total declarations:" "$TOTAL_DECLS"
echo ""

if [ "$TOTAL_SORRY" -eq 0 ] && [ "$TOTAL_ADMIT" -eq 0 ] && [ "$TOTAL_AXIOMS" -eq 0 ]; then
    echo -e "  ${GREEN}Coverage: 100% -- All proofs complete${NC}"
elif [ "$TOTAL_SORRY" -eq 0 ] && [ "$TOTAL_ADMIT" -eq 0 ]; then
    echo -e "  ${YELLOW}Coverage: ${COVERAGE_PCT}% -- No sorry/admit, but ${TOTAL_AXIOMS} axioms remain${NC}"
else
    echo -e "  ${YELLOW}Coverage: ${COVERAGE_PCT}%${NC}"
fi
echo ""

# ─── Per-Component Table ────────────────────────────────────

echo -e "${BOLD}2. Per-Component Coverage${NC}"
echo ""
printf "  %b%-24s %8s %8s %8s %8s%b\n" "$DIM" "Component" "Proven" "Axioms" "Sorry" "Coverage" "$NC"
printf "  %b%-24s %8s %8s %8s %8s%b\n" "$DIM" "------------------------" "--------" "--------" "--------" "--------" "$NC"

for comp in "${COMPONENTS[@]}"; do
    local_proven=${COMP_PROVEN[$comp]:-0}
    local_ax=${COMP_AXIOMS[$comp]:-0}
    local_sorry=${COMP_SORRY[$comp]:-0}
    local_total=$((local_proven + local_ax + local_sorry))

    if [ "$local_total" -eq 0 ]; then
        pct="n/a"
        color="$DIM"
    elif [ "$local_ax" -eq 0 ] && [ "$local_sorry" -eq 0 ]; then
        pct="100%"
        color="$GREEN"
    else
        pct="$(( (local_proven * 100) / local_total ))%"
        color="$YELLOW"
    fi

    printf "  %b%-24s %8d %8d %8d %8s%b\n" \
        "$color" "$comp" "$local_proven" "$local_ax" "$local_sorry" "$pct" "$NC"
done
echo ""

# ─── Sorry Locations ────────────────────────────────────────

if [ "${#SORRY_LOCATIONS[@]}" -gt 0 ]; then
    echo -e "${BOLD}3. Sorry Locations${NC}"
    echo ""
    for loc in "${SORRY_LOCATIONS[@]}"; do
        echo -e "  ${RED}$loc${NC}"
    done
    echo ""
fi

# ─── Axiom Locations ────────────────────────────────────────

if [ "${#AXIOM_LOCATIONS[@]}" -gt 0 ]; then
    echo -e "${BOLD}4. Axiom Locations${NC}"
    echo ""
    for loc in "${AXIOM_LOCATIONS[@]}"; do
        echo -e "  ${YELLOW}$loc${NC}"
    done
    echo ""
fi

# ─── Coverage Matrix ────────────────────────────────────────

echo -e "${BOLD}5. Coverage Matrix (Component x Property Type)${NC}"
echo ""
echo "  Legend: [x] = proven  [~] = axiom/sorry  [ ] = no coverage"
echo ""

# For each component, classify its proofs into categories
# Categories: Structural (gate/port counts), Behavioral (correctness), Protocol (handshaking/ordering)
printf "  %-24s %12s %12s %12s\n" "Component" "Structural" "Behavioral" "Protocol"
printf "  %-24s %12s %12s %12s\n" "--------" "--------" "--------" "--------"

classify_component() {
    local comp="$1"
    local structural="[ ]"
    local behavioral="[ ]"
    local protocol="[ ]"

    case "$comp" in
        FullAdder)
            structural="[x]"; behavioral="[x]" ;;
        RippleCarryAdder|Subtractor|Comparator|LogicUnit|Shifter)
            structural="[x]"; behavioral="[ ]" ;;
        ALU32)
            structural="[x]"; behavioral="[ ]" ;;
        ALU-BitVec-Bridge)
            structural="[ ]"; behavioral="[~]" ;;
        Decoder)
            structural="[x]"; behavioral="[x]" ;;
        MuxTree)
            structural="[x]"; behavioral="[x]" ;;
        Arbiter)
            structural="[ ]"; behavioral="[~]"; protocol="[~]" ;;
        DFlipFlop)
            structural="[x]"; behavioral="[x]" ;;
        Register)
            structural="[x]"; behavioral="[x]" ;;
        Queue)
            structural="[x]"; behavioral="[x]"; protocol="[x]" ;;
        RV32I-Decoder)
            structural="[x]"; behavioral="[x]" ;;
        FreeList)
            structural="[x]"; behavioral="[x]" ;;
        RAT)
            structural="[x]"; behavioral="[x]" ;;
        PhysRegFile)
            structural="[x]"; behavioral="[x]" ;;
        RenameStage)
            structural="[x]"; behavioral="[~]" ;;
        ReservationStation)
            structural="[x]"; behavioral="[~]" ;;
        Decoupled)
            structural="[ ]"; behavioral="[ ]"; protocol="[~]" ;;
        Core-Theorems)
            behavioral="[~]" ;;
        *)
            ;;
    esac

    printf "  %-24s %12s %12s %12s\n" "$comp" "$structural" "$behavioral" "$protocol"
}

for comp in "${COMPONENTS[@]}"; do
    classify_component "$comp"
done
echo ""

# ─── Markdown Report ────────────────────────────────────────

MD="$REPORT_DIR/proof-coverage.md"
{
    echo "# Proof Coverage Report"
    echo ""
    echo "Generated: $(date -u '+%Y-%m-%d %H:%M:%S UTC')"
    echo ""
    echo "## Summary"
    echo ""
    echo "| Metric | Count |"
    echo "|--------|------:|"
    echo "| Lean files scanned | $TOTAL_FILES |"
    echo "| Theorems + Lemmas | $((TOTAL_THEOREMS + TOTAL_LEMMAS)) |"
    echo "| Axioms (unproven) | $TOTAL_AXIOMS |"
    echo "| Sorry occurrences | $TOTAL_SORRY |"
    echo "| Admit occurrences | $TOTAL_ADMIT |"
    echo "| Proven (no sorry/axiom) | $TOTAL_PROVEN |"
    echo "| **Coverage** | **${COVERAGE_PCT}%** |"
    echo ""
    echo "## Per-Component Coverage"
    echo ""
    echo "| Component | Proven | Axioms | Sorry | Coverage |"
    echo "|-----------|-------:|-------:|------:|---------:|"

    for comp in "${COMPONENTS[@]}"; do
        local_proven=${COMP_PROVEN[$comp]:-0}
        local_ax=${COMP_AXIOMS[$comp]:-0}
        local_sorry=${COMP_SORRY[$comp]:-0}
        local_total=$((local_proven + local_ax + local_sorry))
        if [ "$local_total" -eq 0 ]; then
            pct="n/a"
        elif [ "$local_ax" -eq 0 ] && [ "$local_sorry" -eq 0 ]; then
            pct="100%"
        else
            pct="$(( (local_proven * 100) / local_total ))%"
        fi
        echo "| $comp | $local_proven | $local_ax | $local_sorry | $pct |"
    done

    echo ""
    echo "## Coverage Matrix"
    echo ""
    echo "Legend: x = proven, ~ = axiom/sorry, blank = no coverage"
    echo ""
    echo "| Component | Structural | Behavioral | Protocol |"
    echo "|-----------|:----------:|:----------:|:--------:|"

    matrix_row() {
        local comp="$1"
        local s="" b="" p=""
        case "$comp" in
            FullAdder)              s="x"; b="x" ;;
            RippleCarryAdder|Subtractor|Comparator|LogicUnit|Shifter)
                                    s="x" ;;
            ALU32)                  s="x" ;;
            ALU-BitVec-Bridge)      b="~" ;;
            Decoder)                s="x"; b="x" ;;
            MuxTree)                s="x"; b="x" ;;
            Arbiter)                b="~"; p="~" ;;
            DFlipFlop)              s="x"; b="x" ;;
            Register)               s="x"; b="x" ;;
            Queue)                  s="x"; b="x"; p="x" ;;
            RV32I-Decoder)          s="x"; b="x" ;;
            FreeList)               s="x"; b="x" ;;
            RAT)                    s="x"; b="x" ;;
            PhysRegFile)            s="x"; b="x" ;;
            RenameStage)            s="x"; b="~" ;;
            ReservationStation)     s="x"; b="~" ;;
            Decoupled)              p="~" ;;
            Core-Theorems)          b="~" ;;
        esac
        echo "| $comp | $s | $b | $p |"
    }

    for comp in "${COMPONENTS[@]}"; do
        matrix_row "$comp"
    done

    if [ "${#SORRY_LOCATIONS[@]}" -gt 0 ]; then
        echo ""
        echo "## Sorry Locations"
        echo ""
        echo '```'
        for loc in "${SORRY_LOCATIONS[@]}"; do
            echo "$loc"
        done
        echo '```'
    fi

    if [ "${#AXIOM_LOCATIONS[@]}" -gt 0 ]; then
        echo ""
        echo "## Axiom Locations"
        echo ""
        echo '```'
        for loc in "${AXIOM_LOCATIONS[@]}"; do
            echo "$loc"
        done
        echo '```'
    fi

    echo ""
    echo "## Gaps to Close"
    echo ""
    echo "### Priority 1: Remove sorry"
    echo ""
    if [ "$TOTAL_SORRY" -gt 0 ]; then
        echo "There are **$TOTAL_SORRY** sorry occurrences to resolve."
    else
        echo "No sorry found."
    fi
    echo ""
    echo "### Priority 2: Prove axioms"
    echo ""
    if [ "$TOTAL_AXIOMS" -gt 0 ]; then
        echo "There are **$TOTAL_AXIOMS** axioms to prove or justify."
    else
        echo "No axioms remaining."
    fi
    echo ""
    echo "### Priority 3: Add behavioral proofs"
    echo ""
    echo "The following components have only structural proofs (gate/port counts)"
    echo "but no behavioral correctness proofs:"
    echo ""
    for comp in RippleCarryAdder Subtractor Comparator LogicUnit Shifter ALU32; do
        if [ -n "${COMP_THEOREMS[$comp]:-}" ]; then
            echo "- **$comp**: needs arithmetic/functional correctness theorems"
        fi
    done
} > "$MD"

echo -e "${DIM}Markdown report: $MD${NC}"

# ─── GitHub Actions Job Summary ─────────────────────────────

if [ -n "${GITHUB_STEP_SUMMARY:-}" ]; then
    cat "$MD" >> "$GITHUB_STEP_SUMMARY"
    echo ""
    echo -e "${DIM}Written to GitHub Actions job summary${NC}"
fi

# ─── JSON output for programmatic use ───────────────────────

JSON="$REPORT_DIR/proof-coverage.json"
{
    echo "{"
    echo "  \"generated\": \"$(date -u '+%Y-%m-%dT%H:%M:%SZ')\","
    echo "  \"total_files\": $TOTAL_FILES,"
    echo "  \"total_theorems\": $((TOTAL_THEOREMS + TOTAL_LEMMAS)),"
    echo "  \"total_axioms\": $TOTAL_AXIOMS,"
    echo "  \"total_sorry\": $TOTAL_SORRY,"
    echo "  \"total_admit\": $TOTAL_ADMIT,"
    echo "  \"total_proven\": $TOTAL_PROVEN,"
    echo "  \"total_declarations\": $TOTAL_DECLS,"
    echo "  \"coverage_pct\": $COVERAGE_PCT,"
    echo "  \"components\": {"

    first=true
    for comp in "${COMPONENTS[@]}"; do
        local_proven=${COMP_PROVEN[$comp]:-0}
        local_ax=${COMP_AXIOMS[$comp]:-0}
        local_sorry=${COMP_SORRY[$comp]:-0}
        local_total=$((local_proven + local_ax + local_sorry))
        if [ "$local_total" -gt 0 ]; then
            local_pct=$(( (local_proven * 100) / local_total ))
        else
            local_pct=0
        fi

        if [ "$first" = true ]; then first=false; else echo ","; fi
        printf "    \"%s\": {\"proven\": %d, \"axioms\": %d, \"sorry\": %d, \"coverage_pct\": %d}" \
            "$comp" "$local_proven" "$local_ax" "$local_sorry" "$local_pct"
    done

    echo ""
    echo "  }"
    echo "}"
} > "$JSON"

echo -e "${DIM}JSON report:    $JSON${NC}"
echo ""

# ─── Final status line ──────────────────────────────────────

echo -e "${BOLD}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
if [ "$TOTAL_SORRY" -eq 0 ] && [ "$TOTAL_ADMIT" -eq 0 ] && [ "$TOTAL_AXIOMS" -eq 0 ]; then
    echo -e "${GREEN}  PROOF COVERAGE: 100% -- All ${TOTAL_DECLS} declarations fully proven${NC}"
else
    echo -e "${YELLOW}  PROOF COVERAGE: ${COVERAGE_PCT}% -- ${TOTAL_PROVEN}/${TOTAL_DECLS} proven, ${TOTAL_INCOMPLETE} gaps remaining${NC}"
fi
echo -e "${BOLD}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo ""

# Always exit 0 -- this is informational only
exit 0
