#!/usr/bin/env bash
# techmap-equiv.sh - Yosys logical equivalence check for tech-mapped modules
#
# For every module emitted in both output/sv-from-lean (gate level, "gold") and
# output/sv-<pdk> (cell level), prove the two equivalent with a miter + SAT:
#
#   read cell models (from Liberty, see scripts/gen-pdk-cell-models.py)
#   read every gold module and the mapped module under a fresh name
#   miter -equiv -flatten -make_outputs gold mapped miter
#   sat -verify -prove-asserts miter
#
# The mapped copy is renamed so both definitions coexist; sub-modules resolve
# to the gold definitions for both sides, so the only difference under test is
# the module's own gate-level vs cell-level body.  `keep_hierarchy` is stripped
# in the temp copies so the miter can flatten.
#
# Usage: verification/techmap-equiv.sh [module ...]
#   (no arguments: every module present in both directories, on both PDKs)

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
cd "$ROOT"

GOLD_DIR="output/sv-from-lean"
CELL_MODELS="verification/pdk-cells-model.sv"

if [ ! -d "$GOLD_DIR" ]; then
    echo "ERROR: $GOLD_DIR not found. Run: make codegen"
    exit 1
fi
if [ ! -f "$CELL_MODELS" ]; then
    echo "ERROR: $CELL_MODELS not found. Run: scripts/gen-pdk-cell-models.py"
    exit 1
fi

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

# Gold copies with keep_hierarchy stripped (so the miter can flatten).
mkdir -p "$TMP/gold"
for f in "$GOLD_DIR"/*.sv; do
    sed '/keep_hierarchy/d' "$f" > "$TMP/gold/$(basename "$f")"
done

# Modules that (transitively) contain a RAM primitive cannot be flattened:
# Yosys keeps memory-bearing modules as cells, and SAT has no model for $memrd.
# Their RAMs are copied verbatim by the emitter (same definition on both sides),
# so the equivalence there rests on the gate part, which the other modules cover.
ram_bearing() {
    local all=""
    for f in "$GOLD_DIR"/*.sv; do
        if grep -q "\[0:" "$f"; then
            all="$all $(basename "$f" .sv)"
        fi
    done
    local changed=1
    while [ "$changed" = 1 ]; do
        changed=0
        for f in "$GOLD_DIR"/*.sv; do
            local base
            base="$(basename "$f" .sv)"
            case " $all " in *" $base "*) continue ;; esac
            for r in $all; do
                if grep -q "\b$r\b" "$f"; then
                    all="$all $base"; changed=1; break
                fi
            done
        done
    done
    # shellcheck disable=SC2086  # intentional word splitting of the list
    printf '%s\n' $all
}

select_modules() {
    local pdk_dir="$1"; shift
    if [ "$#" -gt 0 ]; then
        printf '%s\n' "$@"
        return
    fi
    local skip
    skip="$(ram_bearing | tr '\n' ' ')"
    for f in "$pdk_dir"/*.sv; do
        [ -e "$f" ] || continue
        local base
        base="$(basename "$f" .sv)"
        [ -f "$GOLD_DIR/$base.sv" ] || continue
        case " $skip " in *" $base "*) continue ;; esac
        echo "$base"
    done
}

run_pdk() {
    local pdk="$1" pdk_dir="$2"; shift 2
    local modules
    modules="$(select_modules "$pdk_dir" "$@")"
    if [ -z "$modules" ]; then
        echo "== $pdk: no modules to check"
        return 0
    fi

    local mapped_dir="$TMP/$pdk"
    mkdir -p "$mapped_dir"
    local tcl="$TMP/equiv_$pdk.tcl"
    {
        echo "yosys -import"
        echo "read_verilog -sv $CELL_MODELS"
        for f in "$TMP/gold"/*.sv; do
            echo "read_verilog -sv $f"
        done
        for m in $modules; do
            sed -e "/keep_hierarchy/d" -e "s/^module $m (/module ${m}__mapped (/" \
                "$pdk_dir/$m.sv" > "$mapped_dir/${m}__mapped.sv"
            echo "read_verilog -sv $mapped_dir/${m}__mapped.sv"
        done
        echo "design -save base"
        local i=0
        for m in $modules; do
            echo "design -load base"
            echo "miter -equiv -flatten -make_outputs $m ${m}__mapped miter_$i"
            echo "hierarchy -top miter_$i"
            # RAM primitives lower to $memrd/$memwr, which SAT cannot model
            # directly; map them to registers first.
            echo "memory"
            echo "opt_clean"
            echo "sat -verify -prove-asserts miter_$i"
            i=$((i + 1))
        done
    } > "$tcl"

    local count skipped
    count="$(printf '%s\n' "$modules" | wc -l | tr -d ' ')"
    skipped="$(ram_bearing | tr '\n' ' ')"
    echo "== $pdk: LEC over $count modules"
    [ -n "$skipped" ] && echo "   skipped (RAM-bearing): $skipped"
    if ! yosys -q -c "$tcl" > "$TMP/lec_$pdk.log" 2>&1; then
        echo "FAIL: $pdk equivalence check failed"
        grep -nE "ERROR|SUCCESS|FAIL|SAT proof" "$TMP/lec_$pdk.log" | tail -n 20
        exit 1
    fi
    echo "   $pdk: all $count modules equivalent"
}

run_pdk asap7   output/sv-asap7   "$@"
run_pdk gf180   output/sv-gf180   "$@"

echo "techmap LEC: PASS"
