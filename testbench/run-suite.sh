#!/usr/bin/env bash
# run-suite.sh - parallel test-suite driver for the Shoumei testbenches.
#
# Every test is an independent process, so running one per core turns a 30-40 s
# serial sweep into a couple of seconds on a workstation.  Results are printed
# per test and written as CSV in input order (deterministic regardless of
# completion order); the exit status is non-zero if any test failed.
#
# Usage:
#   run-suite.sh --mode sim|cosim --bin <binary> [--jobs N]
#                [--default-timeout N] [--csv <path>] [--timeout <glob>=<sec>]...
#                <elf> [<elf> ...]

set -uo pipefail

MODE="sim"
BIN=""
JOBS="$(nproc)"
DEFAULT_TIMEOUT=5000
CSV="/dev/null"
declare -a OVERRIDES=()
declare -a ELFS=()

while [[ $# -gt 0 ]]; do
    case "$1" in
        --mode)            MODE="$2"; shift 2 ;;
        --bin)             BIN="$2"; shift 2 ;;
        --jobs)            JOBS="$2"; shift 2 ;;
        --default-timeout) DEFAULT_TIMEOUT="$2"; shift 2 ;;
        --csv)             CSV="$2"; shift 2 ;;
        --timeout)         OVERRIDES+=("$2"); shift 2 ;;
        -*) echo "unknown option: $1" >&2; exit 2 ;;
        *) ELFS+=("$1"); shift ;;
    esac
done

if [[ -z "$BIN" || ${#ELFS[@]} -eq 0 ]]; then
    echo "usage: run-suite.sh --mode sim|cosim --bin <binary> [--jobs N] <elf>..." >&2
    exit 2
fi

# Per-test timeout: last matching --timeout glob wins.
timeout_for() {
    local name="$1" t="$DEFAULT_TIMEOUT"
    local ov
    for ov in "${OVERRIDES[@]}"; do
        # shellcheck disable=SC2053
        if [[ "$name" == ${ov%%=*} ]]; then t="${ov##*=}"; fi
    done
    echo "$t"
}

OUT_DIR="$(mktemp -d)"
trap 'rm -rf "$OUT_DIR"' EXIT

run_one() {
    local timeout="$1" elf="$2" mode="$3" bin="$4" out_dir="$5"
    local name; name="$(basename "$elf")"
    local result
    result=$(timeout "$timeout" "$bin" +elf="$elf" +timeout="$timeout" 2>&1)

    local cycles retired ipc status
    cycles=$(echo "$result"  | grep -oP '(Cycles|Total cycles):\s+\K[0-9]+'   | tail -1)
    retired=$(echo "$result" | grep -oP '(Retired|Total retired):\s+\K[0-9]+' | tail -1)
    ipc=$(echo "$result"     | grep -oP 'IPC:\s+\K[0-9.]+'                   | tail -1)

    if [[ "$mode" == "cosim" ]]; then
        if echo "$result" | grep -q "COSIM PASS"; then status=PASS; else status=FAIL; fi
    else
        local tohost
        tohost=$(echo "$result" | grep -oP 'tohost:\s+\K0x[0-9a-fA-F]+' | tail -1)
        tohost="${tohost,,}"
        if [[ "$tohost" == "0x00000001" ]]; then status=PASS; else status=FAIL; fi
    fi

    printf '%s,%s,%s,%s,%s\n' "$status" "$name" "${cycles:-0}" "${retired:-0}" "${ipc:-0}" \
        > "$out_dir/$(echo "$name" | tr -c 'A-Za-z0-9._-' '_')"
}
export -f run_one

JOBS_FILE="$OUT_DIR/jobs.txt"
: > "$JOBS_FILE"
for elf in "${ELFS[@]}"; do
    [[ -f "$elf" ]] || continue
    echo "$(timeout_for "$(basename "$elf")") $elf" >> "$JOBS_FILE"
done

# run_one is exported; mode/bin/out_dir ride in the environment so xargs can
# supply the per-test arguments as $1/$2.
export SUITE_MODE="$MODE" SUITE_BIN="$BIN" SUITE_OUT_DIR="$OUT_DIR"
# shellcheck disable=SC2016
xargs -P "$JOBS" -a "$JOBS_FILE" -n 2 bash -c \
    'run_one "$1" "$2" "$SUITE_MODE" "$SUITE_BIN" "$SUITE_OUT_DIR"' _

echo "test,status,cycles,retired,ipc" > "$CSV"
pass=0; fail=0
while read -r _timeout elf; do
    name="$(basename "$elf")"
    rec="$OUT_DIR/$(echo "$name" | tr -c 'A-Za-z0-9._-' '_')"
    if [[ -f "$rec" ]]; then
        IFS=, read -r status _n cycles retired ipc < "$rec"
    else
        status=FAIL; cycles=0; retired=0; ipc=0
    fi
    if [[ "$status" == "PASS" ]]; then
        printf 'PASS  %s  (cycles %s, retired %s, IPC %s)\n' "$name" "$cycles" "$retired" "$ipc"
        pass=$((pass + 1))
    else
        printf 'FAIL  %s  (cycles %s, retired %s, IPC %s)\n' "$name" "$cycles" "$retired" "$ipc"
        fail=$((fail + 1))
    fi
    echo "$name,$status,$cycles,$retired,$ipc" >> "$CSV"
done < "$JOBS_FILE"

echo ""
echo "$pass/$((pass + fail)) passed, $fail failed"
[[ "$fail" -eq 0 ]]
