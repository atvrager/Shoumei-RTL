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
#                [--timeout-json <manifest>] [--kanata-dir <dir>]
#                <elf> [<elf> ...]

set -uo pipefail

MODE="sim"
BIN=""
JOBS="$(nproc)"
DEFAULT_TIMEOUT=5000
CSV="/dev/null"
COV_DIR=""
KANATA_DIR=""
BENCH_CSV=""
TIMEOUT_JSON=""
declare -a OVERRIDES=()
declare -a ELFS=()

while [[ $# -gt 0 ]]; do
    case "$1" in
        --mode)            MODE="$2"; shift 2 ;;
        --bin)             BIN="$2"; shift 2 ;;
        --jobs)            JOBS="$2"; shift 2 ;;
        --default-timeout) DEFAULT_TIMEOUT="$2"; shift 2 ;;
        --timeout-json)    TIMEOUT_JSON="$2"; shift 2 ;;
        --csv)             CSV="$2"; shift 2 ;;
        --bench-csv)       BENCH_CSV="$2"; shift 2 ;;
        --coverage-dir)    COV_DIR="$2"; shift 2 ;;
        --kanata-dir)      KANATA_DIR="$2"; shift 2 ;;
        --timeout)         OVERRIDES+=("$2"); shift 2 ;;
        -*) echo "unknown option: $1" >&2; exit 2 ;;
        *) ELFS+=("$1"); shift ;;
    esac
done

if [[ -z "$BIN" || ${#ELFS[@]} -eq 0 ]]; then
    echo "usage: run-suite.sh --mode sim|cosim --bin <binary> [--jobs N] <elf>..." >&2
    exit 2
fi

# Per-test timeout: last matching --timeout glob wins.  A glob is matched against
# both the basename and the full path, so a suite sub-directory carries its own
# budget without listing every program (e.g. --timeout '*bench*=3000000').
#
# --timeout-json supplies a per-test budget from a benchmark manifest
# ({name, march, max_cycles}).  It is consulted first and the globs act as an
# override, so a hung benchmark fails inside its own bound rather than a
# suite-wide cap.  ELF basename -> spec name strips the .elf suffix and the
# march prefix (fp_/amo_/zb_), matching how the emitter names the programs.
json_timeout_for() {
    local name="$1"
    [[ -n "$TIMEOUT_JSON" && -f "$TIMEOUT_JSON" ]] || return 1
    python3 - "$TIMEOUT_JSON" "$name" <<'PY'
import json, sys
manifest, name = sys.argv[1], sys.argv[2]
spec = name[:-4] if name.endswith(".elf") else name
for prefix in ("fp_", "amo_", "zb_"):
    if spec.startswith(prefix):
        spec = spec[len(prefix):]
        break
for entry in json.load(open(manifest)):
    if entry.get("name") == spec:
        print(entry.get("max_cycles", ""))
        break
PY
}

timeout_for() {
    local name="$1" path="$2" t="$DEFAULT_TIMEOUT"
    local jt
    jt="$(json_timeout_for "$name")"
    if [[ -n "$jt" ]]; then t="$jt"; fi
    local ov
    for ov in "${OVERRIDES[@]}"; do
        # shellcheck disable=SC2053
        if [[ "$name" == ${ov%%=*} || "$path" == ${ov%%=*} ]]; then t="${ov##*=}"; fi
    done
    echo "$t"
}

OUT_DIR="$(mktemp -d)"
trap 'rm -rf "$OUT_DIR"' EXIT

run_one() {
    local timeout="$1" elf="$2" mode="$3" bin="$4" out_dir="$5" cov_dir="${6:-}"
    local name; name="$(basename "$elf")"
    local cov_arg=()
    if [[ -n "$cov_dir" ]]; then
        cov_arg=("+cov_file=$cov_dir/${name}.dat")
    fi
    local kanata_arg=()
    if [[ -n "$SUITE_KANATA_DIR" ]]; then
        kanata_arg=("+kanata=$SUITE_KANATA_DIR/${name}.txt")
    fi
    local result
    result=$(timeout "$timeout" "$bin" +elf="$elf" +timeout="$timeout" "${cov_arg[@]}" "${kanata_arg[@]}" 2>&1)

    # Per-benchmark CPI lines ("BENCH <name> <thr_milli> <lat_milli>") land in
    # a per-test file; the driver aggregates them in input order at the end.
    if [[ -n "$SUITE_BENCH_CSV" ]]; then
        echo "$result" | grep '^BENCH ' > "$out_dir/bench_$(basename "$elf")" || true
    fi

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
    echo "$(timeout_for "$(basename "$elf")" "$elf") $elf" >> "$JOBS_FILE"
done

if [[ -n "$COV_DIR" ]]; then
    mkdir -p "$COV_DIR"
fi

if [[ -n "$KANATA_DIR" ]]; then
    mkdir -p "$KANATA_DIR"
fi

# run_one is exported; mode/bin/out_dir/cov_dir ride in the environment so xargs can
# supply the per-test arguments as $1/$2.
export SUITE_MODE="$MODE" SUITE_BIN="$BIN" SUITE_OUT_DIR="$OUT_DIR" SUITE_COV_DIR="$COV_DIR"
export SUITE_KANATA_DIR="$KANATA_DIR" SUITE_BENCH_CSV="$BENCH_CSV"
# shellcheck disable=SC2016
xargs -P "$JOBS" -a "$JOBS_FILE" -n 2 bash -c \
    'run_one "$1" "$2" "$SUITE_MODE" "$SUITE_BIN" "$SUITE_OUT_DIR" "$SUITE_COV_DIR"' _

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

# Aggregate per-benchmark CPI rows into the suite bench CSV (input order):
# name,throughput_cpi_milli,latency_cpi_milli
if [[ -n "$BENCH_CSV" && "$BENCH_CSV" != "/dev/null" ]]; then
    printf 'name,throughput_cpi_milli,latency_cpi_milli\n' > "$BENCH_CSV"
    while read -r _t elf; do
        name="$(basename "$elf")"
        rec="$OUT_DIR/bench_$name"
        if [[ -f "$rec" ]]; then
            sed 's/^BENCH //; s/ /,/g' "$rec" >> "$BENCH_CSV"
        fi
    done < "$JOBS_FILE"
fi

echo ""
echo "$pass/$((pass + fail)) passed, $fail failed"

if [[ -n "$COV_DIR" ]] && compgen -G "$COV_DIR/*.dat" > /dev/null; then
    echo ""
    echo "==> Merging coverage data..."
    mkdir -p "$COV_DIR/annotated"
    # Merge individual test coverage files
    # shellcheck disable=SC2086
    verilator_coverage --write "$COV_DIR/coverage.dat" "$COV_DIR"/*.dat
    echo "==> Generating annotated source files in $COV_DIR/annotated..."
    verilator_coverage --annotate "$COV_DIR/annotated" "$COV_DIR/coverage.dat"
    verilator_coverage --write-info "$COV_DIR/coverage.info" "$COV_DIR/coverage.dat"
    echo ""
    echo "==> Coverage summary:"
    verilator_coverage "$COV_DIR/coverage.dat"
fi

[[ "$fail" -eq 0 ]]
