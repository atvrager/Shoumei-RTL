#!/usr/bin/env bash
# sec-verify.sh - Sequential Equivalence Checking (SEC) runner
#
# Verifies sequential equivalence between alternative circuit implementations
# (e.g., flat vs hierarchical registers, clock-enable loopbacks, delay pipelines).
#
# Supported backends:
#   1. Yosys (default, open-source): SAT miter verification
#   2. Formality (--formality): Synopsys Formality formal equivalence checking
#
# Usage:
#   verification/sec-verify.sh                  # Run all Yosys SEC checks
#   verification/sec-verify.sh --formality      # Run Formality locally (if fm_shell in PATH)
#   verification/sec-verify.sh --remote <host>  # Run Formality remotely via SSH
#

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
cd "$ROOT"

SEC_DIR="output/sv-sec"
BACKEND="yosys"
REMOTE_HOST=""
FM_BIN="${FM_BIN:-fm_shell}"

while [[ $# -gt 0 ]]; do
  case "$1" in
    --formality)
      BACKEND="formality"
      shift
      ;;
    --remote)
      REMOTE_HOST="$2"
      BACKEND="formality"
      shift 2
      ;;
    -h|--help)
      echo "Usage: $0 [--formality] [--remote <host>]"
      exit 0
      ;;
    *)
      echo "Unknown argument: $1"
      exit 1
      ;;
  esac
done

if [[ ! -d "$SEC_DIR" ]]; then
  echo "==> SEC output directory not found. Running codegen..."
  lake --no-ansi exe generate_all
fi

echo "============================================================"
echo "  Shoumei Sequential Equivalence Checking (SEC)"
echo "  Backend: $BACKEND"
echo "============================================================"

PASS_COUNT=0
FAIL_COUNT=0

if [[ "$BACKEND" == "yosys" ]]; then
  if ! command -v yosys >/dev/null 2>&1; then
    echo "ERROR: yosys not found in PATH"
    exit 1
  fi

  for script in "$SEC_DIR"/*_yosys.tcl; do
    [[ -f "$script" ]] || continue
    name="$(basename "$script" _yosys.tcl)"
    echo -n "Checking $name (Yosys SAT)... "
    if yosys -q -s "$script" >/dev/null 2>&1; then
      echo "PASS (QED)"
      PASS_COUNT=$((PASS_COUNT + 1))
    else
      echo "FAIL"
      FAIL_COUNT=$((FAIL_COUNT + 1))
    fi
  done

elif [[ "$BACKEND" == "formality" ]]; then
  if [[ -n "$REMOTE_HOST" ]]; then
    echo "Running Formality remotely on $REMOTE_HOST..."
    TMP_REMOTE="sec_run_$(date +%s)"
    # shellcheck disable=SC2029
    ssh "$REMOTE_HOST" "mkdir -p '$TMP_REMOTE'"
    # shellcheck disable=SC2029
    tar -cf - -C "$ROOT/output/sv-from-lean" . -C "$ROOT/$SEC_DIR" . | ssh "$REMOTE_HOST" "tar -xf - -C '$TMP_REMOTE'"

    for script in "$SEC_DIR"/*_formality.tcl; do
      [[ -f "$script" ]] || continue
      tcl_name="$(basename "$script")"
      name="$(basename "$script" _formality.tcl)"
      echo -n "Checking $name (Synopsys Formality on $REMOTE_HOST)... "
      # shellcheck disable=SC2029
      if ssh "$REMOTE_HOST" "cd '$TMP_REMOTE' && { [ -f ~/.profile ] && source ~/.profile >/dev/null 2>&1 || true; } && { [ -f ~/.bashrc ] && source ~/.bashrc >/dev/null 2>&1 || true; } && { [ -f ~/.zshrc ] && source ~/.zshrc >/dev/null 2>&1 || true; } && ${FM_BIN} -f '$tcl_name' < /dev/null" >/dev/null 2>&1; then
        echo "PASS"
        PASS_COUNT=$((PASS_COUNT + 1))
      else
        echo "FAIL"
        FAIL_COUNT=$((FAIL_COUNT + 1))
      fi
    done
    # shellcheck disable=SC2029
    ssh "$REMOTE_HOST" "rm -rf '$TMP_REMOTE'"
  else
    if ! command -v "$FM_BIN" >/dev/null 2>&1; then
      echo "ERROR: $FM_BIN not found in PATH (use --remote <host> for remote execution)"
      exit 1
    fi
    for script in "$SEC_DIR"/*_formality.tcl; do
      [[ -f "$script" ]] || continue
      name="$(basename "$script" _formality.tcl)"
      echo -n "Checking $name (Synopsys Formality)... "
      if "$FM_BIN" -f "$script" < /dev/null >/dev/null 2>&1; then
        echo "PASS"
        PASS_COUNT=$((PASS_COUNT + 1))
      else
        echo "FAIL"
        FAIL_COUNT=$((FAIL_COUNT + 1))
      fi
    done
  fi
fi

echo "============================================================"
echo "  SEC Results: $PASS_COUNT passed, $FAIL_COUNT failed"
echo "============================================================"

if [[ $FAIL_COUNT -gt 0 ]]; then
  exit 1
fi
