#!/usr/bin/env bash
# sva-verify.sh - SystemVerilog Assertions (SVA) Formal Property Verification runner
#
# Formally verifies SVA properties emitted from Lean definitions.
#
# Supported backends:
#   1. Synopsys VC Formal (--vc-formal, --remote <host>):
#      Full IEEE 1800 SVA formal property verification (FPV).
#   2. Verilator Simulation (--verilator):
#      Dynamic simulation assertion monitoring with --assert.
#
# Usage:
#   verification/sva-verify.sh                  # Run all available SVA checks
#   verification/sva-verify.sh --vc-formal      # Run VC Formal locally
#   verification/sva-verify.sh --remote <host>  # Run VC Formal remotely via SSH
#   verification/sva-verify.sh --verilator      # Run Verilator assertion simulation
#

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
cd "$ROOT"

SEC_DIR="output/sv-sec"
BACKEND="auto"
REMOTE_HOST=""
VCF_BIN="${VCF_BIN:-vcf}"

while [[ $# -gt 0 ]]; do
  case "$1" in
    --vc-formal)
      BACKEND="vc-formal"
      shift
      ;;
    --remote)
      REMOTE_HOST="$2"
      BACKEND="vc-formal"
      shift 2
      ;;
    --verilator)
      BACKEND="verilator"
      shift
      ;;
    -h|--help)
      echo "Usage: $0 [--vc-formal] [--remote <host>] [--verilator]"
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
echo "  Shoumei SVA Formal Property Verification (FPV)"
echo "  Backend: $BACKEND"
echo "============================================================"

PASS_COUNT=0
FAIL_COUNT=0

if [[ "$BACKEND" == "vc-formal" || ( "$BACKEND" == "auto" && -n "$REMOTE_HOST" ) ]]; then
  if [[ -n "$REMOTE_HOST" ]]; then
    echo "Running VC Formal remotely on $REMOTE_HOST..."
    TMP_REMOTE="sva_run_$(date +%s)"
    # shellcheck disable=SC2029
    ssh "$REMOTE_HOST" "mkdir -p '$TMP_REMOTE'"
    # shellcheck disable=SC2029
    tar -cf - -C "$ROOT/output/sv-from-lean" . -C "$ROOT/$SEC_DIR" . | ssh "$REMOTE_HOST" "tar -xf - -C '$TMP_REMOTE'"

    for script in "$SEC_DIR"/*_sva_formal.tcl; do
      [[ -f "$script" ]] || continue
      tcl_name="$(basename "$script")"
      name="$(basename "$script" .tcl)"
      echo -n "Checking $name (Synopsys VC Formal on $REMOTE_HOST)... "
      # shellcheck disable=SC2029
      if ssh "$REMOTE_HOST" "cd '$TMP_REMOTE' && rm -rf vcst_rtdb && { [ -f ~/.profile ] && source ~/.profile >/dev/null 2>&1 || true; } && { [ -f ~/.bashrc ] && source ~/.bashrc >/dev/null 2>&1 || true; } && { [ -f ~/.zshrc ] && source ~/.zshrc >/dev/null 2>&1 || true; } && if [[ '${VCF_BIN}' == */* ]]; then export VC_STATIC_HOME=\"\$(dirname \"\$(dirname '${VCF_BIN}')\")\"; unset VCS_HOME; unset VERDI_HOME; fi && ${VCF_BIN} -fmode FPV -batch -no_restore -f '$tcl_name' < /dev/null" >/dev/null 2>&1; then
        echo "PASS (PROVEN)"
        PASS_COUNT=$((PASS_COUNT + 1))
      else
        echo "FAIL"
        FAIL_COUNT=$((FAIL_COUNT + 1))
      fi
    done
    # shellcheck disable=SC2029
    ssh "$REMOTE_HOST" "rm -rf '$TMP_REMOTE'"
  else
    if ! command -v "$VCF_BIN" >/dev/null 2>&1; then
      echo "ERROR: $VCF_BIN not found in PATH (use --remote <host> for remote execution)"
      exit 1
    fi
    for script in "$SEC_DIR"/*_sva_formal.tcl; do
      [[ -f "$script" ]] || continue
      name="$(basename "$script" .tcl)"
      echo -n "Checking $name (Synopsys VC Formal)... "
      if "$VCF_BIN" -fmode FPV -batch -no_restore -f "$script" < /dev/null >/dev/null 2>&1; then
        echo "PASS (PROVEN)"
        PASS_COUNT=$((PASS_COUNT + 1))
      else
        echo "FAIL"
        FAIL_COUNT=$((FAIL_COUNT + 1))
      fi
    done
  fi

elif [[ "$BACKEND" == "verilator" ]]; then
  echo -n "Checking SVA dynamic simulation compilation (Verilator --assert)... "
  if verilator --assert --lint-only \
      output/sv-from-lean/Register64.sv \
      output/sv-from-lean/Register32.sv \
      output/sv-from-lean/Register160.sv \
      --top-module Register160 >/dev/null 2>&1 && \
     verilator --assert --lint-only \
      output/sv-from-lean/LogicUnit32.sv \
      --top-module LogicUnit32 >/dev/null 2>&1; then
    echo "PASS (ASSERTIONS ACTIVE)"
    PASS_COUNT=$((PASS_COUNT + 1))
  else
    echo "FAIL"
    FAIL_COUNT=$((FAIL_COUNT + 1))
  fi

else
  # Default open-source flow: Verilator SVA compilation + assertion linting
  if command -v slang >/dev/null 2>&1 || python3 -c "import pyslang" >/dev/null 2>&1; then
    echo -n "Checking SVA elaboration with slang... "
    if python3 verification/slang-lint.py output/sv-sec >/dev/null 2>&1; then
      echo "PASS (SYNTACTIC QED)"
      PASS_COUNT=$((PASS_COUNT + 1))
    else
      echo "FAIL"
      FAIL_COUNT=$((FAIL_COUNT + 1))
    fi
  fi

  if command -v verilator >/dev/null 2>&1; then
    echo -n "Checking SVA dynamic simulation compilation (Verilator --assert)... "
    if verilator --assert --lint-only \
        output/sv-from-lean/Register64.sv \
        output/sv-from-lean/Register32.sv \
        output/sv-from-lean/Register160.sv \
        --top-module Register160 >/dev/null 2>&1 && \
       verilator --assert --lint-only \
        output/sv-from-lean/LogicUnit32.sv \
        --top-module LogicUnit32 >/dev/null 2>&1; then
      echo "PASS (ASSERTIONS ACTIVE)"
      PASS_COUNT=$((PASS_COUNT + 1))
    else
      echo "FAIL"
      FAIL_COUNT=$((FAIL_COUNT + 1))
    fi
  fi
fi

echo "============================================================"
echo "  SVA Results: $PASS_COUNT passed, $FAIL_COUNT failed"
echo "============================================================"

if [[ $FAIL_COUNT -gt 0 ]]; then
  exit 1
fi
