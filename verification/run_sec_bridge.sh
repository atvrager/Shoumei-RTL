#!/usr/bin/env bash
# verification/run_sec_bridge.sh - Certified Dual-RTL bridge test under Bazel
set -euo pipefail

if [ $# -lt 3 ]; then
    echo "Usage: $0 <smt2lean_bin> <sva2lean_bin> <sv_dir> [modules...]" >&2
    exit 1
fi

SMT2LEAN_BIN="$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"
SVA2LEAN_BIN="$(cd "$(dirname "$2")" && pwd)/$(basename "$2")"
SV_DIR_ARG="$(cd "$3" && pwd)"
shift 3

MODULES=("$@")
if [ ${#MODULES[@]} -eq 0 ]; then
    # Default representative modules
    MODULES=("FullAdder" "ALU32")
fi

ROOT="${TEST_SRCDIR}/${TEST_WORKSPACE}"
if [ ! -d "$ROOT/verification" ]; then
    ROOT="."
fi

# Ensure lean compiler is in PATH
for elan_cand in \
    "/usr/local/google/home/atv/.elan/toolchains/leanprover--lean4---v4.34.1/bin" \
    "$HOME/.elan/toolchains/leanprover--lean4---v4.34.1/bin" \
    "$HOME/.elan/bin" "$HOME/bin" \
    "/usr/local/google/home/atv/.elan/bin" "/usr/local/google/home/atv/bin"; do
    if [ -d "$elan_cand" ]; then
        export PATH="$elan_cand:$PATH"
    fi
done

if [ -d "/usr/local/google/home/atv/.elan" ] && [ ! -d "${HOME}/.elan" ]; then
    export ELAN_HOME="/usr/local/google/home/atv/.elan"
fi

WORK_DIR="${TEST_TMPDIR:-/tmp}/sec_bridge_work"
rm -rf "$WORK_DIR"
mkdir -p "$WORK_DIR/verification/bridge"
mkdir -p "$WORK_DIR/output/sec-bridge/ShoumeiSec/Bridge"
mkdir -p "$WORK_DIR/scripts"

cp -rL "$ROOT/verification/specs" "$WORK_DIR/verification/"
cp -L "$ROOT/scripts/gen-bridges.py" "$WORK_DIR/scripts/"
if [ -f "$ROOT/lean-toolchain" ]; then
    cp -L "$ROOT/lean-toolchain" "$WORK_DIR/"
fi

export SMT2LEAN="$SMT2LEAN_BIN"
export SVA2LEAN="$SVA2LEAN_BIN"
export SV_DIR="$SV_DIR_ARG"

echo "==> Running Certified Dual-RTL Bridge generation for: ${MODULES[*]}"
(
    cd "$WORK_DIR"
    python3 scripts/gen-bridges.py "${MODULES[@]}"
)

echo "==> Verifying generated Lean bv_decide proofs..."
export LEAN_PATH="$WORK_DIR/output/sec-bridge:${ROOT}/bazel-bin/lean"

for mod in "${MODULES[@]}"; do
    spec_lean="$WORK_DIR/output/sec-bridge/ShoumeiSec/Bridge/${mod}Spec.lean"
    impl_lean="$WORK_DIR/output/sec-bridge/ShoumeiSec/Bridge/${mod}Impl.lean"
    proof_lean="$WORK_DIR/output/sec-bridge/ShoumeiSec/Bridge${mod}.lean"

    if [ -f "$spec_lean" ] && [ -f "$impl_lean" ] && [ -f "$proof_lean" ]; then
        echo "  Verifying $mod (bv_decide)..."
        lean -R "$WORK_DIR/output/sec-bridge" -o "${spec_lean%.lean}.olean" "$spec_lean"
        lean -R "$WORK_DIR/output/sec-bridge" -o "${impl_lean%.lean}.olean" "$impl_lean"
        lean -R "$WORK_DIR/output/sec-bridge" -o "${proof_lean%.lean}.olean" "$proof_lean"
        echo "  ✓ $mod passed"
    fi
done

echo ""
echo "✓ Certified Dual-RTL bridge verification passed (${MODULES[*]}, bv_decide, 0 axioms)"
