#!/usr/bin/env bash
# setup-riscv-toolchain.sh - Download prebuilt RISC-V toolchain
# Idempotent: skips if already installed.
set -euo pipefail

RISCV_DIR="${RISCV_DIR:-$HOME/.local/riscv64-elf}"
TAG="2026.01.23"
URL="https://github.com/riscv-collab/riscv-gnu-toolchain/releases/download/${TAG}/riscv64-elf-ubuntu-22.04-gcc.tar.xz"

if [ -x "${RISCV_DIR}/bin/riscv64-unknown-elf-gcc" ] || [ -x "${RISCV_DIR}/bin/riscv64-elf-gcc" ]; then
    echo "RISC-V toolchain already installed at ${RISCV_DIR}"
    exit 0
fi

echo "Downloading RISC-V toolchain (tag ${TAG})..."
mkdir -p "${RISCV_DIR}"
curl -fSL "${URL}" | tar xJ -C "${RISCV_DIR}" --strip-components=1

# Create symlinks with riscv64-elf- prefix if only riscv64-unknown-elf- is present
for tool in "${RISCV_DIR}/bin/riscv64-unknown-elf-"*; do
    if [ -f "$tool" ]; then
        base=$(basename "$tool")
        short="${base/riscv64-unknown-elf-/riscv64-elf-}"
        if [ ! -f "${RISCV_DIR}/bin/$short" ]; then
            ln -sf "$base" "${RISCV_DIR}/bin/$short"
        fi
    fi
done

echo "Installed to ${RISCV_DIR}"
echo "Add to PATH:  export PATH=\"${RISCV_DIR}/bin:\$PATH\""
