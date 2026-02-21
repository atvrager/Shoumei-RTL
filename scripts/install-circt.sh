#!/usr/bin/env bash
# Install CIRCT/firtool 1.140.0 (arcilator, circt-verilog, firtool)
#
# Downloads circt-full-shared-linux-x64.tar.gz from GitHub releases,
# extracts to CIRCT_PREFIX (default: ~/.local/circt).
#
# Usage:
#   ./scripts/install-circt.sh              # install to ~/.local/circt
#   CIRCT_PREFIX=/opt/circt ./scripts/install-circt.sh

set -euo pipefail

CIRCT_VERSION="firtool-1.140.0"
CIRCT_TARBALL="circt-full-shared-linux-x64.tar.gz"
CIRCT_URL="https://github.com/llvm/circt/releases/download/${CIRCT_VERSION}/${CIRCT_TARBALL}"

CIRCT_PREFIX="${CIRCT_PREFIX:-${HOME}/.local/circt}"

echo "==> Installing CIRCT ${CIRCT_VERSION} to ${CIRCT_PREFIX}"

# Check if already installed
if [ -x "${CIRCT_PREFIX}/bin/firtool" ] && \
   [ -x "${CIRCT_PREFIX}/bin/arcilator" ] && \
   [ -x "${CIRCT_PREFIX}/bin/circt-verilog" ]; then
    installed_ver=$("${CIRCT_PREFIX}/bin/firtool" --version 2>&1 || true)
    echo "CIRCT already installed: ${installed_ver}"
    echo "To reinstall, remove ${CIRCT_PREFIX} and re-run."
    exit 0
fi

# Download
tmpdir=$(mktemp -d)
trap 'rm -rf "${tmpdir}"' EXIT

echo "Downloading ${CIRCT_URL} ..."
curl -fSL --progress-bar -o "${tmpdir}/${CIRCT_TARBALL}" "${CIRCT_URL}"

# Extract
echo "Extracting to ${CIRCT_PREFIX} ..."
mkdir -p "${CIRCT_PREFIX}"
tar xzf "${tmpdir}/${CIRCT_TARBALL}" -C "${CIRCT_PREFIX}" --strip-components=1

# Verify required binaries
for bin in firtool arcilator circt-verilog; do
    if [ ! -x "${CIRCT_PREFIX}/bin/${bin}" ]; then
        echo "ERROR: ${bin} not found after extraction" >&2
        exit 1
    fi
done

echo ""
echo "Installed binaries:"
echo "  firtool:       $("${CIRCT_PREFIX}/bin/firtool" --version 2>&1 || echo unknown)"
echo "  arcilator:     ${CIRCT_PREFIX}/bin/arcilator"
echo "  circt-verilog: ${CIRCT_PREFIX}/bin/circt-verilog"
echo ""
echo "Add to PATH:"
echo "  export PATH=\"${CIRCT_PREFIX}/bin:\$PATH\""
