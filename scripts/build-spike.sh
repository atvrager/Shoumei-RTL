#!/usr/bin/env bash
set -euo pipefail

SPIKE_PREFIX="${SPIKE_PREFIX:-$HOME/.local/spike}"
SPIKE_SRC="$(cd "$(dirname "$0")/../third_party/riscv-isa-sim" && pwd)"

echo "Building Spike from $SPIKE_SRC"
echo "Install prefix: $SPIKE_PREFIX"

cd "$SPIKE_SRC"
mkdir -p build && cd build
../configure --prefix="$SPIKE_PREFIX" --enable-commitlog
make -j"$(nproc)"
make install

echo "Spike installed to $SPIKE_PREFIX"
echo "Libraries: $SPIKE_PREFIX/lib"
echo "Headers:   $SPIKE_PREFIX/include"
