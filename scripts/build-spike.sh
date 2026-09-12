#!/usr/bin/env bash
set -euo pipefail

SPIKE_PREFIX="${SPIKE_PREFIX:-$HOME/.local/spike}"
SPIKE_SRC="$(cd "$(dirname "$0")/../third_party/riscv-isa-sim" && pwd)"

echo "Building Spike from $SPIKE_SRC"
echo "Install prefix: $SPIKE_PREFIX"

cd "$SPIKE_SRC"
mkdir -p build && cd build
../configure --prefix="$SPIKE_PREFIX"
make -j"$(nproc)"
make install

# Strip debug symbols.  The unstripped shared objects are ~190 MB each, which
# dominates cache/artifact transfer for the cosim job; stripped they are ~8 MB.
# --strip-unneeded keeps the dynamic symbol table, so linking still works.
find "$SPIKE_PREFIX/lib" -type f -name '*.so*' \
    -exec strip --strip-unneeded {} + 2>/dev/null || true

echo "Spike installed to $SPIKE_PREFIX"
echo "Libraries: $SPIKE_PREFIX/lib"
echo "Headers:   $SPIKE_PREFIX/include"
