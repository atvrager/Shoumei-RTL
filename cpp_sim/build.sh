#!/bin/bash
set -e

echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "  証明 Shoumei RTL - SystemC Compilation"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

# Check SystemC installation via pkg-config, ldconfig, or common paths
SYSTEMC_FOUND=false

if pkg-config --exists systemc 2>/dev/null; then
  SYSTEMC_FOUND=true
elif ldconfig -p 2>/dev/null | grep -q libsystemc; then
  SYSTEMC_FOUND=true
else
  for d in /usr/lib /usr/local/lib /usr/lib/x86_64-linux-gnu /usr/lib/aarch64-linux-gnu; do
    if [ -f "$d/libsystemc.so" ] || [ -f "$d/libsystemc.a" ]; then
      SYSTEMC_FOUND=true
      break
    fi
  done
fi

if [ "$SYSTEMC_FOUND" = false ]; then
  echo ""
  echo "ERROR: SystemC not found"
  echo ""
  echo "Install SystemC:"
  echo "  Ubuntu/Debian: sudo apt-get install libsystemc-dev"
  echo "  Arch Linux:    yay -S systemc"
  echo "  macOS:         brew install systemc"
  echo "  Manual:        https://github.com/accellera-official/systemc"
  echo ""
  exit 1
fi

echo ""
echo "SystemC found"
echo ""

# Build
mkdir -p build
cd build
cmake ..
make -j"$(nproc)"

echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "✓ SystemC compilation complete"
echo "  Object files in: systemc/build/"
echo "  Phase 3 will add testbench executables"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
