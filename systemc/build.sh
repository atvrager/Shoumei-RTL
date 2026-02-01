#!/bin/bash
set -e

echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "  証明 Shoumei RTL - SystemC Compilation"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

# Check SystemC installation (library or headers)
if [ ! -f /usr/lib/libsystemc.so ] && [ ! -f /usr/local/lib/libsystemc.so ]; then
  echo ""
  echo "ERROR: SystemC not found"
  echo ""
  echo "Install SystemC:"
  echo "  Arch Linux:    yay -S systemc"
  echo "  Ubuntu/Debian: sudo apt-get install systemc systemc-dev"
  echo "  macOS:         brew install systemc"
  echo "  Manual:        https://github.com/accellera-official/systemc"
  echo ""
  exit 1
fi

echo ""
echo "SystemC found: /usr/lib/libsystemc.so"
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
