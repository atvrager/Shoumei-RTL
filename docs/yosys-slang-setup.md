# yosys-slang Setup Guide

This document explains how to install and configure yosys-slang for enhanced SystemVerilog support when reading and elaborating Shoumei's emitted RTL with Yosys.

## What is yosys-slang?

yosys-slang is a Yosys plugin that integrates the `slang` SystemVerilog compiler as a frontend. It provides:

- **Full SystemVerilog 2017 support**: Better standard compliance than built-in Yosys parser
- **Struct type support**: Proper handling of packed structs for interface bundles
- **Better diagnostics**: More helpful error messages for syntax issues
- **Improved parsing**: Handles complex SystemVerilog constructs more reliably

## When is it needed?

Yosys can read the emitted SystemVerilog with either frontend:

- **read_verilog -sv** (default): Works for all current Shoumei modules
  - Handles basic SystemVerilog features
  - Sufficient for flat wire-based designs
  - No additional installation required

- **read_slang** (optional): Enhanced support
  - Required for struct-based interface bundles (future Phase 4 enhancement)
  - Better error messages and diagnostics
  - Full SystemVerilog 2017 compliance

**Current status**: Phase 4 SVV2 generator uses typed buses (`logic [31:0]`) which work with both parsers. Struct support is planned for future enhancement.

## Installation

### Prerequisites

- Yosys 0.60+ installed
- CMake 3.15+
- C++20 compiler (GCC 10+ or Clang 10+)
- Git

### Option 1: AUR Package (Arch Linux)

```bash
yay -S yosys-slang-git
# or
paru -S yosys-slang-git
```

This installs the plugin to `/usr/share/yosys/plugins/slang.so`.

### Option 2: Build from Source

```bash
# Clone the repository
git clone https://github.com/povik/yosys-slang.git
cd yosys-slang

# Build and install
mkdir build && cd build
cmake .. -DCMAKE_BUILD_TYPE=Release
make -j$(nproc)
sudo make install
```

By default, this installs to `/usr/local/share/yosys/plugins/slang.so`.

### Option 3: Manual Plugin Path

If installed to a custom location:

```bash
export YOSYS_PLUGINS="/path/to/plugin/directory"
```

Add this to your `~/.bashrc` or `~/.zshrc` to make it persistent.

## Verification

Test that yosys-slang is working:

```bash
yosys -m slang -p "help read_slang"
```

Expected output:
```
    read_slang [options] [filenames]

Load SystemVerilog source files using slang frontend.
```

If you see an error like:
```
ERROR: Can't load module `./slang': ... cannot open shared object file
```

Then slang is not installed or not in the plugin search path.

## Using Yosys on Shoumei's RTL

`make systemverilog` runs `verification/validate-sv.sh output/sv-from-lean`, which
reads every emitted SystemVerilog file with Yosys and checks the design hierarchy
(`hierarchy -auto-top`). That script uses the built-in `read_verilog -sv` frontend,
which handles all current Shoumei modules.

To read the same files with yosys-slang instead, load the plugin and use `read_slang`:

```bash
yosys -m slang -p "read_slang output/sv-from-lean/RV32IDecoder.sv; hierarchy -auto-top"
```

In your own Yosys scripts, swap the `read_verilog -sv "<file>"` line for
`read_slang "<file>"`; everything after the read step is unchanged.

## Troubleshooting

### Plugin not found

**Error**: `ERROR: Can't load module './slang'`

**Solution**:
1. Verify installation: `find /usr -name "slang.so" 2>/dev/null`
2. Check plugin path: `yosys -p "plugin -list"`
3. Set `YOSYS_PLUGINS` environment variable if needed

### Slang build failures

**Error**: CMake can't find slang library

**Solution**:
```bash
# Install slang library first
git clone https://github.com/MikePopoloski/slang.git
cd slang
cmake -B build
cmake --build build -j$(nproc)
sudo cmake --install build
```

Then retry yosys-slang build.

### Version mismatches

**Error**: `undefined symbol` errors when loading plugin

**Solution**: Rebuild yosys-slang against your current Yosys version:
```bash
cd yosys-slang/build
cmake .. -DCMAKE_BUILD_TYPE=Release
make clean && make -j$(nproc)
sudo make install
```

## Checking the Parser

Confirm which frontend Yosys loads:

```bash
yosys -m slang -p "help read_slang"   # yosys-slang plugin available
yosys -p "help read_verilog"          # built-in SystemVerilog frontend
```

## Migration Plan

**Phase 5 (Current)**: Both frontends work for the emitted SV
- `read_verilog -sv` handles all current modules
- `read_slang` is a drop-in replacement for the read step
- No breaking changes

**Phase 4 Enhancement (Future)**: Add struct-based interface bundles
- Generate `shoumei_types.sv` package with struct definitions
- Use structs for complex interfaces (e.g., CDB entries, Decoupled bundles)
- **Requires yosys-slang** for struct flattening when Yosys reads the emitted SV

**Phase 6 (Planned)**: Netlist codegen
- Flat netlist output for formal tools
- Independent of parser choice

## References

- [yosys-slang GitHub](https://github.com/povik/yosys-slang)
- [slang GitHub](https://github.com/MikePopoloski/slang)
- [Yosys Documentation](https://yosyshq.readthedocs.io/)
- [SystemVerilog 2017 Spec (IEEE 1800-2017)](https://ieeexplore.ieee.org/document/8299595)

## See Also

- [verification-guide.md](verification-guide.md) - Full verification workflow
- [codegen-v2.md](codegen-v2.md) - Code generation architecture
- [adding-a-module.md](adding-a-module.md) - Module development guide
