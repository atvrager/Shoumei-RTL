#!/usr/bin/env bash
# Generate cache SRAM macros with OpenRAM for the data RAMs.
#
# The codegen contract (SystemVerilog.lean, SHOUMEI_SRAM_MACROS branch) is:
#   sram_1r1w_<width>x<depth>  (.clk, .we, .waddr, .wdata, .raddr, .rdata)
#
# This script runs OpenRAM per geometry and emits a shim module with the
# canonical name instantiating the OpenRAM macro, so the contract is immune
# to OpenRAM's internal naming.
#
# Usage:
#   scripts/gen-sram-macros.sh [node] [outdir]
#     node : gf180mcu (default) | asap7
#     outdir : third_party/sram-macros/<node> (default)
#
# Requires: openram on PATH (see https://github.com/VLSIDA/OpenRAM)
# Optional env: OPENRAM_PDK_OPTIONS for extra OpenRAM flags (e.g. timing corners)
set -euo pipefail

NODE="${1:-gf180mcu}"
OUT="${2:-third_party/sram-macros/$NODE}"

case "$NODE" in
  gf180mcu) PDK=gf180mcuD ;;
  asap7)    PDK=asap7 ;;
  *)
    echo "error: unknown node '$NODE' (gf180mcu | asap7)" >&2
    exit 1
    ;;
esac

if ! command -v openram > /dev/null 2>&1; then
  echo "error: 'openram' not found. Install OpenRAM (pip install openram or build from VLSIDA/OpenRAM)." >&2
  exit 1
fi

mkdir -p "$OUT"

# Geometries currently emitted by the cache hierarchy:
#   L1D: 2x 4 deep x 256 wide, L1I: 8x256, L2: 2x 8x256
# Scaled sizes repeat the pattern (depth = lines per way).
GEOMS="${SRAM_GEOMS:-4x256 8x256}"

for geom in $GEOMS; do
  depth="${geom%x*}"
  width="${geom#*x}"
  depth_bits=$(python3 -c 'import math; print(max(1, math.ceil(math.log2('"$depth"'))))')
  echo "==> OpenRAM: ${width}w x ${depth}d (PDK ${PDK})"

  # Extra OpenRAM flags (word-split intentionally, e.g. timing corners).
  read -ra EXTRA <<< "${OPENRAM_PDK_OPTIONS:-}"

  openram \
    --outdir="$OUT" \
    --pdk="$PDK" \
    --width="$width" \
    --depth="$depth" \
    --rport=1 --wport=1 \
    --output_name="sram_1r1w_${width}x${depth}_openram" \
    "${EXTRA[@]}"

  # Shim with the canonical contract name -> OpenRAM macro.
  cat > "$OUT/sram_1r1w_${width}x${depth}.sv" <<EOF
// Shim: canonical SRAM contract (codegen SHOUMEI_SRAM_MACROS branch)
// -> OpenRAM-generated macro. Do not edit.
module sram_1r1w_${width}x${depth} (
  input  wire              clk,
  input  wire              we,
  input  wire [$((depth_bits - 1)):0] waddr,
  input  wire [$((width - 1)):0] wdata,
  input  wire [$((depth_bits - 1)):0] raddr,
  output wire [$((width - 1)):0] rdata
);
  sram_1r1w_${width}x${depth}_openram u_ram (
    .clk   (clk),
    .we    (we),
    .waddr (waddr),
    .wdata (wdata),
    .raddr (raddr),
    .rdata (rdata)
  );
endmodule
EOF
done

echo "Generated SRAM macros in $OUT (contract: sram_1r1w_<width>x<depth>)."