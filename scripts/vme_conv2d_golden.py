#!/usr/bin/env python3
"""Generate golden test vectors for int8 Conv2D using VME outer-product.

Filter shape: [Cout=48, kH=4, kW=4, Cin=48]
Input shape:  [N=1, H=8, W=8, Cin=48]  (NHWC layout)
Output shape: [N=1, Hout=5, Wout=5, Cout=48]  (stride=1, no padding)

The Conv2D is decomposed into a sequence of outer-product accumulate operations
on the VME accumulator, following the im2col approach:

1. im2col transforms input patches into a matrix A of shape [Hout*Wout, kH*kW*Cin]
2. Filter is reshaped to B of shape [kH*kW*Cin, Cout]
3. Output = A @ B, shape [Hout*Wout, Cout]

For VME with VLEN=128 and int8 (16 elements per vector register):
- Tile size: 16×16 accumulator
- A tiles: ceil(25/16)=2 row tiles × ceil(768/16)=48 k-tiles
- B tiles: 48 k-tiles × ceil(48/16)=3 col tiles
- Total outer products: 2 × 3 × 48 = 288 VOPACC_AVV operations

Output format: C header with test vectors for RTL simulation.
"""

import numpy as np
import struct
import sys
from pathlib import Path


def conv2d_nhwc_int8(input_nhwc, filter_oihw_transposed, stride=1):
    """Pure numpy int8 Conv2D in NHWC layout with int32 accumulation."""
    N, H, W, Cin = input_nhwc.shape
    Cout, kH, kW, Cin2 = filter_oihw_transposed.shape
    assert Cin == Cin2

    Hout = (H - kH) // stride + 1
    Wout = (W - kW) // stride + 1

    output = np.zeros((N, Hout, Wout, Cout), dtype=np.int32)
    for n in range(N):
        for oh in range(Hout):
            for ow in range(Wout):
                for co in range(Cout):
                    acc = np.int32(0)
                    for kh in range(kH):
                        for kw in range(kW):
                            for ci in range(Cin):
                                a = np.int32(input_nhwc[n, oh*stride+kh, ow*stride+kw, ci])
                                b = np.int32(filter_oihw_transposed[co, kh, kw, ci])
                                acc += a * b
                    output[n, oh, ow, co] = acc
    return output


def im2col(input_nhwc, kH, kW, stride=1):
    """im2col: extract patches into matrix [Hout*Wout, kH*kW*Cin]."""
    N, H, W, Cin = input_nhwc.shape
    Hout = (H - kH) // stride + 1
    Wout = (W - kW) // stride + 1

    cols = np.zeros((Hout * Wout, kH * kW * Cin), dtype=input_nhwc.dtype)
    idx = 0
    for oh in range(Hout):
        for ow in range(Wout):
            patch = input_nhwc[0, oh*stride:oh*stride+kH, ow*stride:ow*stride+kW, :]
            cols[idx] = patch.reshape(-1)
            idx += 1
    return cols


def outer_product_matmul(A, B, tile_rows=16, tile_cols=16):
    """Simulate VME outer-product tiled matmul.

    For each k-slice, compute rank-1 update: C[r_tile, c_tile] += a_col @ b_row
    This matches the VME VOPACC_AVV instruction sequence.
    """
    M, K = A.shape
    K2, N = B.shape
    assert K == K2

    C = np.zeros((M, N), dtype=np.int32)
    num_ops = 0

    # Tile over output
    for r_start in range(0, M, tile_rows):
        r_end = min(r_start + tile_rows, M)
        for c_start in range(0, N, tile_cols):
            c_end = min(c_start + tile_cols, N)
            # Accumulate over K dimension
            for k in range(K):
                a_col = A[r_start:r_end, k].astype(np.int32)  # [tile_rows]
                b_row = B[k, c_start:c_end].astype(np.int32)  # [tile_cols]
                # Outer product accumulate
                C[r_start:r_end, c_start:c_end] += np.outer(a_col, b_row)
                num_ops += 1

    return C, num_ops


def generate_c_header(input_data, filter_data, output_data, im2col_A, filter_B):
    """Generate C header with test vectors."""
    lines = []
    lines.append("/* Auto-generated VME Conv2D golden test vectors */")
    lines.append(f"/* Input:  [1, 8, 8, 48] int8 */")
    lines.append(f"/* Filter: [48, 4, 4, 48] int8 */")
    lines.append(f"/* Output: [1, 5, 5, 48] int32 */")
    lines.append("")
    lines.append("#pragma once")
    lines.append("#include <stdint.h>")
    lines.append("")

    # Shapes
    lines.append("#define CONV2D_N 1")
    lines.append("#define CONV2D_H 8")
    lines.append("#define CONV2D_W 8")
    lines.append("#define CONV2D_CIN 48")
    lines.append("#define CONV2D_COUT 48")
    lines.append("#define CONV2D_KH 4")
    lines.append("#define CONV2D_KW 4")
    lines.append("#define CONV2D_HOUT 5")
    lines.append("#define CONV2D_WOUT 5")
    lines.append("#define CONV2D_M 25    /* Hout * Wout */")
    lines.append("#define CONV2D_K 768   /* kH * kW * Cin */")
    lines.append("")

    # Input data (flat, int8)
    flat_input = input_data.flatten()
    lines.append(f"static const int8_t conv2d_input[{len(flat_input)}] = {{")
    for i in range(0, len(flat_input), 16):
        chunk = flat_input[i:i+16]
        lines.append("    " + ", ".join(str(int(x)) for x in chunk) + ",")
    lines.append("};")
    lines.append("")

    # Filter data (flat, int8) — [Cout, kH, kW, Cin] layout
    flat_filter = filter_data.flatten()
    lines.append(f"static const int8_t conv2d_filter[{len(flat_filter)}] = {{")
    for i in range(0, len(flat_filter), 16):
        chunk = flat_filter[i:i+16]
        lines.append("    " + ", ".join(str(int(x)) for x in chunk) + ",")
    lines.append("};")
    lines.append("")

    # Expected output (flat, int32) — [1, Hout, Wout, Cout] layout
    flat_output = output_data.flatten()
    lines.append(f"static const int32_t conv2d_expected[{len(flat_output)}] = {{")
    for i in range(0, len(flat_output), 8):
        chunk = flat_output[i:i+8]
        lines.append("    " + ", ".join(str(int(x)) for x in chunk) + ",")
    lines.append("};")
    lines.append("")

    # im2col matrix A — first tile (16 rows, first 16 cols) for spot-check
    lines.append("/* First 16x16 tile of im2col matrix A (for VME tile verification) */")
    tile_A = im2col_A[:16, :16].astype(np.int8)
    lines.append(f"static const int8_t conv2d_im2col_tile[256] = {{")
    for i in range(16):
        row = tile_A[i]
        lines.append("    " + ", ".join(str(int(x)) for x in row) + ",")
    lines.append("};")
    lines.append("")

    # Filter matrix B — first tile (first 16 rows, first 16 cols)
    tile_B = filter_B[:16, :16].astype(np.int8)
    lines.append(f"static const int8_t conv2d_filter_tile[256] = {{")
    for i in range(16):
        row = tile_B[i]
        lines.append("    " + ", ".join(str(int(x)) for x in row) + ",")
    lines.append("};")

    return "\n".join(lines) + "\n"


def main():
    np.random.seed(42)  # Reproducible

    # Generate random int8 data
    input_data = np.random.randint(-128, 127, size=(1, 8, 8, 48), dtype=np.int8)
    filter_data = np.random.randint(-128, 127, size=(48, 4, 4, 48), dtype=np.int8)

    # Reference Conv2D
    print("Computing reference Conv2D [1,8,8,48] * [48,4,4,48] → [1,5,5,48]...")
    output_ref = conv2d_nhwc_int8(input_data, filter_data)
    print(f"  Output range: [{output_ref.min()}, {output_ref.max()}]")
    print(f"  Output shape: {output_ref.shape}")

    # im2col + outer-product verification
    kH, kW, Cin = 4, 4, 48
    A = im2col(input_data, kH, kW)  # [25, 768]
    B = filter_data.reshape(48, -1).T  # [768, 48]
    print(f"  im2col A shape: {A.shape}")
    print(f"  filter B shape: {B.shape}")

    C_tiled, num_ops = outer_product_matmul(A, B, tile_rows=16, tile_cols=16)
    output_tiled = C_tiled.reshape(1, 5, 5, 48)

    # Verify equivalence
    assert np.array_equal(output_ref, output_tiled), "Tiled outer-product result mismatch!"
    print(f"  Tiled outer-product matches reference ({num_ops} VOPACC_AVV ops)")

    # Generate C header
    header = generate_c_header(input_data, filter_data, output_ref, A, B)
    out_path = Path(__file__).parent.parent / "testbench" / "tests" / "conv2d_golden.h"
    out_path.write_text(header)
    print(f"  Written golden vectors to {out_path}")

    # Summary stats
    print(f"\nVME Conv2D Summary:")
    print(f"  Input:  [1, 8, 8, 48] = {input_data.size} int8 values")
    print(f"  Filter: [48, 4, 4, 48] = {filter_data.size} int8 values")
    print(f"  Output: [1, 5, 5, 48] = {output_ref.size} int32 values")
    print(f"  im2col: [{A.shape[0]}, {A.shape[1]}] @ [{B.shape[0]}, {B.shape[1]}]")
    print(f"  Tile size: 16×16 (VLEN=128, int8)")
    print(f"  Row tiles: {(A.shape[0] + 15) // 16}")
    print(f"  Col tiles: {(B.shape[1] + 15) // 16}")
    print(f"  K tiles:   {A.shape[1]}")
    print(f"  Total VOPACC_AVV: {num_ops}")


if __name__ == "__main__":
    main()
