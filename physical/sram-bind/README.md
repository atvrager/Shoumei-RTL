# SRAM binding layer

Per-process memories that satisfy the contracts the RTL declares.  The RTL
names a *shape and a contract*; nothing above this directory knows whether the
macro came from OpenRAM, a PDK vendor library, or a behavioural model.

## What the RTL asks for

Every cache data array is a `RAMPrimitive` (`lean/Shoumei/DSL.lean`) carrying a
`portKind`:

| `portKind` | contract | emitted module |
|---|---|---|
| `r1w1` | separate read and write addresses, asynchronous read | `sram_1r1w_<width>x<depth>` |
| `rw1ByteMask` | one address, registered read, per-byte write mask | `sram_rw1_<width>x<depth>` |

Port lists:

```systemverilog
module sram_1r1w_<w>x<d> (clk, we, waddr, wdata, raddr, rdata);
module sram_rw1_<w>x<d>  (clk, en, we, addr, wmask, wdata, rdata);
```

`rw1ByteMask` lands as a single-port macro: the address is `we ? waddr : raddr`,
which is sound exactly when the RTL never reads and writes the same array in the
same cycle (the single-port data-path invariant the caches hold).

## Layout

```
physical/sram-bind/<node>/     # the binding layer for a process node
  sram_<kind>_<w>x<d>.sv       # macro model (or a shim instantiating vendor macros)
  sram_<kind>_<w>x<d>.lib      # optional liberty (area/timing for synthesis)
  vendor/                      # optional: vendor cells this node's shims wrap
```

The physical flows consume the layer through:

```bash
SRAM_MACROS=1 SRAM_MACRO_LIB=physical/sram-bind/gf180 \
  ./physical/run-yosys-gf180.sh
```

`SRAM_MACRO_LIB` defaults to `third_party/sram-macros/<node>` (the OpenRAM
output of `make sram-macros`).  Requesting `SRAM_MACROS=1` with no library is a
**hard error**: a synthesis run that silently falls back to register arrays is
worse than no run at all.

## Generating a layer

```bash
make sram-macros                       # OpenRAM, per node, geometries taken from the emitted RTL
scripts/gen-sram-macros.sh --stub      # behavioural models (no OpenRAM needed): CI + flow smoke
```

Both write canonical module names, so the emitted RTL never changes.

## Process notes

- **GF180MCU**: the PDK ships exactly four SRAM cells
  (`gf180mcu_fd_ip_sram__sram{64,128,256,512}x8m8wm1`), all **8-bit wide and
  single-port**, with byte-wise write enables (`CLK/CEN/GWEN/WEN[7:0]/A/D/Q`).
  A wide line is therefore built from byte lanes: 64 B line = 64 macros per way,
  one `sram64x8m8wm1` per (way, byte lane).  The shim is what adapts the vendor
  pin names/polarity (`CEN`/`GWEN` active low) to the canonical contract.
- **ASAP7**: no vendor memory catalogue in the academic PDK; OpenRAM
  (`--pdk asap7`) provides the layer.
- **Simulation** never uses this directory: the emitted `ifdef` fallback is a
  plain `reg` array, which is what Verilator and cosim run against.