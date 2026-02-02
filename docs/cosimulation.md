# Cosimulation with Spike

Architecture and integration guide for cosimulating the Shoumei RTL against Spike, the canonical RISC-V ISA reference simulator.

## Overview

Cosimulation compares two executions of the same program:

1. **Spike** (golden model) -- produces a commit-level trace of every retired instruction
2. **RTL simulation** (design under test) -- produces a commit-level trace from the ROB retirement port

A mismatch at any retirement point is a bug in the RTL, the code generators, or the test infrastructure.

```
                    ELF binary
                   /          \
                  v            v
             Spike            RTL Sim
          (reference)         (DUT)
               |                |
               v                v
          golden.trace      dut.trace
               \              /
                v            v
              Trace Comparator
                    |
                    v
              PASS / FAIL
```

## Spike Configuration

### Invocation

```bash
spike --log-commits --isa=rv32im -m0x80000000:0x10000 test.elf 2> golden.trace
```

| Flag | Purpose |
|------|---------|
| `--log-commits` | Emit one line per retired instruction on stderr |
| `--isa=rv32im` | RV32I base + M extension (matches Shoumei config) |
| `-m0x80000000:0x10000` | Physical memory: 64KB at 0x80000000 |
| `--priv=m` | Stay in M-mode (optional, simplifies bare-metal tests) |

### Commit log format

Spike's `--log-commits` output:

```
core   0: 0x80000000 (0x00500093) x1  0x00000005
core   0: 0x80000004 (0x00a00113) x2  0x0000000a
core   0: 0x80000008 (0x002081b3) x3  0x0000000f
core   0: 0x8000000c (0x00312023) mem 0x80010000 0x0000000f
```

Fields: `core N: PC (encoding) writeback_reg value` for register writes, `mem addr data` for stores.

### Other useful Spike modes

| Mode | Flag | Use case |
|------|------|----------|
| Interactive debug | `-d` | Step through failures, set breakpoints |
| Full instruction log | `-l` | Verbose trace including fetched instructions |
| Signature dump | `+signature=sig.out` | riscv-arch-test compatible output |
| VCD trace | `--vcd=trace.vcd` | Waveform output for timing analysis |

## Trace Format

Both Spike and the RTL produce traces in a common normalized format:

```
# PC         ENCODING   WB_REG  WB_VALUE    MEM_OP
80000040   00500093   x01     00000005
80000044   00a00113   x02     0000000a
80000048   002081b3   x03     0000000f
8000004c   00312023   ---     ----------  ST 80002000 0000000f W
```

### Fields

| Field | Width | Description |
|-------|-------|-------------|
| PC | 8 hex chars | Program counter at retirement |
| ENCODING | 8 hex chars | Raw instruction encoding |
| WB_REG | `x00`-`x31` or `---` | Destination register (or none for stores/branches) |
| WB_VALUE | 8 hex chars or `----------` | Writeback value |
| MEM_OP | optional | `ST addr data W/H/B` for stores, `LD addr data W/H/B` for loads |

### Filtering

Generated ELFs include a metadata sidecar (`.meta` JSON) with symbol addresses:

```json
{
  "test_body": "0x80000040",
  "test_end": "0x80000120",
  "num_test_insns": 28,
  "pattern": "rawChain",
  "description": "RAW ADD->SUB distance=3"
}
```

The trace parser strips bootstrap instructions (before `test_body`) and termination code (after `test_end`), comparing only the test payload.

## RTL Trace Extraction

### From the ROB commit port

When an instruction retires from the ROB, the following fields are available from the `ROBEntry` structure:

```
Bit 0:      valid
Bit 1:      complete
Bits 2-7:   physRd (destination physical register)
Bit 8:      hasPhysRd
Bits 9-14:  oldPhysRd (previous mapping)
Bit 15:     hasOldPhysRd
Bits 16-20: archRd (architectural destination)
Bit 21:     exception
Bit 22:     isBranch
Bit 23:     branchMispredicted
```

At each ROB commit:
1. Read `archRd` (bits [16:20]) for the destination register name
2. Read the committed value from `PhysRegFile[physRd]` (bits [2:7])
3. Read `pc` from the ROB's PC tracking (or a separate PC queue)
4. Log as: `PC ENCODING archRd value`

### SystemC testbench

The SystemC code generator already produces models for all pipeline components. The cosimulation testbench:

1. Loads the ELF `.text` section into instruction memory
2. Loads the ELF `.data` section into data memory
3. Asserts reset for N cycles, then releases
4. On each clock edge, checks the ROB commit port
5. When commit fires, logs the trace line
6. Terminates when `tohost` is written (HTIF convention)

```cpp
// Pseudocode for SystemC testbench commit monitor
void monitor() {
    if (rob_commit_valid.read()) {
        uint32_t pc = rob_commit_pc.read();
        uint32_t encoding = imem[pc >> 2];
        uint32_t arch_rd = rob_commit_arch_rd.read();
        uint32_t value = rob_commit_value.read();
        trace_file << hex(pc) << " " << hex(encoding)
                   << " x" << dec(arch_rd) << " " << hex(value) << "\n";
    }
}
```

### Verilator alternative

For faster simulation, Verilator compiles the generated SystemVerilog directly:

```bash
verilator --cc --exe --build \
  -Ioutput/sv-from-lean \
  output/sv-from-lean/ShoumeiCPU.sv \
  testbench/cosim_tb.cpp \
  -o build/shoumei_sim
```

The testbench structure is identical -- monitor the ROB commit port and log traces.

## Trace Comparison

### Basic diff

```bash
spike --log-commits --isa=rv32im test.elf 2>&1 \
  | python3 scripts/parse_spike_trace.py --meta test.meta > golden.trace

./build/shoumei_sim +binary=test.elf +trace=dut.trace

python3 scripts/compare_traces.py golden.trace dut.trace
```

### Comparison algorithm

The comparator aligns traces by PC and instruction index (not cycle count -- the RTL is out-of-order, so cycle alignment is meaningless). The comparison is at retirement boundaries only:

1. Read one entry from each trace
2. Compare PC -- must match (instructions retire in program order from the ROB)
3. Compare encoding -- must match (same instruction)
4. Compare writeback register and value -- must match
5. Compare memory operations if present -- address, data, and width must match
6. On first mismatch, report with context

### Mismatch report format

```
MISMATCH at instruction #17:
  PC:       0x80000058
  Encoding: 0x002081b3 (ADD x3, x1, x2)

  Spike:    x03 = 0x0000000f
  DUT:      x03 = 0x00000010

  Test:     rawChain ADD->SUB distance=2
  Context:  This is a RAW hazard test. x1 was written 2 instructions
            ago. Possible CDB forwarding or register file read bug.

Previous 3 instructions:
  #14: 80000048 00500093 x01 00000005  (ADDI x1, x0, 5)
  #15: 8000004c 00000013 ---           (NOP)
  #16: 80000050 00000013 ---           (NOP)
```

### Handling out-of-order retirement

The Tomasulo ROB guarantees in-order retirement even though execution is out-of-order. The commit trace from the RTL should be in strict program order. If the RTL trace is out of order relative to Spike, that itself is a bug (ROB commit logic is broken).

## Synchronization

The RTL is an out-of-order pipeline; Spike is a simple in-order stepper. They must agree at retirement boundaries, not at execution time.

### Implicit sync: program order retirement

Because the ROB commits in program order, every committed instruction is a natural sync point. The trace comparison works instruction-by-instruction without explicit barriers.

### Explicit sync: FENCE as drain point

For tests that need the pipeline to fully drain (e.g., before checking memory state):

```asm
FENCE       # All prior loads/stores complete
            # Store buffer is empty after this point
```

After a FENCE, the store buffer and load queue are empty, and all prior instructions have committed. This is useful for memory-ordering tests where you want to check memory contents at a known quiescent point.

## CI Integration

```yaml
# .github/workflows/cosim.yml
name: Cosimulation
on: [push, pull_request]

jobs:
  cosim:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - name: Install Spike
        run: |
          git clone https://github.com/riscv-software-src/riscv-isa-sim.git
          cd riscv-isa-sim
          mkdir build && cd build
          ../configure --prefix=/opt/spike
          make -j$(nproc) && sudo make install
          echo "/opt/spike/bin" >> $GITHUB_PATH

      - name: Build Lean + generate tests
        run: |
          lake build
          lake exe generate_tests --suite all --output tests/generated/

      - name: Run cosimulation
        run: |
          scripts/run_cosim.sh tests/generated/
          # Exits non-zero on any mismatch
```

### `run_cosim.sh` structure

```bash
#!/usr/bin/env bash
set -euo pipefail

TEST_DIR="${1:?Usage: run_cosim.sh <test_dir>}"
PASS=0
FAIL=0

for elf in "$TEST_DIR"/*.elf; do
    meta="${elf%.elf}.meta"
    name=$(basename "$elf" .elf)

    # Golden trace from Spike
    spike --log-commits --isa=rv32im "$elf" 2>&1 \
      | python3 scripts/parse_spike_trace.py --meta "$meta" > "/tmp/${name}.golden"

    # DUT trace from RTL simulation
    ./build/shoumei_sim "$elf" > "/tmp/${name}.dut"

    # Compare
    if python3 scripts/compare_traces.py "/tmp/${name}.golden" "/tmp/${name}.dut"; then
        echo "PASS: $name"
        PASS=$((PASS + 1))
    else
        echo "FAIL: $name"
        FAIL=$((FAIL + 1))
    fi
done

echo "Results: $PASS passed, $FAIL failed out of $((PASS + FAIL)) tests"
[ "$FAIL" -eq 0 ]
```

## Debugging Failures

### Step 1: Identify the divergence

The comparator output tells you the PC, instruction, and expected vs actual values.

### Step 2: Disassemble the ELF

```bash
riscv32-unknown-elf-objdump -d test.elf
```

Locate the failing instruction in the disassembly. The symbol table shows `test_body`, `test_end`, and the test description.

### Step 3: Run Spike interactively

```bash
spike -d --isa=rv32im test.elf
: until pc 0 0x80000058    # Run to the failing PC
: reg 0                     # Dump all registers
: mem 0 0x80002000 16       # Dump memory
```

### Step 4: Check the RTL waveform

If using Verilator with `--trace`:

```bash
./build/shoumei_sim +binary=test.elf +vcd=dump.vcd
gtkwave dump.vcd
```

Look at the ROB commit signals around the failing instruction. Check whether the CDB broadcast, register file write, or store buffer forwarding is incorrect.

### Step 5: Cross-reference with Lean model

If the bug is in the microarchitectural logic, the Lean behavioral models can help pinpoint which component is at fault. Run the Lean microarchitectural simulator on the same program and check which pipeline stage produces the wrong value.

## Comparison with Other Approaches

| | riscv-dv | Directed tests | Formal (BMC) | Shoumei (Lean + Spike) |
|---|---|---|---|---|
| Microarch-aware generation | No | Manual | N/A | Yes (Lean models) |
| Trusted oracle | Spike | Spike | Self-referential | Spike |
| Coverage model | Instruction-level | Ad hoc | State space | Microarchitectural |
| Reusable regression suite | Yes | Yes | No | Yes |
| Provable encoder correctness | No | No | No | Yes (Lean proof) |
| Effort to add new patterns | Config files | Manual assembly | New properties | Lean functions |
