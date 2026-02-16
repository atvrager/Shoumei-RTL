# Lock-Step Cosimulation via RVVI

Architecture and integration guide for three-way lock-step cosimulation of the Shoumei RTL, the Lean-generated SystemC model, and Spike, driven by the RVVI (RISC-V Verification Interface) trace port.

## Overview

Three independently generated implementations execute the same ELF and are compared at every retirement point:

1. **RTL** (Verilator) -- generated SystemVerilog, the primary DUT
2. **SystemC** (Lean codegen) -- generated `SC_MODULE`, a second DUT
3. **Spike** (libriscv) -- canonical ISA reference, the oracle

```
                              ELF binary
                                  |
                +--------+--------+--------+
                |        |                 |
                v        v                 v
          RTL (Verilator)  SystemC       Spike
          (SV from Lean)   (SC from Lean) (libriscv)
                |            |             |
                |  RVVI      |  step()     |  step()
                |  valid     |             |
                +-----+------+------+------+
                      |             |
                      v             v
                 3-way compare (per retirement)
                      |
                 PASS / FAIL + fault isolation
```

When the RTL retires an instruction (RVVI `valid` asserted), the testbench:
1. Reads the RVVI signals from the RTL
2. Steps the SystemC model one instruction and reads its state
3. Steps Spike one instruction and reads its state
4. Compares all three

All three are linked into the same Verilator testbench process. No trace files, no offline comparison -- mismatches are caught at the exact cycle they occur.

### Why three-way?

Two-way (RTL vs Spike) catches bugs but can't isolate their source. Three-way comparison with the SystemC model adds fault isolation:

| RTL | SystemC | Spike | Diagnosis |
|:---:|:---:|:---:|---|
| ok | ok | ok | All agree -- no bug |
| **wrong** | ok | ok | Bug in SystemVerilog code generator |
| ok | **wrong** | ok | Bug in SystemC code generator |
| **wrong** | **wrong** | ok | Bug in Lean circuit definition (both generators faithfully reproduce it) |
| ok | ok | **wrong** | Spike bug or ISA spec ambiguity (rare) |

The third column is the key insight. When RTL and SystemC agree with each other but both disagree with Spike, the Lean circuit definition itself is wrong -- not a code generator issue. This is the same principle as LEC (which checks Lean SV vs Chisel SV at the gate level), but operating at simulation time on actual programs.

### Relationship to LEC

LEC proves that Lean SV and Chisel SV are equivalent for all inputs. Three-way cosimulation proves that Lean SV, Lean SystemC, and Spike agree on specific test programs. These are complementary:

- **LEC** catches structural divergence between code generators (complete but only between two generators)
- **Three-way cosim** catches behavioral bugs in the Lean model itself (incomplete but covers all three implementations)
- Together they form a closed verification triangle: Lean proofs establish correctness, LEC verifies code generators, cosim validates against the ISA reference

## RVVI-TRACE Interface

The RVVI-TRACE interface is a set of output-only signals from the RTL, sampled on the positive clock edge. It reports retirement and trap events along with all architectural state changes.

### Parameters derived from Lean model

RVVI-TRACE parameters are not hardcoded -- they are derived from the Lean CPU definition at code generation time. The Lean model is the single source of truth for the microarchitecture, and the RVVI interface must be consistent with it.

| RVVI parameter | Lean source | Current value | Notes |
|----------------|-------------|:---:|-------|
| `XLEN` | `CPUConfig` (RV32 implied) | 32 | Would be 64 for RV64 |
| `ILEN` | `CPUConfig.enableC` | 32 | 16 if compressed extension enabled |
| `NRET` | ROB commit width | 1 | Number of entries the ROB can commit per cycle |
| `NHART` | (not yet in config) | 1 | Single-hart for now |

The code generator reads these from the Lean model and emits the parameterized RVVI interface:

```lean
-- In lean/Shoumei/RISCV/Config.lean (proposed additions)

structure CPUConfig where
  -- ... existing fields ...
  /-- XLEN: register width (32 or 64) -/
  xlen : Nat := 32
  /-- Maximum instructions retired per cycle (ROB commit width) -/
  commitWidth : Nat := 1
  /-- Number of harts -/
  numHarts : Nat := 1

-- RVVI parameters derived from CPU config
structure RVVIConfig where
  xlen : Nat
  ilen : Nat
  nret : Nat
  nhart : Nat

def CPUConfig.rvviConfig (cfg : CPUConfig) : RVVIConfig :=
  { xlen  := cfg.xlen
    ilen  := if cfg.enableC then 16 else 32
    nret  := cfg.commitWidth
    nhart := cfg.numHarts }
```

The SystemVerilog code generator uses `RVVIConfig` to emit the interface with correct widths. If someone later widens the ROB commit port to retire 2 instructions per cycle, the RVVI interface updates automatically -- no manual sync required.

### Signal definitions

RVVI-TRACE, parameterized by the Lean model (current: RV32IM, single-hart, NRET=1):

```systemverilog
interface rvvi_trace #(
    parameter int ILEN  = 32,    // from CPUConfig: 16 if C ext, else 32
    parameter int XLEN  = 32,    // from CPUConfig.xlen
    parameter int NRET  = 1,     // from CPUConfig.commitWidth
    parameter int NHART = 1      // from CPUConfig.numHarts
);
    // Retirement event (active on posedge clk)
    logic                valid  [0:NHART-1][0:NRET-1];
    logic [63:0]         order  [0:NHART-1][0:NRET-1];
    logic [ILEN-1:0]     insn   [0:NHART-1][0:NRET-1];
    logic                trap   [0:NHART-1][0:NRET-1];
    logic                halt   [0:NHART-1][0:NRET-1];
    logic                intr   [0:NHART-1][0:NRET-1];

    // Privilege & mode
    logic [1:0]          mode   [0:NHART-1][0:NRET-1];
    logic [1:0]          ixl    [0:NHART-1][0:NRET-1];

    // Program counter
    logic [XLEN-1:0]     pc_rdata  [0:NHART-1][0:NRET-1];
    logic [XLEN-1:0]     pc_wdata  [0:NHART-1][0:NRET-1];

    // Integer register writeback
    logic [31:0]         x_wb      [0:NHART-1][0:NRET-1];
    logic [XLEN-1:0]     x_wdata   [0:NHART-1][0:NRET-1][0:31];

    // Memory access
    logic [XLEN-1:0]     mem_addr  [0:NHART-1][0:NRET-1];
    logic [XLEN/8-1:0]   mem_rmask [0:NHART-1][0:NRET-1];
    logic [XLEN/8-1:0]   mem_wmask [0:NHART-1][0:NRET-1];
    logic [XLEN-1:0]     mem_rdata [0:NHART-1][0:NRET-1];
    logic [XLEN-1:0]     mem_wdata [0:NHART-1][0:NRET-1];

endinterface
```

For the current Shoumei config (`NHART=1, NRET=1`), the `[0:0][0:0]` array dimensions collapse to scalar signals. The code generator handles this: when `commitWidth = 1` and `numHarts = 1`, it emits flat signals without array indexing for cleaner RTL.

### Signal semantics

**Retirement event:** When `valid` is high and `trap` is low, exactly one instruction has retired. The testbench reads all other signals and steps Spike.

**Trap event:** When `valid` is high and `trap` is high, an instruction trapped (ECALL, EBREAK, illegal instruction, misaligned access). The instruction did not retire. Spike must also be stepped to the same trap so that CSR state (mepc, mcause, mtval) stays in sync.

**Register writeback:** `x_wb` is a bitmask. If bit N is set, register xN was written with `x_wdata[N]`. For instructions that don't write a register (branches, stores), `x_wb` is zero. Writes to x0 must report `x_wdata[0] = 0`.

**Memory access:** `mem_wmask` indicates which bytes were written. For a `SW`, `mem_wmask = 4'b1111`. For `SH`, `mem_wmask = 4'b0011` or `4'b1100` depending on alignment. `mem_rmask` is analogous for loads.

**Ordering:** `order` is a 64-bit monotonically increasing counter. It increments on every `valid` event (both retirements and traps). The ROB guarantees in-order commit, so the order field should match Spike's instruction count.

### Mapping from ROBEntry to RVVI signals

The existing `ROBEntry` structure (24 bits) provides most RVVI fields. Two additions are needed: a PC queue and an instruction word queue, piggybacked on ROB allocation.

```
RVVI signal        Source                                  Notes
──────────────     ──────────────────────────────────      ─────
valid              ROB head: valid && complete             commit fires
order              64-bit counter, increments on valid
insn               insn_queue[rob_head]                    NEW: store at alloc time
trap               ROB head: exception [21]
halt               tohost write detected
intr               first insn after trap (derived)
mode               2'b11 (M-mode only, for now)
ixl                2'b01 (XLEN=32)
pc_rdata           pc_queue[rob_head]                      NEW: store at alloc time
pc_wdata           pc_queue[rob_head+1] or branch target
x_wb               1 << archRd [16:20] (if hasPhysRd)
x_wdata[archRd]    PhysRegFile[physRd] [2:7]
mem_addr           store_buffer commit: address [2:33]
mem_wdata           store_buffer commit: data [34:65]
mem_wmask          derived from store_buffer: size [66:67]
```

**New state required:**
- **PC queue:** `XLEN` bits per ROB entry. Written at allocation from the fetch stage PC. Read at commit for `pc_rdata`.
- **Instruction word queue:** `ILEN` bits per ROB entry. Written at allocation from instruction memory. Read at commit for `insn`.

Both are simple register files indexed by ROB slot, allocated and freed in lockstep with the ROB.

## Spike Integration

### Linking Spike as a library

Spike (riscv-isa-sim) builds `libriscv.so` / `libriscv.a` which exposes the processor model as a C++ library. The testbench links against it directly.

```bash
# Build Spike with shared library
cd riscv-isa-sim
mkdir build && cd build
../configure --prefix=/opt/spike --enable-commitlog
make -j$(nproc) && make install

# Link into Verilator testbench
SPIKE_INC=/opt/spike/include
SPIKE_LIB=/opt/spike/lib
verilator --cc --exe --build \
  -CFLAGS "-I${SPIKE_INC}" \
  -LDFLAGS "-L${SPIKE_LIB} -lriscv -lsoftfloat -ldisasm" \
  output/sv-from-lean/ShoumeiCPU.sv \
  testbench/cosim_tb.cpp \
  -o build/shoumei_cosim
```

### Spike stepping API

```cpp
#include <riscv/sim.h>
#include <riscv/processor.h>

class SpikeOracle {
    std::unique_ptr<sim_t> sim;
    processor_t* proc;

public:
    SpikeOracle(const char* elf_path) {
        // Configure: RV32IM, single hart, M-mode, memory at 0x80000000
        cfg_t cfg;
        cfg.isa = "rv32im";
        cfg.priv = "m";
        std::vector<mem_cfg_t> mem_cfg = {{0x80000000, 0x10000}};

        sim = std::make_unique<sim_t>(
            &cfg, false, mem_cfg,
            std::vector<std::string>{elf_path},
            /*dtb=*/nullptr, /*log_path=*/nullptr,
            /*htif_args=*/std::vector<std::string>{});
        proc = sim->get_core(0);
    }

    // Step one instruction, return state for comparison
    struct StepResult {
        uint32_t pc;
        uint32_t insn;
        uint32_t rd;         // destination register (0 if none)
        uint32_t rd_value;   // written value
        bool     trap;
        bool     mem_write;
        uint32_t mem_addr;
        uint32_t mem_data;
    };

    StepResult step() {
        StepResult r = {};
        r.pc = proc->get_state()->pc;

        // Capture pre-step register file
        uint32_t regs_before[32];
        for (int i = 0; i < 32; i++)
            regs_before[i] = proc->get_state()->XPR[i];

        // Step one instruction
        proc->step(1);

        // Detect which register changed
        for (int i = 1; i < 32; i++) {
            uint32_t val = proc->get_state()->XPR[i];
            if (val != regs_before[i]) {
                r.rd = i;
                r.rd_value = val;
                break;
            }
        }

        return r;
    }

    uint32_t get_pc() { return proc->get_state()->pc; }
    uint32_t get_xreg(int i) { return proc->get_state()->XPR[i]; }
};
```

## SystemC Integration

The SystemC model is generated from the same Lean circuit definitions as the SystemVerilog, via `Codegen/SystemC.lean`. It produces `SC_MODULE` classes with `SC_METHOD` (combinational) and `SC_CTHREAD` (sequential) processes. Since SystemC is C++, it links directly into the Verilator testbench.

### SystemC oracle wrapper

```cpp
#include "ShoumeiCPU.h"  // Generated SC_MODULE

class SystemCOracle {
    ShoumeiCPU sc_cpu{"sc_cpu"};
    sc_signal<bool> sc_clock, sc_reset;
    // ... sc_signals for all ports ...

public:
    SystemCOracle(const char* elf_path) {
        // Bind signals to SC_MODULE ports
        sc_cpu.clock(sc_clock);
        sc_cpu.reset(sc_reset);
        // ... bind all ports ...

        // Load ELF into SystemC model's memory
        load_elf_into_systemc(elf_path, &sc_cpu);

        // Reset sequence
        sc_reset = true;
        for (int i = 0; i < 10; i++) cycle();
        sc_reset = false;
    }

    void cycle() {
        sc_clock = false; sc_start(5, SC_NS);
        sc_clock = true;  sc_start(5, SC_NS);
    }

    struct StepResult {
        uint32_t pc;
        uint32_t rd;
        uint32_t rd_value;
        bool     trap;
        bool     mem_write;
        uint32_t mem_addr;
        uint32_t mem_data;
    };

    // Step until the SystemC model retires an instruction
    // (monitor its commit port, analogous to RVVI valid)
    StepResult step_until_retire() {
        StepResult r = {};
        while (!sc_cpu.commit_valid.read()) {
            cycle();
        }
        r.pc       = sc_cpu.commit_pc.read();
        r.rd       = sc_cpu.commit_rd.read();
        r.rd_value = sc_cpu.commit_rd_value.read();
        r.trap     = sc_cpu.commit_trap.read();
        cycle();  // advance past the commit event
        return r;
    }
};
```

The SystemC model runs cycle-by-cycle in its own simulated time. The testbench steps it until it retires an instruction, then compares against both the RTL's RVVI output and Spike's state.

**Timing independence:** The RTL and SystemC models may take different numbers of cycles to retire the same instruction (different microarchitectural optimizations in the code generators, different gate-level vs behavioral timing). The comparison is at the retirement boundary, not cycle-aligned. The `order` field (RVVI retirement counter) ensures the same logical instruction is being compared.

### Lock-step three-way comparison loop

The core of the testbench: on every RVVI retirement event, step both Spike and SystemC and compare all three.

```cpp
class CosimChecker {
    SpikeOracle spike;
    SystemCOracle systemc;
    uint64_t insn_count = 0;
    uint64_t mismatch_count = 0;

public:
    CosimChecker(const char* elf)
        : spike(elf), systemc(elf) {}

    // Called every clock posedge when RVVI valid is asserted
    void on_rvvi_valid(const RVVISignals& rvvi) {
        insn_count++;

        // Step Spike
        auto spike_result = spike.step();

        // Step SystemC model until it retires
        auto sc_result = systemc.step_until_retire();

        // Three-way comparison
        bool rtl_ok   = compare(rvvi, spike_result);
        bool sc_ok    = compare(sc_result, spike_result);
        bool rtl_sc   = compare(rvvi, sc_result);

        if (rtl_ok && sc_ok) {
            return;  // All three agree
        }

        // Fault isolation
        if (!rtl_ok && sc_ok) {
            report("SystemVerilog codegen bug", rvvi, sc_result, spike_result);
        } else if (rtl_ok && !sc_ok) {
            report("SystemC codegen bug", rvvi, sc_result, spike_result);
        } else if (!rtl_ok && !sc_ok && rtl_sc) {
            report("Lean circuit definition bug (both DUTs agree, Spike disagrees)",
                   rvvi, sc_result, spike_result);
        } else {
            report("Multiple failures (all three disagree)",
                   rvvi, sc_result, spike_result);
        }
        mismatch_count++;
    }

private:
    bool compare(const auto& a, const auto& b) {
        return a.pc == b.pc && a.rd == b.rd && a.rd_value == b.rd_value;
    }

    void report(const char* diagnosis, const RVVISignals& rtl,
                const auto& sc, const auto& spike) {
        fprintf(stderr,
            "\n=== COSIM MISMATCH at instruction #%lu ===\n"
            "  Diagnosis: %s\n"
            "  PC:        RTL=0x%08x  SC=0x%08x  Spike=0x%08x\n"
            "  rd:        RTL=x%d       SC=x%d       Spike=x%d\n"
            "  rd_value:  RTL=0x%08x  SC=0x%08x  Spike=0x%08x\n",
            insn_count, diagnosis,
            rtl.pc_rdata, sc.pc, spike.pc,
            /* rd from rtl */ 0, sc.rd, spike.rd,
            /* value from rtl */ 0, sc.rd_value, spike.rd_value);
    }
};
```

### Testbench main loop

```cpp
int main(int argc, char** argv) {
    const char* elf_path = /* parse from args */;

    // Initialize RTL simulation (Verilator)
    VerilatedContext ctx;
    auto dut = std::make_unique<VShoumeiCPU>(&ctx);

    // Initialize three-way checker (Spike + SystemC, both linked in-process)
    CosimChecker checker(elf_path);

    // Load ELF into RTL instruction/data memory
    load_elf_into_rtl(elf_path, dut.get());

    // Reset
    dut->reset = 1;
    for (int i = 0; i < 10; i++) { dut->clock = !dut->clock; dut->eval(); }
    dut->reset = 0;

    // Run
    while (!done(dut.get())) {
        dut->clock = !dut->clock;
        dut->eval();

        // On positive edge, check RVVI
        if (dut->clock && dut->rvvi_valid) {
            RVVISignals rvvi = capture_rvvi(dut.get());

            if (rvvi.trap) {
                checker.on_rvvi_trap(rvvi);
            } else {
                checker.on_rvvi_valid(rvvi);
            }
        }
    }

    checker.report_summary();
    return checker.pass() ? 0 : 1;
}
```

### Two-way fallback

The SystemC leg is optional. The testbench supports a `--no-systemc` flag for faster runs when only RTL-vs-Spike checking is needed. The three-way mode is the default for CI; two-way is useful for interactive debugging where simulation speed matters.

## Trap Synchronization

Traps require special handling because the instruction does not retire.

When RVVI reports `valid=1, trap=1`:

1. **Step Spike** -- Spike will also trap on the same instruction
2. **Compare trap cause** -- Check `mcause` CSR matches (illegal instruction, misaligned access, ecall, ebreak)
3. **Compare mepc** -- The trapped PC must match
4. **Sync privilege state** -- Both Spike and RTL enter the trap handler

For Shoumei's current scope (M-mode only, no interrupts), traps are synchronous and deterministic. The only expected traps are:
- ECALL (used for HTIF termination)
- Illegal instruction (test for exception handling)
- Misaligned access (if the pipeline doesn't mask them)

### HTIF termination

The program writes to `tohost` to signal completion. The testbench watches for a store to the `tohost` address:

```cpp
if (rvvi.mem_wmask != 0 && rvvi.mem_addr == tohost_addr) {
    uint32_t code = rvvi.mem_wdata;
    if (code == 1) {
        printf("TEST PASS\n");
        done = true;
    } else {
        printf("TEST FAIL: test_num=%d\n", code >> 1);
        done = true;
    }
}
```

## Handling Asynchronous Events (Future)

When Shoumei adds interrupt support, the cosimulation must handle asynchronous events. This is where RVVI's design pays off over simpler interfaces.

**Problem:** An interrupt arrives between two instructions. The RTL takes the interrupt and vectors to the trap handler. Spike must be told about the interrupt so it follows the same path.

**RVVI solution:** The testbench observes the RTL's RVVI `intr` signal (first instruction of trap handler). Before stepping Spike, it injects the same interrupt:

```cpp
if (rvvi.intr) {
    // RTL took an interrupt -- inject it into Spike before stepping
    uint32_t cause = read_csr(dut, CSR_MCAUSE);
    spike.inject_interrupt(cause);
}
spike.step(1);
// Now both are in the trap handler, state should match
```

This is not needed for the current M-mode bare-metal scope but is the reason to adopt RVVI rather than a simpler ad-hoc interface. The migration path to interrupts, privilege modes, and multi-hart is built into the interface.

## RTL Implementation

### Adding the RVVI port to the CPU

The Lean circuit definition for the top-level CPU module adds the RVVI signals as outputs. These are driven from ROB commit logic and the new PC/instruction queues.

**New Lean structures for RVVI support:**

```lean
-- PC queue: stores fetch PC alongside each ROB entry
-- Written at ROB allocation, read at ROB commit
structure PCQueue (depth : Nat) where
  entries : Fin depth → UInt32
  -- Indexed by ROB slot, same alloc/dealloc as ROB

-- Instruction queue: stores encoding alongside each ROB entry
structure InsnQueue (depth : Nat) where
  entries : Fin depth → UInt32

-- RVVI output bundle (active at ROB commit)
structure RVVIOutput where
  valid     : Bool
  order     : UInt64
  insn      : UInt32
  trap      : Bool
  halt      : Bool
  intr      : Bool
  mode      : UInt2        -- 2'b11 for M-mode
  pc_rdata  : UInt32
  pc_wdata  : UInt32
  x_wb      : UInt32       -- bitmask
  x_wdata   : Fin 32 → UInt32
  mem_addr  : UInt32
  mem_wmask : UInt4
  mem_wdata : UInt32
```

**Wire budget:** The RVVI port adds approximately `NRET * (2*XLEN + ILEN + 32*XLEN + 64 + 8)` output bits to the top-level module. For the current config (NRET=1, XLEN=32, ILEN=32), that is ~1200 bits / ~250 wires. This is observation-only -- it does not affect the datapath or timing.

### Generating the RVVI SystemVerilog

The code generator reads `CPUConfig.rvviConfig` and emits the RVVI interface with correct parameterization. The generator also handles the scalar-vs-array distinction: when `NRET=1` and `NHART=1`, signals are emitted as plain wires rather than arrays for cleaner RTL and easier Verilator access.

For Verilator, the RVVI signals are accessible directly on the top-level module:

```cpp
RVVISignals capture_rvvi(VShoumeiCPU* dut) {
    RVVISignals r;
    r.valid     = dut->rvvi_valid;
    r.pc_rdata  = dut->rvvi_pc_rdata;
    r.insn      = dut->rvvi_insn;
    r.trap      = dut->rvvi_trap;
    r.x_wb      = dut->rvvi_x_wb;
    for (int i = 0; i < 32; i++)
        r.x_wdata[i] = dut->rvvi_x_wdata[i];
    r.mem_addr  = dut->rvvi_mem_addr;
    r.mem_wmask = dut->rvvi_mem_wmask;
    r.mem_wdata = dut->rvvi_mem_wdata;
    return r;
}
```

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

      - name: Install Spike (with library)
        run: |
          git clone https://github.com/riscv-software-src/riscv-isa-sim.git
          cd riscv-isa-sim && mkdir build && cd build
          ../configure --prefix=/opt/spike --enable-commitlog
          make -j$(nproc) && sudo make install
          echo "/opt/spike/lib" | sudo tee /etc/ld.so.conf.d/spike.conf
          sudo ldconfig
          echo "/opt/spike/bin" >> $GITHUB_PATH

      - name: Build Lean + generate test ELFs
        run: |
          lake build
          lake exe generate_tests --suite all --output tests/generated/

      - name: Build Verilator cosim testbench
        run: |
          make -C testbench cosim   # Verilates RTL + links Spike

      - name: Run lock-step cosimulation
        run: |
          for elf in tests/generated/*.elf; do
            echo "=== $(basename $elf) ==="
            ./build/shoumei_cosim "$elf" || exit 1
          done
```

## Debugging Failures

When the lock-step checker reports a mismatch, simulation stops at the exact failing cycle.

### Step 1: Read the mismatch report

```
=== COSIM MISMATCH at instruction #17 ===
  PC:       0x80000058
  Insn:     0x002081b3 (ADD x3, x1, x2)
  Field:    x_wdata[3]
  Spike:    0x0000000f
  RTL:      0x00000010
  Cycle:    42
```

### Step 2: Re-run with waveform

```bash
./build/shoumei_cosim +trace +elf=tests/generated/raw_chain_d2.elf
./scripts/fst_inspect shoumei_cpu.fst --list
```

Look at the RVVI signals and the internal pipeline state (CDB, RS entries, ROB) around cycle 42.

### Step 3: Interactive Spike for expected state

```bash
spike -d --isa=rv32im tests/generated/raw_chain_d2.elf
: until pc 0 0x80000058
: reg 0
: mem 0 0x80002000 16
```

### Step 4: Cross-reference with Lean model

Run the Lean microarchitectural simulator to trace which pipeline stage computed the wrong value. The Lean behavioral models for RS, ROB, rename, and store buffer can narrow it to a specific component.

### Step 5: Register file dump on mismatch

The testbench dumps the full register file from all three models at the point of mismatch:

```
Register file at mismatch (instruction #17):
  Reg   Spike       RTL         SystemC     Status
  x00   00000000    00000000    00000000    ok
  x01   00000005    00000005    00000005    ok
  x02   0000000a    0000000a    0000000a    ok
  x03   0000000f    00000010    00000010    RTL+SC wrong (Lean circuit bug)
  x04   00000000    00000000    00000000    ok
  ...
```

When RTL and SystemC agree with each other but both disagree with Spike (as in x03 above), the Lean circuit definition is at fault -- both code generators faithfully reproduced the same incorrect behavior.

## Comparison with Other Approaches

| | riscv-dv + Spike log | ImperasDV + RVVI | Shoumei (Lean + RVVI + Spike + SystemC) |
|---|---|---|---|
| Comparison mode | Offline trace diff | Lock-step (2-way) | Lock-step (3-way) |
| Microarch-aware generation | No | No | Yes (Lean models) |
| Fault isolation | No (1 DUT) | No (1 DUT) | Yes (RTL vs SystemC vs Spike) |
| Detection latency | Post-mortem | Immediate (cycle) | Immediate (cycle) |
| Async event handling | Manual | Built-in | Via RVVI `intr` signal |
| License | Open source | Commercial | Open source |
| Provable test encoder | No | No | Yes (Lean proof) |
| Trace interface | Ad-hoc | RVVI-TRACE | RVVI-TRACE |

## References

- [RVVI Specification (riscv-verification/RVVI)](https://github.com/riscv-verification/RVVI)
- [RVVI-TRACE Interface](https://github.com/riscv-verification/RVVI/tree/main/RVVI-TRACE)
- [Spike (riscv-isa-sim)](https://github.com/riscv-software-src/riscv-isa-sim)
- [OpenHW core-v-verif (RVVI usage example)](https://github.com/openhwgroup/core-v-verif)
- [Imperas RVVI Overview](https://www.imperas.com/index.php/articles/risc-v-verification-interface-rvvi-test-infrastructure-and-methodology-guidelines)
