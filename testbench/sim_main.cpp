//==============================================================================
// sim_main.cpp - Verilator testbench for Shoumei CPU
//
// Drives the tb_cpu wrapper:
//   1. Loads a flat binary or hex file into memory
//   2. Runs clock cycles until tohost is written or timeout
//   3. Reports PASS/FAIL with cycle count
//
// Build (after Verilating):
//   make -C testbench sim
//
// Run:
//   ./build-sim/sim_shoumei [+hex=path/to/program.hex] [+timeout=N] [+trace]
//==============================================================================

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <memory>

#include "Vtb_cpu.h"
#include "Vtb_cpu_tb_cpu.h"
#include "verilated.h"

#if VM_TRACE
#include "verilated_vcd_c.h"
#endif

static const uint32_t DEFAULT_TIMEOUT = 100000;

// Parse +arg=value from command line
static const char* get_plusarg(int argc, char** argv, const char* name) {
    size_t len = strlen(name);
    for (int i = 1; i < argc; i++) {
        if (strncmp(argv[i], name, len) == 0 && argv[i][len] == '=') {
            return argv[i] + len + 1;
        }
    }
    return nullptr;
}

static bool has_plusarg(int argc, char** argv, const char* name) {
    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], name) == 0) return true;
    }
    return false;
}

// Load hex file into simulated memory via verilator public access
// Format: one 32-bit hex word per line, starting at address 0
static int load_hex(Vtb_cpu* dut, const char* path) {
    FILE* f = fopen(path, "r");
    if (!f) {
        fprintf(stderr, "ERROR: Cannot open hex file: %s\n", path);
        return -1;
    }

    char line[256];
    int addr = 0;
    while (fgets(line, sizeof(line), f)) {
        // Skip comments and blank lines
        if (line[0] == '/' || line[0] == '#' || line[0] == '\n') continue;

        uint32_t word;
        if (sscanf(line, "%x", &word) == 1) {
            dut->tb_cpu->mem[addr] = word;
            addr++;
        }
    }

    fclose(f);
    printf("Loaded %d words from %s\n", addr, path);
    return addr;
}

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);

    auto dut = std::make_unique<Vtb_cpu>();

    // Parse arguments
    const char* hex_path = get_plusarg(argc, argv, "+hex");
    const char* timeout_str = get_plusarg(argc, argv, "+timeout");
    bool do_trace = has_plusarg(argc, argv, "+trace");
    bool verbose = has_plusarg(argc, argv, "+verbose");

    uint32_t timeout = timeout_str ? atoi(timeout_str) : DEFAULT_TIMEOUT;

#if VM_TRACE
    VerilatedVcdC* trace = nullptr;
    if (do_trace) {
        Verilated::traceEverOn(true);
        trace = new VerilatedVcdC;
        dut->trace(trace, 99);
        trace->open("shoumei_cpu.vcd");
        printf("VCD trace enabled: shoumei_cpu.vcd\n");
    }
#else
    (void)do_trace;
#endif

    // Load program
    if (hex_path) {
        if (load_hex(dut.get(), hex_path) < 0) {
            return 1;
        }
    } else {
        // Default: tiny test program
        printf("No +hex file specified, loading built-in test program\n");
        // Test: write 1 to tohost (0x1000) → PASS
        // NOPs needed: src_ready is hardwired, so operands must be in PRF
        // before the SW issues. Each NOP burns one pipeline slot.
        dut->tb_cpu->mem[0] = 0x00100213;  // addi x4, x0, 1
        dut->tb_cpu->mem[1] = 0x000012b7;  // lui  x5, 1        (x5 = 0x1000)
        dut->tb_cpu->mem[2] = 0x00000013;  // nop
        dut->tb_cpu->mem[3] = 0x00000013;  // nop
        dut->tb_cpu->mem[4] = 0x00000013;  // nop
        dut->tb_cpu->mem[5] = 0x00000013;  // nop
        dut->tb_cpu->mem[6] = 0x0042A023;  // sw   x4, 0(x5)    (tohost = 1 → PASS)
        dut->tb_cpu->mem[7] = 0x0000006f;  // jal  x0, 0         (spin forever)
    }

    // =====================================================================
    // Reset
    // =====================================================================
    dut->rst_n = 0;
    dut->clk = 0;
    for (int i = 0; i < 10; i++) {
        dut->clk = !dut->clk;
        dut->eval();
#if VM_TRACE
        if (trace) trace->dump(i);
#endif
    }
    dut->rst_n = 1;

    // =====================================================================
    // Main simulation loop
    // =====================================================================
    uint64_t sim_time = 10;
    uint32_t cycle = 0;
    bool done = false;

    printf("Simulation started (timeout=%u cycles)\n", timeout);
    printf("─────────────────────────────────────────────\n");

    while (!done && cycle < timeout && !Verilated::gotFinish()) {
        // Rising edge
        dut->clk = 1;
        dut->eval();
#if VM_TRACE
        if (trace) trace->dump(sim_time++);
#endif

        // Debug: print key signals for first 30 cycles if +verbose
        if (verbose && cycle < 30) {
            auto tb = dut->tb_cpu;
            printf("  [%4u] PC=0x%08x stall=%d rob_empty=%d",
                cycle, dut->o_fetch_pc, (int)dut->o_global_stall, (int)dut->o_rob_empty);
            if (tb->dmem_req_valid)
                printf(" DMEM: we=%d addr=0x%08x data=0x%08x",
                    (int)tb->dmem_req_we, tb->dmem_req_addr, tb->dmem_req_data);
            printf("\n");
        }

        // Check termination via public output ports
        if (dut->o_test_done) {
            done = true;
            if (dut->o_test_pass) {
                printf("\n══════ TEST PASS ══════\n");
            } else {
                printf("\n══════ TEST FAIL ══════\n");
                printf("  test_num:  %u\n", dut->o_test_code >> 1);
            }
            printf("  Cycle:     %u\n", cycle);
            printf("  PC:        0x%08x\n", dut->o_fetch_pc);
            printf("  tohost:    0x%08x\n", dut->o_test_code);
        }

        // Falling edge
        dut->clk = 0;
        dut->eval();
#if VM_TRACE
        if (trace) trace->dump(sim_time++);
#endif

        cycle++;

        // Progress indicator
        if (cycle % 10000 == 0) {
            printf("  [%u cycles] PC=0x%08x\n", cycle, dut->o_fetch_pc);
        }
    }

    if (!done) {
        printf("\n══════ TIMEOUT ══════\n");
        printf("  Cycle:     %u\n", cycle);
        printf("  PC:        0x%08x\n", dut->o_fetch_pc);
        printf("  rob_empty: %d\n", dut->o_rob_empty);
        printf("  stall:     %d\n", dut->o_global_stall);
    }

    printf("─────────────────────────────────────────────\n");
    printf("Total cycles: %u\n", cycle);

#if VM_TRACE
    if (trace) {
        trace->close();
        delete trace;
    }
#endif

    dut->final();
    return done && dut->o_test_pass ? 0 : 1;
}
