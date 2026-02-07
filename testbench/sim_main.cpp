//==============================================================================
// sim_main.cpp - Verilator testbench for Shoumei CPU
//
// Drives the tb_cpu wrapper:
//   1. Loads an ELF binary into memory via DPI-C (PT_LOAD segments)
//   2. Runs clock cycles until tohost is written or timeout
//   3. Reports PASS/FAIL with cycle count
//
// Build (after Verilating):
//   make -C testbench sim
//
// Run:
//   ./build-sim/sim_shoumei +elf=path/to/program.elf [+timeout=N] [+trace]
//==============================================================================

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <memory>
#include <elf.h>

#include "Vtb_cpu.h"
#include "verilated.h"
#include "svdpi.h"

#if VM_TRACE
#include "verilated_vcd_c.h"
#endif

// DPI-C exported from tb_cpu.sv
extern "C" void dpi_mem_write(unsigned int word_addr, unsigned int data);

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

// Load ELF file into simulated memory via DPI-C
// Parses ELF32 PT_LOAD segments, calls dpi_mem_write() for each word
static int load_elf(const char* path) {
    FILE* f = fopen(path, "rb");
    if (!f) {
        fprintf(stderr, "ERROR: Cannot open ELF file: %s\n", path);
        return -1;
    }

    // Read ELF header
    Elf32_Ehdr ehdr;
    if (fread(&ehdr, sizeof(ehdr), 1, f) != 1) {
        fprintf(stderr, "ERROR: Cannot read ELF header: %s\n", path);
        fclose(f);
        return -1;
    }

    // Validate
    if (memcmp(ehdr.e_ident, ELFMAG, SELFMAG) != 0) {
        fprintf(stderr, "ERROR: Not an ELF file: %s\n", path);
        fclose(f);
        return -1;
    }
    if (ehdr.e_ident[EI_CLASS] != ELFCLASS32) {
        fprintf(stderr, "ERROR: Not a 32-bit ELF: %s\n", path);
        fclose(f);
        return -1;
    }
    if (ehdr.e_machine != EM_RISCV) {
        fprintf(stderr, "ERROR: Not a RISC-V ELF (e_machine=%u): %s\n", ehdr.e_machine, path);
        fclose(f);
        return -1;
    }

    // Read program headers and load PT_LOAD segments
    uint32_t total_bytes = 0;
    for (int i = 0; i < ehdr.e_phnum; i++) {
        Elf32_Phdr phdr;
        fseek(f, ehdr.e_phoff + i * ehdr.e_phentsize, SEEK_SET);
        if (fread(&phdr, sizeof(phdr), 1, f) != 1) {
            fprintf(stderr, "ERROR: Cannot read program header %d\n", i);
            fclose(f);
            return -1;
        }

        if (phdr.p_type != PT_LOAD) continue;
        if (phdr.p_memsz == 0) continue;

        uint32_t base_addr = phdr.p_paddr;
        uint32_t filesz = phdr.p_filesz;
        uint32_t memsz = phdr.p_memsz;

        // Zero-fill the entire region first (handles BSS)
        for (uint32_t off = 0; off < memsz; off += 4) {
            dpi_mem_write((base_addr + off) / 4, 0);
        }

        // Read file data
        if (filesz > 0) {
            fseek(f, phdr.p_offset, SEEK_SET);
            uint32_t words = (filesz + 3) / 4;
            for (uint32_t w = 0; w < words; w++) {
                uint32_t word = 0;
                uint32_t remaining = filesz - w * 4;
                uint32_t to_read = remaining < 4 ? remaining : 4;
                if (fread(&word, 1, to_read, f) != to_read) {
                    fprintf(stderr, "ERROR: Short read in segment %d\n", i);
                    fclose(f);
                    return -1;
                }
                dpi_mem_write((base_addr / 4) + w, word);
            }
        }

        printf("  PT_LOAD: paddr=0x%08x filesz=%u memsz=%u\n", base_addr, filesz, memsz);
        total_bytes += memsz;
    }

    fclose(f);
    printf("Loaded ELF %s (%u bytes total)\n", path, total_bytes);
    return (int)total_bytes;
}

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);

    auto dut = std::make_unique<Vtb_cpu>();

    // Parse arguments
    const char* elf_path = get_plusarg(argc, argv, "+elf");
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

    // Load program via DPI-C
    if (!elf_path) {
        fprintf(stderr, "ERROR: No ELF file specified. Use +elf=path/to/program.elf\n");
        return 1;
    }

    // Set DPI scope to tb_cpu so dpi_mem_write resolves to the right instance
    svSetScope(svGetScopeFromName("TOP.tb_cpu"));
    if (load_elf(elf_path) < 0) {
        return 1;
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
    #if VM_TRACE
    uint64_t sim_time = 10;
    #endif
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
            printf("  [%4u] PC=0x%08x stall=%d rob_empty=%d",
                cycle, dut->o_fetch_pc, (int)dut->o_global_stall, (int)dut->o_rob_empty);
            if (dut->o_dmem_req_valid)
                printf(" DMEM: we=%d addr=0x%08x data=0x%08x",
                    (int)dut->o_dmem_req_we, dut->o_dmem_req_addr, dut->o_dmem_req_data);
            printf("\n");
        }

        // Check termination via output ports
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
