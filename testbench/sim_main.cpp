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

// Disable stdout buffering so output appears immediately in non-TTY contexts
static struct _StdoutUnbuffer {
    _StdoutUnbuffer() { setvbuf(stdout, nullptr, _IONBF, 0); }
} _stdout_unbuffer;

// Top module can be overridden at compile time:
//   -DTOP_HEADER=\"Vtb_cpu_microcoded.h\" -DTOP_MODULE=Vtb_cpu_microcoded
//   -DTOP_SCOPE=\"TOP.tb_cpu_microcoded\"
#ifndef TOP_MODULE
#define TOP_MODULE Vtb_cpu
#endif
#ifndef TOP_HEADER
#define TOP_HEADER "Vtb_cpu.h"
#endif
#ifndef TOP_SCOPE
#define TOP_SCOPE "TOP.tb_cpu"
#endif

#include TOP_HEADER

#include "verilated.h"
#include "svdpi.h"
#include "lib/kanata_tracer.h"

#if VM_TRACE
#include "verilated_fst_c.h"
#endif

// DPI-C exported from tb_cpu.sv
extern "C" void dpi_mem_write(unsigned int word_addr, unsigned int data);
extern "C" void dpi_set_tohost_addr(unsigned int addr);
extern "C" void dpi_set_putchar_addr(unsigned int addr);

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

// Look up a symbol by name in the ELF file, returns address or -1 if not found
static int64_t elf_lookup_symbol(const char* path, const char* sym_name) {
    FILE* f = fopen(path, "rb");
    if (!f) return -1;

    Elf32_Ehdr ehdr;
    if (fread(&ehdr, sizeof(ehdr), 1, f) != 1) { fclose(f); return -1; }

    // Find .symtab and .strtab sections
    for (int i = 0; i < ehdr.e_shnum; i++) {
        Elf32_Shdr shdr;
        fseek(f, ehdr.e_shoff + i * ehdr.e_shentsize, SEEK_SET);
        if (fread(&shdr, sizeof(shdr), 1, f) != 1) continue;
        if (shdr.sh_type != SHT_SYMTAB) continue;

        // Read string table for this symtab
        Elf32_Shdr strhdr;
        fseek(f, ehdr.e_shoff + shdr.sh_link * ehdr.e_shentsize, SEEK_SET);
        if (fread(&strhdr, sizeof(strhdr), 1, f) != 1) continue;

        auto* strtab = new char[strhdr.sh_size];
        fseek(f, strhdr.sh_offset, SEEK_SET);
        if (fread(strtab, 1, strhdr.sh_size, f) != strhdr.sh_size) {
            delete[] strtab; continue;
        }

        // Search symbols
        int nsyms = shdr.sh_size / shdr.sh_entsize;
        for (int j = 0; j < nsyms; j++) {
            Elf32_Sym sym;
            fseek(f, shdr.sh_offset + j * shdr.sh_entsize, SEEK_SET);
            if (fread(&sym, sizeof(sym), 1, f) != 1) continue;
            if (sym.st_name < strhdr.sh_size &&
                strcmp(strtab + sym.st_name, sym_name) == 0) {
                delete[] strtab;
                fclose(f);
                return (int64_t)sym.st_value;
            }
        }
        delete[] strtab;
    }
    fclose(f);
    return -1;
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

    auto dut = std::make_unique<TOP_MODULE>();

    // Parse arguments
    const char* elf_path = get_plusarg(argc, argv, "+elf");
    const char* timeout_str = get_plusarg(argc, argv, "+timeout");
    const char* kanata_path = get_plusarg(argc, argv, "+kanata");
    bool do_trace = has_plusarg(argc, argv, "+trace");
    bool verbose = has_plusarg(argc, argv, "+verbose");

    uint32_t timeout = timeout_str ? atoi(timeout_str) : DEFAULT_TIMEOUT;

    // Kanata pipeline tracer
    std::unique_ptr<KanataTracer> kanata;
    if (kanata_path) {
        kanata = std::make_unique<KanataTracer>(kanata_path);
        if (!kanata->is_open()) {
            fprintf(stderr, "ERROR: Cannot open Kanata trace file: %s\n", kanata_path);
            return 1;
        }
        printf("Kanata trace enabled: %s\n", kanata_path);
    }

#if VM_TRACE
    VerilatedFstC* trace = nullptr;
    if (do_trace) {
        Verilated::traceEverOn(true);
        trace = new VerilatedFstC;
        dut->trace(trace, 99);
        trace->open("shoumei_cpu.fst");
        printf("FST trace enabled: shoumei_cpu.fst\n");
    }
#else
    (void)do_trace;
#endif

    // Load program via DPI-C
    if (!elf_path) {
        fprintf(stderr, "ERROR: No ELF file specified. Use +elf=path/to/program.elf\n");
        return 1;
    }

    // Set DPI scope to the testbench top so dpi_mem_write resolves correctly
    svSetScope(svGetScopeFromName(TOP_SCOPE));
    if (load_elf(elf_path) < 0) {
        return 1;
    }

    // Look up HTIF addresses from ELF symbols (applied after reset below)
    int64_t tohost_sym = elf_lookup_symbol(elf_path, "tohost");
    if (tohost_sym >= 0) {
        printf("ELF symbol: tohost = 0x%08x\n", (uint32_t)tohost_sym);
    }
    int64_t putchar_sym = elf_lookup_symbol(elf_path, "putchar_addr");
    if (putchar_sym >= 0) {
        printf("ELF symbol: putchar_addr = 0x%08x\n", (uint32_t)putchar_sym);
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

    // Override HTIF addresses AFTER reset (initial blocks have run)
    if (tohost_sym >= 0) {
        dpi_set_tohost_addr((uint32_t)tohost_sym);
    }
    if (putchar_sym >= 0) {
        dpi_set_putchar_addr((uint32_t)putchar_sym);
    }

    // =====================================================================
    // Main simulation loop
    // =====================================================================
    #if VM_TRACE
    uint64_t sim_time = 10;
    #endif
    uint32_t cycle = 0;
    uint32_t retired = 0;
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

        // Count retired instructions
        if (dut->o_rvvi_valid) {
            retired++;
            if (verbose)
                printf("  RET[%u] PC=0x%08x insn=0x%08x rd=x%u(%d) data=0x%08x\n",
                    retired, dut->o_rvvi_pc_rdata, dut->o_rvvi_insn,
                    dut->o_rvvi_rd, (int)dut->o_rvvi_rd_valid, dut->o_rvvi_rd_data);
        }

        // Kanata pipeline trace
        if (kanata) {
            KanataTracer::Signals ksig;
            ksig.alloc_valid  = dut->o_trace_alloc_valid;
            ksig.alloc_idx    = dut->o_trace_alloc_idx;
            ksig.alloc_physrd = dut->o_trace_alloc_physrd;
            ksig.cdb_valid    = dut->o_trace_cdb_valid;
            ksig.cdb_tag      = dut->o_trace_cdb_tag;
            ksig.flush        = dut->o_trace_flush;
            ksig.commit_valid = dut->o_rvvi_valid;
            ksig.head_idx     = dut->o_trace_head_idx;
            ksig.commit_pc    = dut->o_rvvi_pc_rdata;
            ksig.commit_insn  = dut->o_rvvi_insn;
            // RS dispatch signals (int, mem, branch, muldiv, fp)
            ksig.dispatch[0] = {(bool)dut->o_trace_dispatch_int,    dut->o_trace_dispatch_int_tag};
            ksig.dispatch[1] = {(bool)dut->o_trace_dispatch_mem,    dut->o_trace_dispatch_mem_tag};
            ksig.dispatch[2] = {(bool)dut->o_trace_dispatch_branch, dut->o_trace_dispatch_branch_tag};
            ksig.dispatch[3] = {(bool)dut->o_trace_dispatch_muldiv, dut->o_trace_dispatch_muldiv_tag};
            ksig.dispatch[4] = {(bool)dut->o_trace_dispatch_fp,     dut->o_trace_dispatch_fp_tag};
            kanata->tick(cycle, ksig);
        }

        // Log all dmem accesses if +verbose
        if (verbose && dut->o_dmem_req_valid) {
            printf("  %s cy%u addr=0x%08x data=0x%08x\n",
                dut->o_dmem_req_we ? "STORE" : "LOAD ",
                cycle, dut->o_dmem_req_addr, dut->o_dmem_req_data);
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
            printf("  Retired:   %u\n", retired);
            printf("  IPC:       %.3f\n", cycle > 0 ? (double)retired / cycle : 0.0);
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
    printf("Total retired: %u\n", retired);
    printf("IPC: %.3f\n", cycle > 0 ? (double)retired / cycle : 0.0);

#if VM_TRACE
    if (trace) {
        trace->close();
        delete trace;
    }
#endif

    dut->final();
    return done && dut->o_test_pass ? 0 : 1;
}
