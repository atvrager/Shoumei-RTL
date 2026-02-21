//==============================================================================
// sim_main_arc.cpp - Arcilator testbench for Shoumei CPU
//
// Drives the tb_cpu model compiled by arcilator (CIRCT's MLIR/LLVM simulator):
//   1. Loads an ELF binary into memory via direct state array writes
//   2. Runs clock cycles until tohost is written or timeout
//   3. Reports PASS/FAIL with cycle count
//
// Key differences from Verilator sim_main.cpp:
//   - No DPI-C: memory loaded directly into model state array
//   - No Verilated:: API: uses arcilator's eval() function
//   - State accessed via generated header from arcilator --state-file JSON
//
// Build:  make -C testbench sim-arc
// Run:    ./build-sim/sim_shoumei_arc +elf=path/to/program.elf [+timeout=N]
//==============================================================================

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdint>
#include <elf.h>

#include "tb_cpu_arc.h"
#include "lib/elf_loader.h"

// Disable stdout buffering for non-TTY contexts
static struct _StdoutUnbuffer {
    _StdoutUnbuffer() { setvbuf(stdout, nullptr, _IONBF, 0); }
} _stdout_unbuffer;

static const uint32_t DEFAULT_TIMEOUT = 100000;

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

    for (int i = 0; i < ehdr.e_shnum; i++) {
        Elf32_Shdr shdr;
        fseek(f, ehdr.e_shoff + i * ehdr.e_shentsize, SEEK_SET);
        if (fread(&shdr, sizeof(shdr), 1, f) != 1) continue;
        if (shdr.sh_type != SHT_SYMTAB) continue;

        Elf32_Shdr strhdr;
        fseek(f, ehdr.e_shoff + shdr.sh_link * ehdr.e_shentsize, SEEK_SET);
        if (fread(&strhdr, sizeof(strhdr), 1, f) != 1) continue;

        auto* strtab = new char[strhdr.sh_size];
        fseek(f, strhdr.sh_offset, SEEK_SET);
        if (fread(strtab, 1, strhdr.sh_size, f) != strhdr.sh_size) {
            delete[] strtab; continue;
        }

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

int main(int argc, char** argv) {
    // Parse arguments
    const char* elf_path = get_plusarg(argc, argv, "+elf");
    const char* timeout_str = get_plusarg(argc, argv, "+timeout");
    bool verbose = has_plusarg(argc, argv, "+verbose");

    uint32_t timeout = timeout_str ? atoi(timeout_str) : DEFAULT_TIMEOUT;

    if (!elf_path) {
        fprintf(stderr, "ERROR: No ELF file specified. Use +elf=path/to/program.elf\n");
        return 1;
    }

    // Initialize model
    tb_cpu_model model;
    memset(model.state, 0, sizeof(model.state));

    // Load ELF directly into model state memory.
    // The memory base offset in the state array is determined by gen-arc-header.py
    // from the arcilator state JSON. We need to discover it at build time.
    // For now, use the MEM_STATE_OFFSET constant from the generated header.
    printf("Loading ELF: %s\n", elf_path);

    int elf_bytes = load_elf(elf_path, [&](uint32_t byte_addr, uint32_t data) {
        model.write_mem_word(MEM_STATE_OFFSET, byte_addr, data);
    });
    if (elf_bytes < 0) return 1;

    // Look up tohost/putchar symbols
    int64_t tohost_sym = elf_lookup_symbol(elf_path, "tohost");
    uint32_t tohost_addr = (tohost_sym >= 0) ? (uint32_t)tohost_sym : 0x1000;
    if (tohost_sym >= 0)
        printf("ELF symbol: tohost = 0x%08x\n", tohost_addr);

    // Reset: assert rst_n=0, clock several times, then deassert
    model.set_rst_n(0);
    model.set_clk(0);
    for (int i = 0; i < 10; i++) {
        model.set_clk(i & 1);
        model.eval();
    }
    model.set_rst_n(1);

    // Main simulation loop
    uint32_t cycle = 0;
    uint32_t retired = 0;
    bool done = false;

    printf("Simulation started (timeout=%u cycles, backend=arcilator)\n", timeout);
    printf("─────────────────────────────────────────────\n");

    while (!done && cycle < timeout) {
        // Rising edge
        model.set_clk(1);
        model.eval();

        // Check RVVI retirement
        if (model.get_o_rvvi_valid()) {
            retired++;
            if (verbose)
                printf("  RET[%u] PC=0x%08x insn=0x%08x rd=x%u(%d) data=0x%08x\n",
                    retired, model.get_o_rvvi_pc_rdata(), model.get_o_rvvi_insn(),
                    model.get_o_rvvi_rd(), (int)model.get_o_rvvi_rd_valid(),
                    model.get_o_rvvi_rd_data());
        }

        // Check termination via output ports
        if (model.get_o_test_done()) {
            done = true;
            if (model.get_o_test_pass()) {
                printf("\n══════ TEST PASS ══════\n");
            } else {
                printf("\n══════ TEST FAIL ══════\n");
                printf("  test_num:  %u\n", model.get_o_test_code() >> 1);
            }
            printf("  Cycle:     %u\n", cycle);
            printf("  Retired:   %u\n", retired);
            printf("  IPC:       %.3f\n", cycle > 0 ? (double)retired / cycle : 0.0);
            printf("  PC:        0x%08x\n", model.get_o_fetch_pc());
            printf("  tohost:    0x%08x\n", model.get_o_test_code());
        }

        // Falling edge
        model.set_clk(0);
        model.eval();

        cycle++;

        if (cycle % 10000 == 0) {
            printf("  [%u cycles] PC=0x%08x\n", cycle, model.get_o_fetch_pc());
        }
    }

    if (!done) {
        printf("\n══════ TIMEOUT ══════\n");
        printf("  Cycle:     %u\n", cycle);
        printf("  PC:        0x%08x\n", model.get_o_fetch_pc());
    }

    printf("─────────────────────────────────────────────\n");
    printf("Total cycles: %u\n", cycle);
    printf("Total retired: %u\n", retired);
    printf("IPC: %.3f\n", cycle > 0 ? (double)retired / cycle : 0.0);

    return done && model.get_o_test_pass() ? 0 : 1;
}
