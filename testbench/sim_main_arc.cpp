//==============================================================================
// sim_main_arc.cpp - Arcilator simulation driver for Shoumei CPU
//
// Drives the CPU model compiled by arcilator (no SV testbench wrapper).
// Implements cache-line memory, tohost/putchar detection, and ELF loading
// entirely in C++.
//
// Build:  make -C testbench sim-arc
// Run:    ./build-sim/sim_shoumei_arc +elf=path/to/program.elf [+timeout=N]
//==============================================================================

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdint>
#include <elf.h>

#include "cpu_arc.h"
#include "lib/elf_loader.h"

// Use a shorter alias for the long model name
using Model = CPU_RV32IMF_Zicsr_Zifencei_Microcoded_L1I256B_L1D256B_L2512B_model;

static struct _StdoutUnbuffer {
    _StdoutUnbuffer() { setvbuf(stdout, nullptr, _IONBF, 0); }
} _stdout_unbuffer;

static const uint32_t DEFAULT_TIMEOUT = 100000;
static const uint32_t MEM_SIZE_WORDS = 16384;
static const uint32_t TOHOST_DEFAULT = 0x1000;
static const uint32_t PUTCHAR_DEFAULT = 0x1004;
static const uint32_t MEM_BASE = 0x00000000;

// C++ memory model (replaces SV testbench memory)
static uint32_t mem[MEM_SIZE_WORDS];

static const char* get_plusarg(int argc, char** argv, const char* name) {
    size_t len = strlen(name);
    for (int i = 1; i < argc; i++) {
        if (strncmp(argv[i], name, len) == 0 && argv[i][len] == '=')
            return argv[i] + len + 1;
    }
    return nullptr;
}

static bool has_plusarg(int argc, char** argv, const char* name) {
    for (int i = 1; i < argc; i++)
        if (strcmp(argv[i], name) == 0) return true;
    return false;
}

// ELF symbol lookup
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

// Pack 8 consecutive memory words into a 256-bit cache line (little-endian)
static void pack_cache_line(uint32_t base_word_idx, uint8_t* dest) {
    for (int w = 0; w < 8; w++) {
        uint32_t idx = base_word_idx + w;
        uint32_t val = (idx < MEM_SIZE_WORDS) ? mem[idx] : 0;
        memcpy(dest + w * 4, &val, 4);
    }
}

// Unpack a 256-bit cache line into 8 consecutive memory words
static void unpack_cache_line(uint32_t base_word_idx, const uint8_t* src) {
    for (int w = 0; w < 8; w++) {
        uint32_t idx = base_word_idx + w;
        if (idx < MEM_SIZE_WORDS) {
            memcpy(&mem[idx], src + w * 4, 4);
        }
    }
}

int main(int argc, char** argv) {
    const char* elf_path = get_plusarg(argc, argv, "+elf");
    const char* timeout_str = get_plusarg(argc, argv, "+timeout");
    bool verbose = has_plusarg(argc, argv, "+verbose");

    uint32_t timeout = timeout_str ? atoi(timeout_str) : DEFAULT_TIMEOUT;

    if (!elf_path) {
        fprintf(stderr, "ERROR: No ELF file specified. Use +elf=path/to/program.elf\n");
        return 1;
    }

    // Load ELF into C++ memory array
    memset(mem, 0, sizeof(mem));
    printf("Loading ELF: %s\n", elf_path);

    int elf_bytes = load_elf(elf_path, [&](uint32_t byte_addr, uint32_t data) {
        uint32_t word_idx = (byte_addr - MEM_BASE) >> 2;
        if (word_idx < MEM_SIZE_WORDS)
            mem[word_idx] = data;
    });
    if (elf_bytes < 0) return 1;

    // Look up tohost/putchar symbols
    int64_t tohost_sym = elf_lookup_symbol(elf_path, "tohost");
    uint32_t tohost_addr = (tohost_sym >= 0) ? (uint32_t)tohost_sym : TOHOST_DEFAULT;
    int64_t putchar_sym = elf_lookup_symbol(elf_path, "putchar_addr");
    uint32_t putchar_addr = (putchar_sym >= 0) ? (uint32_t)putchar_sym : PUTCHAR_DEFAULT;
    if (tohost_sym >= 0)
        printf("ELF symbol: tohost = 0x%08x\n", tohost_addr);

    // Initialize model
    Model model;
    model.set_zero(0);
    model.set_one(1);

    // Reset sequence
    model.set_mem_resp_valid(0);
    model.set_reset(1);
    for (int i = 0; i < 10; i++) {
        model.set_clock(0);
        model.eval();
        model.set_clock(1);
        model.eval();
    }
    model.set_reset(0);
    model.set_clock(0);
    model.eval();

    // Memory state machine (mirrors SV testbench: 2-cycle read latency)
    // Cycle N: request seen, data latched → Cycle N+1: pending → Cycle N+2: response valid
    bool mem_pending = false;
    bool mem_ready = false;
    uint8_t mem_read_line[32] = {};

    uint32_t cycle = 0;
    uint32_t retired = 0;
    bool done = false;
    bool pass = false;
    uint32_t test_code = 0;

    printf("Simulation started (timeout=%u cycles, backend=arcilator)\n", timeout);

    while (!done && cycle < timeout) {
        // Rising edge
        model.set_clock(1);

        // Drive memory response (2-cycle read latency like SV testbench)
        if (mem_ready) {
            model.set_mem_resp_valid(1);
            memcpy(model.mem_resp_data_ptr(), mem_read_line, 32);
            mem_ready = false;
        } else {
            model.set_mem_resp_valid(0);
        }
        if (mem_pending) {
            mem_ready = true;
            mem_pending = false;
        }

        model.eval();

        // Process memory request (after eval, check outputs)
        if (model.get_mem_req_valid()) {
            uint32_t addr = model.get_mem_req_addr();
            uint32_t word_idx = (addr - MEM_BASE) >> 2;

            if (model.get_mem_req_we()) {
                // Cache-line write
                unpack_cache_line(word_idx, model.mem_req_data_ptr());
            } else {
                // Cache-line read (1-cycle latency)
                pack_cache_line(word_idx, mem_read_line);
                mem_pending = true;
            }
        }

        // Check RVVI retirement
        if (model.get_rvvi_valid()) {
            retired++;
            if (verbose)
                printf("  RET[%u] PC=0x%08x insn=0x%08x rd=x%u(%d) data=0x%08x\n",
                    retired, model.get_rvvi_pc_rdata(), model.get_rvvi_insn(),
                    model.get_rvvi_rd(), (int)model.get_rvvi_rd_valid(),
                    model.get_rvvi_rd_data());
        }

        // Check store snooping for tohost/putchar
        if (model.get_store_snoop_valid()) {
            uint32_t saddr = model.get_store_snoop_addr();
            uint32_t sdata = model.get_store_snoop_data();

            if (saddr == tohost_addr) {
                test_code = sdata;
                pass = (sdata == 1);
                done = true;
            } else if (saddr == putchar_addr) {
                putchar(sdata & 0xFF);
            }
        }

        // Falling edge
        model.set_clock(0);
        model.eval();

        cycle++;

        if (cycle % 10000 == 0)
            printf("  [%u cycles] PC=0x%08x\n", cycle, model.get_rvvi_pc_rdata());
    }

    if (done) {
        if (pass)
            printf("\nPASS\n");
        else
            printf("\nFAIL (test_num=%u)\n", test_code >> 1);
        printf("  Cycle:   %u\n", cycle);
        printf("  Retired: %u\n", retired);
        printf("  IPC:     %.3f\n", cycle > 0 ? (double)retired / cycle : 0.0);
    } else {
        printf("\nTIMEOUT after %u cycles\n", cycle);
        printf("  PC: 0x%08x\n", model.get_rvvi_pc_rdata());
    }

    return done && pass ? 0 : 1;
}
