//==============================================================================
// cosim_main_arc.cpp - Lock-Step Cosimulation with Arcilator backend
//
// RTL (Arcilator) vs Spike (ISA reference) comparison.
// Drives the CPU directly (no SV testbench wrapper).
//
// Usage:
//   ./build-sim/cosim_shoumei_arc +elf=path/to/program.elf [+timeout=N]
//==============================================================================

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdint>
#include <memory>
#include <vector>
#include <elf.h>

#include "cpu_arc.h"
#include "lib/elf_loader.h"
#include "lib/spike_oracle.h"

using Model = CPU_RV32IMF_Zicsr_Zifencei_Microcoded_L1I256B_L1D256B_L2512B_model;

static const uint32_t DEFAULT_TIMEOUT = 100000;
static const uint32_t MEM_SIZE_WORDS = 16384;
static const uint32_t MEM_BASE = 0x00000000;

static uint32_t mem[MEM_SIZE_WORDS];

static const char* get_plusarg(int argc, char** argv, const char* name) {
    size_t len = strlen(name);
    for (int i = 1; i < argc; i++) {
        if (strncmp(argv[i], name, len) == 0 && argv[i][len] == '=')
            return argv[i] + len + 1;
    }
    return nullptr;
}

static bool is_unsyncable_csr_read(uint32_t insn) {
    uint32_t opcode = insn & 0x7f;
    if (opcode != 0x73) return false;
    uint32_t funct3 = (insn >> 12) & 0x7;
    if (funct3 == 0) return false;
    uint32_t csr_addr = (insn >> 20) & 0xfff;
    return csr_addr == 0xB00 || csr_addr == 0xB02 ||
           csr_addr == 0xB80 || csr_addr == 0xB82 ||
           csr_addr == 0xC00 || csr_addr == 0xC02 ||
           csr_addr == 0xC80 || csr_addr == 0xC82;
}

static uint32_t find_tohost_addr(const char* path) {
    FILE* f = fopen(path, "rb");
    if (!f) return 0x1000;
    Elf32_Ehdr ehdr;
    if (fread(&ehdr, sizeof(ehdr), 1, f) != 1) { fclose(f); return 0x1000; }
    for (int i = 0; i < ehdr.e_shnum; i++) {
        Elf32_Shdr shdr;
        fseek(f, ehdr.e_shoff + i * ehdr.e_shentsize, SEEK_SET);
        if (fread(&shdr, sizeof(shdr), 1, f) != 1) continue;
        if (shdr.sh_type != SHT_SYMTAB) continue;
        Elf32_Shdr strhdr;
        fseek(f, ehdr.e_shoff + shdr.sh_link * ehdr.e_shentsize, SEEK_SET);
        if (fread(&strhdr, sizeof(strhdr), 1, f) != 1) continue;
        std::vector<char> strtab(strhdr.sh_size);
        fseek(f, strhdr.sh_offset, SEEK_SET);
        (void)fread(strtab.data(), 1, strhdr.sh_size, f);
        int nsyms = shdr.sh_size / shdr.sh_entsize;
        for (int j = 0; j < nsyms; j++) {
            Elf32_Sym sym;
            fseek(f, shdr.sh_offset + j * shdr.sh_entsize, SEEK_SET);
            if (fread(&sym, sizeof(sym), 1, f) != 1) continue;
            if (sym.st_name < strhdr.sh_size &&
                strcmp(&strtab[sym.st_name], "tohost") == 0) {
                fclose(f);
                return sym.st_value;
            }
        }
    }
    fclose(f);
    return 0x1000;
}

static void pack_cache_line(uint32_t base_word_idx, uint8_t* dest) {
    for (int w = 0; w < 8; w++) {
        uint32_t idx = base_word_idx + w;
        uint32_t val = (idx < MEM_SIZE_WORDS) ? mem[idx] : 0;
        memcpy(dest + w * 4, &val, 4);
    }
}

static void unpack_cache_line(uint32_t base_word_idx, const uint8_t* src) {
    for (int w = 0; w < 8; w++) {
        uint32_t idx = base_word_idx + w;
        if (idx < MEM_SIZE_WORDS)
            memcpy(&mem[idx], src + w * 4, 4);
    }
}

int main(int argc, char** argv) {
    const char* elf_path = get_plusarg(argc, argv, "+elf");
    if (!elf_path) {
        fprintf(stderr, "Usage: %s +elf=<path.elf> [+timeout=N]\n", argv[0]);
        return 1;
    }

    uint32_t timeout = DEFAULT_TIMEOUT;
    const char* to = get_plusarg(argc, argv, "+timeout");
    if (to) timeout = static_cast<uint32_t>(atol(to));

    // Load ELF into C++ memory
    memset(mem, 0, sizeof(mem));
    int elf_bytes = load_elf(elf_path, [&](uint32_t byte_addr, uint32_t data) {
        uint32_t word_idx = (byte_addr - MEM_BASE) >> 2;
        if (word_idx < MEM_SIZE_WORDS) mem[word_idx] = data;
    });
    if (elf_bytes < 0) return 1;

    uint32_t tohost_addr = find_tohost_addr(elf_path);

    // Initialize Spike oracle
    auto spike = std::make_unique<SpikeOracle>(elf_path);

    // Initialize model
    Model model;
    model.set_zero(0);
    model.set_one(1);

    // Reset
    model.set_reset(1);
    model.set_mem_resp_valid(0);
    for (int i = 0; i < 10; i++) {
        model.set_clock(0); model.eval();
        model.set_clock(1); model.eval();
    }
    model.set_reset(0);
    model.set_clock(0); model.eval();

    // Memory state machine (2-cycle read latency)
    bool mem_pending = false;
    bool mem_ready = false;
    uint8_t mem_read_line[32] = {};

    uint64_t cycle = 0;
    uint64_t retired = 0;
    uint64_t mismatches = 0;
    bool done = false;

    while (!done && cycle < timeout) {
        model.set_clock(1);

        if (mem_ready) {
            model.set_mem_resp_valid(1);
            memcpy(model.mem_resp_data_ptr(), mem_read_line, 32);
            mem_ready = false;
        } else {
            model.set_mem_resp_valid(0);
        }
        if (mem_pending) { mem_ready = true; mem_pending = false; }

        model.eval();

        // Memory requests
        if (model.get_mem_req_valid()) {
            uint32_t addr = model.get_mem_req_addr();
            uint32_t word_idx = (addr - MEM_BASE) >> 2;
            if (model.get_mem_req_we())
                unpack_cache_line(word_idx, model.mem_req_data_ptr());
            else {
                pack_cache_line(word_idx, mem_read_line);
                mem_pending = true;
            }
        }

        // RVVI comparison
        if (model.get_rvvi_valid()) {
            uint32_t rtl_pc   = model.get_rvvi_pc_rdata();
            uint32_t rtl_insn = model.get_rvvi_insn();
            uint32_t rtl_rd   = model.get_rvvi_rd();
            bool     rtl_rd_v = model.get_rvvi_rd_valid();
            uint32_t rtl_rd_d = model.get_rvvi_rd_data();
            bool     rtl_frd_v = model.get_rvvi_frd_valid();
            uint32_t rtl_frd_d = model.get_rvvi_frd_data();

            SpikeStepResult spike_r = spike->step();
            int skip = 0;
            while (spike_r.pc != rtl_pc && skip < 32) {
                if (is_unsyncable_csr_read(spike_r.insn) && spike_r.rd != 0) {
                    uint32_t csr_addr = (spike_r.insn >> 20) & 0xfff;
                    if (csr_addr == 0xB02 || csr_addr == 0xC02)
                        spike->set_xreg(spike_r.rd, spike_r.rd_value - 1);
                }
                spike_r = spike->step();
                skip++;
            }

            bool skip_rd_cmp = is_unsyncable_csr_read(rtl_insn);
            if (skip_rd_cmp && rtl_rd_v && spike_r.rd != 0)
                spike->set_xreg(spike_r.rd, rtl_rd_d);

            if (rtl_pc != spike_r.pc) {
                fprintf(stderr, "MISMATCH ret#%lu cyc%lu: PC RTL=0x%08x Spike=0x%08x\n",
                    retired, cycle, rtl_pc, spike_r.pc);
                mismatches++;
            }
            if (rtl_insn != spike_r.insn) {
                fprintf(stderr, "MISMATCH ret#%lu cyc%lu: insn RTL=0x%08x Spike=0x%08x\n",
                    retired, cycle, rtl_insn, spike_r.insn);
                mismatches++;
            }
            if (rtl_rd_v && spike_r.rd != 0 && !skip_rd_cmp && rtl_rd_d != spike_r.rd_value) {
                fprintf(stderr, "MISMATCH ret#%lu cyc%lu: x%u RTL=0x%08x Spike=0x%08x\n",
                    retired, cycle, spike_r.rd, rtl_rd_d, spike_r.rd_value);
                mismatches++;
            }
            if (spike_r.frd_valid && rtl_frd_v && rtl_frd_d != spike_r.frd_value) {
                fprintf(stderr, "MISMATCH ret#%lu cyc%lu: f%u RTL=0x%08x Spike=0x%08x\n",
                    retired, cycle, spike_r.frd, rtl_frd_d, spike_r.frd_value);
                mismatches++;
            }

            retired++;
            if (mismatches > 10) { fprintf(stderr, "Too many mismatches.\n"); done = true; }
        }

        // Check tohost via store snooping
        if (model.get_store_snoop_valid() && model.get_store_snoop_addr() == tohost_addr)
            done = true;

        model.set_clock(0);
        model.eval();
        cycle++;
    }

    uint32_t tohost_val = 0;
    if (model.get_store_snoop_valid() && model.get_store_snoop_addr() == tohost_addr)
        tohost_val = model.get_store_snoop_data();
    // Also check memory for tohost
    if (tohost_val == 0) {
        uint32_t idx = (tohost_addr - MEM_BASE) >> 2;
        if (idx < MEM_SIZE_WORDS) tohost_val = mem[idx];
    }

    printf("Cosimulation complete (backend=arcilator):\n");
    printf("  Cycles:     %lu\n", cycle);
    printf("  Retired:    %lu\n", retired);
    printf("  IPC:        %.3f\n", cycle > 0 ? (double)retired / cycle : 0.0);
    printf("  Mismatches: %lu\n", mismatches);
    printf("  tohost:     0x%08x\n", tohost_val);

    if (mismatches == 0 && tohost_val == 1) {
        printf("COSIM PASS\n");
        return 0;
    } else {
        printf("COSIM FAIL\n");
        return 1;
    }
}
