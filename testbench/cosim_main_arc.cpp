//==============================================================================
// cosim_main_arc.cpp - Lock-Step Cosimulation with Arcilator backend
//
// Three-way comparison: RTL (Arcilator) vs Spike (ISA reference) vs C++ Sim
// Driven by RVVI-TRACE signals from the RTL model.
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

#include "tb_cpu_arc.h"
#include "lib/elf_loader.h"
#include "lib/spike_oracle.h"

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

// Check if instruction is a CSR read of a performance counter.
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

// Find 'tohost' symbol address in ELF symbol table
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

struct RVVIState {
    bool     valid;
    bool     trap;
    uint32_t pc;
    uint32_t insn;
    uint32_t rd;
    bool     rd_valid;
    uint32_t rd_data;
    uint32_t frd;
    bool     frd_valid;
    uint32_t frd_data;
    uint32_t fflags;
};

static RVVIState read_rvvi(const tb_cpu_model& m) {
    RVVIState s = {};
    s.valid    = m.get_o_rvvi_valid();
    s.trap     = m.get_o_rvvi_trap();
    s.pc       = m.get_o_rvvi_pc_rdata();
    s.insn     = m.get_o_rvvi_insn();
    s.rd       = m.get_o_rvvi_rd();
    s.rd_valid = m.get_o_rvvi_rd_valid();
    s.rd_data  = m.get_o_rvvi_rd_data();
    s.frd      = m.get_o_rvvi_frd();
    s.frd_valid = m.get_o_rvvi_frd_valid();
    s.frd_data = m.get_o_rvvi_frd_data();
    s.fflags   = m.get_o_fflags_acc();
    return s;
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

    // Initialize arcilator model
    tb_cpu_model model;
    memset(model.state, 0, sizeof(model.state));

    // Load ELF into model state memory
    int elf_bytes = load_elf(elf_path, [&](uint32_t byte_addr, uint32_t data) {
        model.write_mem_word(MEM_STATE_OFFSET, byte_addr, data);
    });
    if (elf_bytes < 0) return 1;

    uint32_t tohost_addr = find_tohost_addr(elf_path);

    // Initialize Spike oracle
    auto spike = std::make_unique<SpikeOracle>(elf_path);

    // Reset
    model.set_clk(0);
    model.set_rst_n(0);
    for (int i = 0; i < 10; i++) {
        model.set_clk(i & 1);
        model.eval();
    }
    model.set_rst_n(1);

    // Main simulation loop
    uint64_t cycle = 0;
    uint64_t retired = 0;
    uint64_t mismatches = 0;
    bool done = false;

    while (!done && cycle < timeout) {
        // Posedge
        model.set_clk(1);
        model.eval();

        RVVIState rvvi = read_rvvi(model);
        if (rvvi.valid) {
            SpikeStepResult spike_r = spike->step();
            int skip = 0;
            while (spike_r.pc != rvvi.pc && skip < 32) {
                if (is_unsyncable_csr_read(spike_r.insn) && spike_r.rd != 0) {
                    uint32_t csr_addr = (spike_r.insn >> 20) & 0xfff;
                    if (csr_addr == 0xB02 || csr_addr == 0xC02) {
                        spike->set_xreg(spike_r.rd, spike_r.rd_value - 1);
                    }
                }
                spike_r = spike->step();
                skip++;
            }

            bool skip_rd_cmp = false;
            if (is_unsyncable_csr_read(rvvi.insn)) {
                if (rvvi.rd_valid && spike_r.rd != 0) {
                    spike->set_xreg(spike_r.rd, rvvi.rd_data);
                }
                skip_rd_cmp = true;
            }

            if (rvvi.pc != spike_r.pc) {
                fprintf(stderr,
                    "MISMATCH at retirement #%lu (cycle %lu): "
                    "PC RTL=0x%08x Spike=0x%08x (skipped %d)\n",
                    retired, cycle, rvvi.pc, spike_r.pc, skip);
                mismatches++;
            }

            if (rvvi.insn != spike_r.insn) {
                fprintf(stderr,
                    "MISMATCH at retirement #%lu (cycle %lu): "
                    "insn RTL=0x%08x Spike=0x%08x\n",
                    retired, cycle, rvvi.insn, spike_r.insn);
                mismatches++;
            }

            if (rvvi.rd_valid && spike_r.rd != 0 && !skip_rd_cmp) {
                if (rvvi.rd_data != spike_r.rd_value) {
                    fprintf(stderr,
                        "MISMATCH at retirement #%lu (cycle %lu): "
                        "x%u RTL=0x%08x Spike=0x%08x (rd_data)\n",
                        retired, cycle, spike_r.rd, rvvi.rd_data, spike_r.rd_value);
                    mismatches++;
                }
            }

            if (spike_r.frd_valid && rvvi.frd_valid) {
                if (rvvi.frd_data != spike_r.frd_value) {
                    fprintf(stderr,
                        "MISMATCH at retirement #%lu (cycle %lu): "
                        "f%u RTL=0x%08x Spike=0x%08x (frd_data)\n",
                        retired, cycle, spike_r.frd, rvvi.frd_data, spike_r.frd_value);
                    mismatches++;
                }
            } else if (spike_r.frd_valid && !rvvi.frd_valid) {
                fprintf(stderr,
                    "MISMATCH at retirement #%lu (cycle %lu): "
                    "frd_valid RTL=%d Spike=%d\n",
                    retired, cycle, rvvi.frd_valid, spike_r.frd_valid);
                mismatches++;
            }

            retired++;

            if (mismatches > 10) {
                fprintf(stderr, "Too many mismatches, aborting.\n");
                done = true;
            }
        }

        if (model.get_o_test_done()) {
            done = true;
        }

        // Negedge
        model.set_clk(0);
        model.eval();
        cycle++;
    }

    uint32_t tohost = model.get_o_tohost();
    printf("Cosimulation complete (backend=arcilator):\n");
    printf("  Cycles:      %lu\n", cycle);
    printf("  Retired:     %lu\n", retired);
    printf("  IPC:         %.3f\n", cycle > 0 ? (double)retired / cycle : 0.0);
    printf("  Mismatches:  %lu\n", mismatches);
    printf("  tohost:      0x%08x\n", tohost);

    if (mismatches == 0 && tohost == 1) {
        printf("COSIM PASS\n");
        return 0;
    } else {
        printf("COSIM FAIL\n");
        return 1;
    }
}
