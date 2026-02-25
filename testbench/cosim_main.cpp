//==============================================================================
// cosim_main.cpp - Lock-Step Cosimulation Testbench
//
// Three-way comparison: RTL (Verilator) vs Spike (ISA reference) vs C++ Sim
// Driven by RVVI-TRACE signals from the RTL DUT.
//
// Usage:
//   ./build-sim/cosim_shoumei +elf=path/to/program.elf [+timeout=N]
//
// See docs/cosimulation.md for design details.
//==============================================================================

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <memory>
#include <elf.h>

#include "Vtb_cpu.h"
#include "verilated.h"
#include "svdpi.h"

#include "lib/spike_oracle.h"
#include "generated/lean_sim_CPU_RV32IMF_Zicsr_Zifencei.h"

// DPI-C exported from tb_cpu.sv
extern "C" void dpi_mem_write(unsigned int word_addr, unsigned int data);
extern "C" void dpi_set_tohost_addr(unsigned int addr);

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

// Load ELF file into simulated memory via DPI-C
static int load_elf(const char* path) {
    FILE* f = fopen(path, "rb");
    if (!f) {
        fprintf(stderr, "ERROR: Cannot open ELF file: %s\n", path);
        return -1;
    }

    Elf32_Ehdr ehdr;
    if (fread(&ehdr, sizeof(ehdr), 1, f) != 1) {
        fprintf(stderr, "ERROR: Cannot read ELF header: %s\n", path);
        fclose(f);
        return -1;
    }

    if (memcmp(ehdr.e_ident, ELFMAG, SELFMAG) != 0 ||
        ehdr.e_ident[EI_CLASS] != ELFCLASS32) {
        fprintf(stderr, "ERROR: Not a valid 32-bit ELF: %s\n", path);
        fclose(f);
        return -1;
    }

    for (int i = 0; i < ehdr.e_phnum; i++) {
        Elf32_Phdr phdr;
        fseek(f, ehdr.e_phoff + i * ehdr.e_phentsize, SEEK_SET);
        if (fread(&phdr, sizeof(phdr), 1, f) != 1) continue;
        if (phdr.p_type != PT_LOAD || phdr.p_filesz == 0) continue;

        std::vector<uint8_t> seg(phdr.p_memsz, 0);
        fseek(f, phdr.p_offset, SEEK_SET);
        (void)fread(seg.data(), 1, phdr.p_filesz, f);

        for (uint32_t off = 0; off < phdr.p_memsz; off += 4) {
            uint32_t addr = phdr.p_paddr + off;
            uint32_t word = 0;
            memcpy(&word, &seg[off], std::min<uint32_t>(4, phdr.p_memsz - off));
            dpi_mem_write(addr >> 2, word);
        }
    }

    fclose(f);
    return 0;
}

// Check if instruction is a CSR read of a performance counter.
// These CSRs (mcycle, minstret, mcycleh, minstreth, and their read-only
// aliases cycle, instret, cycleh, instreth) have implementation-defined
// values that legitimately differ between RTL and Spike.
static bool is_unsyncable_csr_read(uint32_t insn) {
    uint32_t opcode = insn & 0x7f;
    if (opcode != 0x73) return false;  // Not SYSTEM
    uint32_t funct3 = (insn >> 12) & 0x7;
    if (funct3 == 0) return false;     // ECALL/EBREAK, not CSR
    uint32_t csr_addr = (insn >> 20) & 0xfff;
    // mcycle=0xB00, mcycleh=0xB80, cycle=0xC00, cycleh=0xC80
    //   RTL cycle count differs from Spike's
    // minstret=0xB02, minstreth=0xB82, instret=0xC02, instreth=0xC82
    //   Spec says csrr reads pre-increment value; Spike returns post-increment
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

// Extract RVVI signals from the RTL DUT (per-slot)
struct RVVIState {
    bool     valid;
    bool     trap;
    uint32_t pc;
    uint32_t insn;
    uint32_t rd;        // architectural destination register
    bool     rd_valid;
    uint32_t rd_data;
};

static RVVIState read_rvvi_slot0(const Vtb_cpu* dut) {
    RVVIState s = {};
    s.valid    = dut->o_rvvi_valid_0;
    s.trap     = dut->o_rvvi_trap_0;
    s.pc       = dut->o_rvvi_pc_rdata_0;
    s.insn     = dut->o_rvvi_insn_0;
    s.rd       = dut->o_rvvi_rd_0;
    s.rd_valid = dut->o_rvvi_rd_valid_0;
    s.rd_data  = dut->o_rvvi_rd_data_0;
    return s;
}

static RVVIState read_rvvi_slot1(const Vtb_cpu* dut) {
    RVVIState s = {};
    s.valid    = dut->o_rvvi_valid_1;
    s.trap     = dut->o_rvvi_trap_1;
    s.pc       = dut->o_rvvi_pc_rdata_1;
    s.insn     = dut->o_rvvi_insn_1;
    s.rd       = dut->o_rvvi_rd_1;
    s.rd_valid = dut->o_rvvi_rd_valid_1;
    s.rd_data  = dut->o_rvvi_rd_data_1;
    return s;
}

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);

    const char* elf_path = get_plusarg(argc, argv, "+elf");
    if (!elf_path) {
        fprintf(stderr, "Usage: %s +elf=<path.elf> [+timeout=N]\n", argv[0]);
        return 1;
    }

    uint32_t timeout = DEFAULT_TIMEOUT;
    const char* to = get_plusarg(argc, argv, "+timeout");
    if (to) timeout = static_cast<uint32_t>(atol(to));

    // Initialize RTL DUT
    auto dut = std::make_unique<Vtb_cpu>();

    // Load ELF into RTL memory
    dut->eval();  // Initialize DPI context
    svSetScope(svGetScopeFromName("TOP.tb_cpu"));
    if (load_elf(elf_path) != 0) return 1;

    // Set tohost address from ELF symbol table
    uint32_t tohost_addr = find_tohost_addr(elf_path);
    dpi_set_tohost_addr(tohost_addr);

    // Initialize Spike oracle
    auto spike = std::make_unique<SpikeOracle>(elf_path);

    // Initialize C++ sim oracle (same Lean-generated circuit, different codegen path)
    auto lean_sim = std::make_unique<LeanSim>(elf_path);

    // Reset (rst_n is active-low)
    dut->clk = 0;
    dut->rst_n = 0;
    for (int i = 0; i < 10; i++) {
        dut->clk = !dut->clk;
        dut->eval();
    }
    dut->rst_n = 1;

    // Main simulation loop
    uint64_t cycle = 0;
    uint64_t retired = 0;
    uint64_t mismatches = 0;
    bool done = false;

    // Lambda to compare one RVVI slot against Spike + LeanSim
    auto compare_slot = [&](const RVVIState& rvvi, int slot) {
        // Step Spike, advancing past instructions the RTL doesn't
        // report (e.g. branches/jumps resolved in the fetch stage)
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

        // Sync perf counter CSR reads visible via RVVI
        bool skip_rd_cmp = false;
        if (is_unsyncable_csr_read(rvvi.insn)) {
            if (rvvi.rd_valid && spike_r.rd != 0) {
                spike->set_xreg(spike_r.rd, rvvi.rd_data);
            }
            skip_rd_cmp = true;
        }

        // Compare PC
        if (rvvi.pc != spike_r.pc) {
            fprintf(stderr,
                "MISMATCH ret#%lu cy%lu slot%d: "
                "PC RTL=0x%08x Spike=0x%08x (skip %d)\n",
                retired, cycle, slot, rvvi.pc, spike_r.pc, skip);
            mismatches++;
        }

        // Compare instruction word
        if (rvvi.insn != spike_r.insn) {
            fprintf(stderr,
                "MISMATCH ret#%lu cy%lu slot%d: "
                "insn RTL=0x%08x Spike=0x%08x\n",
                retired, cycle, slot, rvvi.insn, spike_r.insn);
            mismatches++;
        }

        // Compare integer register writeback
        if (rvvi.rd_valid && spike_r.rd != 0 && !skip_rd_cmp) {
            if (rvvi.rd_data != spike_r.rd_value) {
                fprintf(stderr,
                    "MISMATCH ret#%lu cy%lu slot%d: "
                    "PC=0x%08x insn=0x%08x x%u RTL=0x%08x Spike=0x%08x\n",
                    retired, cycle, slot, rvvi.pc, rvvi.insn,
                    spike_r.rd, rvvi.rd_data, spike_r.rd_value);
                mismatches++;
            }
        }

        // FP register comparison: not available in W=2 RVVI yet
        // TODO: add FP RVVI outputs to CPU and compare here

        // 3-way: compare C++ sim
        LeanSimStepResult cs_r = lean_sim->step();
        if (!cs_r.done) {
            if (rvvi.pc != cs_r.pc) {
                fprintf(stderr,
                    "MISMATCH ret#%lu cy%lu slot%d: "
                    "PC RTL=0x%08x LeanSim=0x%08x Spike=0x%08x\n",
                    retired, cycle, slot, rvvi.pc, cs_r.pc, spike_r.pc);
                if (cs_r.pc == spike_r.pc)
                    fprintf(stderr, "  -> SV codegen bug (RTL wrong, LeanSim+Spike agree)\n");
                else if (rvvi.pc == cs_r.pc)
                    fprintf(stderr, "  -> Spike disagree (RTL+LeanSim agree)\n");
                else
                    fprintf(stderr, "  -> Lean circuit bug (RTL+LeanSim both wrong)\n");
                mismatches++;
            }
            if (cs_r.rd_valid && cs_r.rd != 0 && rvvi.rd_valid) {
                if (cs_r.rd_data != rvvi.rd_data) {
                    fprintf(stderr,
                        "MISMATCH ret#%lu cy%lu slot%d: "
                        "x%u RTL=0x%08x LeanSim=0x%08x\n",
                        retired, cycle, slot, cs_r.rd, rvvi.rd_data, cs_r.rd_data);
                    mismatches++;
                }
            }
        }

        retired++;
    };

    while (!done && cycle < timeout) {
        // Posedge
        dut->clk = 1;
        dut->eval();

        // Check RVVI — dual-slot retirement
        RVVIState rvvi0 = read_rvvi_slot0(dut.get());
        RVVIState rvvi1 = read_rvvi_slot1(dut.get());

        // Slot 0 retires first (in program order)
        if (rvvi0.valid) {
            compare_slot(rvvi0, 0);
        }
        // Slot 1 retires second
        if (rvvi1.valid) {
            compare_slot(rvvi1, 1);
        }

        if (mismatches > 10) {
            fprintf(stderr, "Too many mismatches\n");
            done = true;
        }

        // Check for test completion (tohost write)
        if (dut->o_test_done) {
            done = true;
        }

        // Negedge
        dut->clk = 0;
        dut->eval();
        cycle++;
    }

    // Check final state
    uint32_t tohost = dut->o_tohost;
    printf("Cosimulation complete:\n");
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
