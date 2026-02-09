#include "systemc_oracle.h"

#ifdef HAS_SYSTEMC

#include <cstring>
#include <cstdio>
#include <elf.h>

// TODO: Include the generated SystemC CPU header once RVVI ports are added
// #include "CPU_RV32IM.h"

struct SystemCOracle::Impl {
    // TODO: Instantiate SC_MODULE(CPU_RV32IM) with sc_signals
    // sc_signal<bool> clk, rst;
    // sc_signal<sc_bv<32>> imem_resp_data;
    // ... etc
    // CPU_RV32IM cpu{"sc_cpu"};

    // Memory model (shared with RTL testbench)
    uint32_t mem[0x10000 / 4];  // 64KB

    Impl() {
        memset(mem, 0, sizeof(mem));
    }
};

SystemCOracle::SystemCOracle(const std::string& elf_path)
    : impl_(std::make_unique<Impl>())
{
    // Load ELF into SystemC memory model
    FILE* f = fopen(elf_path.c_str(), "rb");
    if (!f) {
        fprintf(stderr, "SystemCOracle: cannot open ELF: %s\n", elf_path.c_str());
        return;
    }

    Elf32_Ehdr ehdr;
    if (fread(&ehdr, sizeof(ehdr), 1, f) != 1) { fclose(f); return; }

    for (int i = 0; i < ehdr.e_phnum; i++) {
        Elf32_Phdr phdr;
        fseek(f, ehdr.e_phoff + i * ehdr.e_phentsize, SEEK_SET);
        if (fread(&phdr, sizeof(phdr), 1, f) != 1) continue;
        if (phdr.p_type != PT_LOAD) continue;

        fseek(f, phdr.p_offset, SEEK_SET);
        uint8_t* dest = reinterpret_cast<uint8_t*>(impl_->mem) + phdr.p_paddr;
        fread(dest, 1, phdr.p_filesz, f);
    }
    fclose(f);

    // TODO: Connect SC_MODULE ports to signals, bind memory
    // TODO: Run sc_start(0, SC_NS) to initialize
}

SystemCOracle::~SystemCOracle() = default;

SystemCStepResult SystemCOracle::step() {
    SystemCStepResult r = {};

    // TODO: Clock the SystemC model until rvvi_valid is asserted
    // For now, return empty result (3-way mode is aspirational)
    fprintf(stderr, "SystemCOracle::step() not yet implemented\n");

    return r;
}

uint32_t SystemCOracle::get_xreg(int /*i*/) const {
    // TODO: Read through committed RAT + PRF
    return 0;
}

uint32_t SystemCOracle::get_pc() const {
    // TODO: Read from SystemC model
    return 0;
}

void SystemCOracle::reset(int /*cycles*/) {
    // TODO: Assert reset for N cycles
}

#endif // HAS_SYSTEMC
