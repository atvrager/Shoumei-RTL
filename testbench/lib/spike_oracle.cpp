#include "spike_oracle.h"

#include <riscv/processor.h>
#include <riscv/mmu.h>
#include <riscv/simif.h>
#include <riscv/cfg.h>

#include <vector>
#include <map>
#include <cstring>
#include <cstdio>
#include <elf.h>

// Custom simif_t that provides flat memory at address 0x0
// Avoids sim_t's debug module / boot ROM conflicts
class flat_simif_t : public simif_t {
public:
    static constexpr size_t MEM_SIZE = 0x10000; // 64KB

    explicit flat_simif_t(cfg_t* cfg) : cfg_(cfg), mem_(MEM_SIZE, 0) {}

    char* addr_to_mem(reg_t paddr) override {
        if (paddr < MEM_SIZE)
            return &mem_[paddr];
        return nullptr;
    }

    bool mmio_load(reg_t, size_t, uint8_t*) override { return false; }
    bool mmio_store(reg_t, size_t, const uint8_t*) override { return false; }
    void proc_reset(unsigned) override {}
    const cfg_t& get_cfg() const override { return *cfg_; }
    const std::map<size_t, processor_t*>& get_harts() const override { return harts_; }
    const char* get_symbol(uint64_t) override { return nullptr; }

    void register_hart(size_t id, processor_t* p) { harts_[id] = p; }

    // Load ELF segments into flat memory
    int load_elf(const char* path) {
        FILE* f = fopen(path, "rb");
        if (!f) return -1;

        Elf32_Ehdr ehdr;
        if (fread(&ehdr, sizeof(ehdr), 1, f) != 1) { fclose(f); return -1; }

        for (int i = 0; i < ehdr.e_phnum; i++) {
            Elf32_Phdr phdr;
            fseek(f, ehdr.e_phoff + i * ehdr.e_phentsize, SEEK_SET);
            if (fread(&phdr, sizeof(phdr), 1, f) != 1) continue;
            if (phdr.p_type != PT_LOAD || phdr.p_filesz == 0) continue;

            std::vector<uint8_t> seg(phdr.p_memsz, 0);
            fseek(f, phdr.p_offset, SEEK_SET);
            (void)fread(seg.data(), 1, phdr.p_filesz, f);

            if (phdr.p_paddr + phdr.p_memsz <= MEM_SIZE) {
                memcpy(&mem_[phdr.p_paddr], seg.data(), phdr.p_memsz);
            }
        }
        fclose(f);
        return 0;
    }

private:
    cfg_t* cfg_;
    std::map<size_t, processor_t*> harts_;
    std::vector<char> mem_;
};

SpikeOracle::SpikeOracle(const std::string& elf_path)
    : cfg_(std::make_unique<cfg_t>()) {
    cfg_->isa = "rv32imf";
    cfg_->priv = "m";
    cfg_->hartids = {0};
    cfg_->start_pc = 0;

    auto* flat = new flat_simif_t(cfg_.get());
    flat->load_elf(elf_path.c_str());
    simif_.reset(flat);

    proc_ = std::make_unique<processor_t>(
        cfg_->isa, cfg_->priv, cfg_.get(), simif_.get(),
        /*hartid=*/0, /*halted=*/false, /*log_file=*/nullptr,
        /*sout=*/std::cerr);

    flat->register_hart(0, proc_.get());
    proc_->get_state()->pc = 0;

    // Enable FP: set MSTATUS.FS = Dirty (bits 14:13 = 11)
    // Without this, Spike traps on any FP instruction with illegal-insn
    proc_->put_csr(/*CSR_MSTATUS*/ 0x300,
                   proc_->get_csr(/*CSR_MSTATUS*/ 0x300) | 0x6000);
}

SpikeOracle::~SpikeOracle() = default;

SpikeStepResult SpikeOracle::step() {
    SpikeStepResult r = {};
    r.pc = static_cast<uint32_t>(proc_->get_state()->pc);

    uint32_t regs_before[32];
    for (int i = 0; i < 32; i++)
        regs_before[i] = static_cast<uint32_t>(proc_->get_state()->XPR[i]);

    // Snapshot FP registers before stepping
    uint32_t fregs_before[32];
    for (int i = 0; i < 32; i++)
        fregs_before[i] = static_cast<uint32_t>(proc_->get_state()->FPR[i].v[0]);

    try {
        r.insn = static_cast<uint32_t>(
            proc_->get_mmu()->load<uint32_t>(r.pc));
    } catch (...) {
        r.insn = 0;
    }

    try {
        proc_->step(1);
        r.trap = false;
    } catch (...) {
        r.trap = true;
    }

    // Detect integer register change
    for (int i = 1; i < 32; i++) {
        uint32_t val = static_cast<uint32_t>(proc_->get_state()->XPR[i]);
        if (val != regs_before[i]) {
            r.rd = static_cast<uint32_t>(i);
            r.rd_value = val;
            break;
        }
    }

    // Detect FP register change
    r.frd_valid = false;
    for (int i = 0; i < 32; i++) {
        uint32_t val = static_cast<uint32_t>(proc_->get_state()->FPR[i].v[0]);
        if (val != fregs_before[i]) {
            r.frd = static_cast<uint32_t>(i);
            r.frd_value = val;
            r.frd_valid = true;
            break;
        }
    }

    return r;
}

uint32_t SpikeOracle::get_xreg(int i) const {
    return static_cast<uint32_t>(proc_->get_state()->XPR[i]);
}

uint32_t SpikeOracle::get_freg(int i) const {
    return static_cast<uint32_t>(proc_->get_state()->FPR[i].v[0]);
}

uint32_t SpikeOracle::get_pc() const {
    return static_cast<uint32_t>(proc_->get_state()->pc);
}
