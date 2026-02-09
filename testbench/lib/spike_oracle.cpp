#include "spike_oracle.h"

#include <riscv/sim.h>
#include <riscv/processor.h>
#include <riscv/mmu.h>
#include <fesvr/elf.h>

#include <vector>
#include <cstring>

SpikeOracle::SpikeOracle(const std::string& elf_path) {
    // Configure: RV32IM, single hart, M-mode
    // Memory at 0x0 to match our linker script (testbench/tests/link.ld)
    cfg_t cfg;
    cfg.isa = "rv32im";
    cfg.priv = "m";

    std::vector<mem_cfg_t> mem_cfg = {{0x0, 0x10000}};

    sim_ = std::make_unique<sim_t>(
        &cfg, false, mem_cfg,
        std::vector<std::string>{elf_path},
        /*dtb=*/nullptr, /*log_path=*/nullptr,
        /*htif_args=*/std::vector<std::string>{});
    proc_ = sim_->get_core(0);
}

SpikeOracle::~SpikeOracle() = default;

SpikeStepResult SpikeOracle::step() {
    SpikeStepResult r = {};
    r.pc = static_cast<uint32_t>(proc_->get_state()->pc);

    // Snapshot registers before step
    uint32_t regs_before[32];
    for (int i = 0; i < 32; i++)
        regs_before[i] = static_cast<uint32_t>(proc_->get_state()->XPR[i]);

    // Read instruction word at current PC
    try {
        r.insn = static_cast<uint32_t>(
            proc_->get_mmu()->load<uint32_t>(r.pc));
    } catch (...) {
        r.insn = 0;
    }

    // Step one instruction
    try {
        proc_->step(1);
        r.trap = false;
    } catch (...) {
        r.trap = true;
    }

    // Detect which register changed (skip x0)
    for (int i = 1; i < 32; i++) {
        uint32_t val = static_cast<uint32_t>(proc_->get_state()->XPR[i]);
        if (val != regs_before[i]) {
            r.rd = static_cast<uint32_t>(i);
            r.rd_value = val;
            break;
        }
    }

    return r;
}

uint32_t SpikeOracle::get_xreg(int i) const {
    return static_cast<uint32_t>(proc_->get_state()->XPR[i]);
}

uint32_t SpikeOracle::get_pc() const {
    return static_cast<uint32_t>(proc_->get_state()->pc);
}
