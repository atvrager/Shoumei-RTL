#include "cppsim_oracle.h"
#include "cpu_setup_CPU_RV32IMF_Zicsr_Zifencei.h"
#include "elf_loader.h"
#include <cstring>
#include <cstdio>

// ============================================================================
// Bus helpers
// ============================================================================

uint32_t CppSimOracle::read_bus(bool** sigs, int bits) {
    uint32_t v = 0;
    for (int i = 0; i < bits; i++)
        v |= (*sigs[i] ? 1u : 0u) << i;
    return v;
}

void CppSimOracle::write_bus(bool** sigs, uint32_t val, int bits) {
    for (int i = 0; i < bits; i++)
        *sigs[i] = (val >> i) & 1;
}

// ============================================================================
// Memory models
// ============================================================================

void CppSimOracle::imem_update() {
    uint32_t pc = read_bus(fetch_pc_sigs_, 32);
    uint32_t widx = pc / 4;
    uint32_t word = (widx < MEM_SIZE_WORDS) ? mem_[widx] : 0;
    write_bus(imem_resp_data_sigs_, word, 32);
}

void CppSimOracle::dmem_tick(bool req_valid, bool req_we,
                              uint32_t addr, uint32_t data, uint32_t size) {
    dmem_resp_valid_ = false;

    if (dmem_pending_) {
        dmem_resp_valid_ = true;
        write_bus(dmem_resp_data_sigs_, dmem_read_data_, 32);
        dmem_pending_ = false;
    }

    if (req_valid) {
        uint32_t widx = addr / 4;
        uint32_t byte_off = addr & 3;

        if (req_we) {
            // Store
            if (widx < MEM_SIZE_WORDS) {
                uint32_t cur = mem_[widx];
                if (size == 0) {
                    // SB
                    uint32_t mask = 0xFFu << (byte_off * 8);
                    cur = (cur & ~mask) | ((data & 0xFF) << (byte_off * 8));
                } else if (size == 1) {
                    // SH
                    uint32_t shift = (byte_off & 2) * 8;
                    uint32_t mask = 0xFFFFu << shift;
                    cur = (cur & ~mask) | ((data & 0xFFFF) << shift);
                } else {
                    // SW
                    cur = data;
                }
                mem_[widx] = cur;
            }
            // Check tohost
            if (addr == 0x1000 && data != 0) {
                test_done_ = true;
                test_data_ = data;
            }
            dmem_pending_ = true;
            dmem_read_data_ = 0;
        } else {
            // Load
            uint32_t word = (widx < MEM_SIZE_WORDS) ? mem_[widx] : 0;
            dmem_pending_ = true;
            dmem_read_data_ = word;
        }
    }
}

void CppSimOracle::settle() {
    for (int i = 0; i < 10; i++) {
        imem_update();
        cpu_eval_comb_all(ctx_);
    }
}

// ============================================================================
// Constructor
// ============================================================================

CppSimOracle::CppSimOracle(const std::string& elf_path) {
    // Initialize signal pointer arrays
    for (int i = 0; i < 32; i++) {
        imem_resp_data_sigs_[i] = &imem_resp_data_[i];
        dmem_resp_data_sigs_[i] = &dmem_resp_data_[i];
        fetch_pc_sigs_[i] = &fetch_pc_[i];
        dmem_req_addr_sigs_[i] = &dmem_req_addr_[i];
        dmem_req_data_sigs_[i] = &dmem_req_data_[i];
        rvvi_pc_rdata_sigs_[i] = &rvvi_pc_rdata_[i];
        rvvi_insn_sigs_[i] = &rvvi_insn_[i];
        rvvi_rd_data_sigs_[i] = &rvvi_rd_data_[i];
        rvvi_frd_data_sigs_[i] = &rvvi_frd_data_[i];
    }
    for (int i = 0; i < 5; i++) {
        rvvi_rd_sigs_[i] = &rvvi_rd_[i];
        rvvi_frd_sigs_[i] = &rvvi_frd_[i];
        fflags_acc_sigs_[i] = &fflags_acc_[i];
    }
    dmem_req_size_sigs_[0] = &dmem_req_size_[0];
    dmem_req_size_sigs_[1] = &dmem_req_size_[1];

    // Build the port pointer array matching the cpu_setup port order
    // This must match the order in cpu_setup_CPU_RV32IMF_Zicsr_Zifencei.cpp exactly
    bool* cpu_ports[] = {
        &clock_sig_, &zero_sig_, &one_sig_,
        // imem_resp_data [0..31]
        &imem_resp_data_[0], &imem_resp_data_[1], &imem_resp_data_[2], &imem_resp_data_[3],
        &imem_resp_data_[4], &imem_resp_data_[5], &imem_resp_data_[6], &imem_resp_data_[7],
        &imem_resp_data_[8], &imem_resp_data_[9], &imem_resp_data_[10], &imem_resp_data_[11],
        &imem_resp_data_[12], &imem_resp_data_[13], &imem_resp_data_[14], &imem_resp_data_[15],
        &imem_resp_data_[16], &imem_resp_data_[17], &imem_resp_data_[18], &imem_resp_data_[19],
        &imem_resp_data_[20], &imem_resp_data_[21], &imem_resp_data_[22], &imem_resp_data_[23],
        &imem_resp_data_[24], &imem_resp_data_[25], &imem_resp_data_[26], &imem_resp_data_[27],
        &imem_resp_data_[28], &imem_resp_data_[29], &imem_resp_data_[30], &imem_resp_data_[31],
        // dmem response inputs
        &dmem_req_ready_, &dmem_resp_valid_,
        &dmem_resp_data_[0], &dmem_resp_data_[1], &dmem_resp_data_[2], &dmem_resp_data_[3],
        &dmem_resp_data_[4], &dmem_resp_data_[5], &dmem_resp_data_[6], &dmem_resp_data_[7],
        &dmem_resp_data_[8], &dmem_resp_data_[9], &dmem_resp_data_[10], &dmem_resp_data_[11],
        &dmem_resp_data_[12], &dmem_resp_data_[13], &dmem_resp_data_[14], &dmem_resp_data_[15],
        &dmem_resp_data_[16], &dmem_resp_data_[17], &dmem_resp_data_[18], &dmem_resp_data_[19],
        &dmem_resp_data_[20], &dmem_resp_data_[21], &dmem_resp_data_[22], &dmem_resp_data_[23],
        &dmem_resp_data_[24], &dmem_resp_data_[25], &dmem_resp_data_[26], &dmem_resp_data_[27],
        &dmem_resp_data_[28], &dmem_resp_data_[29], &dmem_resp_data_[30], &dmem_resp_data_[31],
        // fetch_pc outputs [0..31]
        &fetch_pc_[0], &fetch_pc_[1], &fetch_pc_[2], &fetch_pc_[3],
        &fetch_pc_[4], &fetch_pc_[5], &fetch_pc_[6], &fetch_pc_[7],
        &fetch_pc_[8], &fetch_pc_[9], &fetch_pc_[10], &fetch_pc_[11],
        &fetch_pc_[12], &fetch_pc_[13], &fetch_pc_[14], &fetch_pc_[15],
        &fetch_pc_[16], &fetch_pc_[17], &fetch_pc_[18], &fetch_pc_[19],
        &fetch_pc_[20], &fetch_pc_[21], &fetch_pc_[22], &fetch_pc_[23],
        &fetch_pc_[24], &fetch_pc_[25], &fetch_pc_[26], &fetch_pc_[27],
        &fetch_pc_[28], &fetch_pc_[29], &fetch_pc_[30], &fetch_pc_[31],
        // control signals
        &fetch_stalled_, &global_stall_,
        // dmem request outputs [addr, we, data, size]
        &dmem_req_valid_, &dmem_req_we_,
        &dmem_req_addr_[0], &dmem_req_addr_[1], &dmem_req_addr_[2], &dmem_req_addr_[3],
        &dmem_req_addr_[4], &dmem_req_addr_[5], &dmem_req_addr_[6], &dmem_req_addr_[7],
        &dmem_req_addr_[8], &dmem_req_addr_[9], &dmem_req_addr_[10], &dmem_req_addr_[11],
        &dmem_req_addr_[12], &dmem_req_addr_[13], &dmem_req_addr_[14], &dmem_req_addr_[15],
        &dmem_req_addr_[16], &dmem_req_addr_[17], &dmem_req_addr_[18], &dmem_req_addr_[19],
        &dmem_req_addr_[20], &dmem_req_addr_[21], &dmem_req_addr_[22], &dmem_req_addr_[23],
        &dmem_req_addr_[24], &dmem_req_addr_[25], &dmem_req_addr_[26], &dmem_req_addr_[27],
        &dmem_req_addr_[28], &dmem_req_addr_[29], &dmem_req_addr_[30], &dmem_req_addr_[31],
        &dmem_req_data_[0], &dmem_req_data_[1], &dmem_req_data_[2], &dmem_req_data_[3],
        &dmem_req_data_[4], &dmem_req_data_[5], &dmem_req_data_[6], &dmem_req_data_[7],
        &dmem_req_data_[8], &dmem_req_data_[9], &dmem_req_data_[10], &dmem_req_data_[11],
        &dmem_req_data_[12], &dmem_req_data_[13], &dmem_req_data_[14], &dmem_req_data_[15],
        &dmem_req_data_[16], &dmem_req_data_[17], &dmem_req_data_[18], &dmem_req_data_[19],
        &dmem_req_data_[20], &dmem_req_data_[21], &dmem_req_data_[22], &dmem_req_data_[23],
        &dmem_req_data_[24], &dmem_req_data_[25], &dmem_req_data_[26], &dmem_req_data_[27],
        &dmem_req_data_[28], &dmem_req_data_[29], &dmem_req_data_[30], &dmem_req_data_[31],
        &dmem_req_size_[0], &dmem_req_size_[1],
        // rob_empty
        &rob_empty_,
        // RVVI outputs
        &rvvi_valid_, &rvvi_trap_,
        &rvvi_pc_rdata_[0], &rvvi_pc_rdata_[1], &rvvi_pc_rdata_[2], &rvvi_pc_rdata_[3],
        &rvvi_pc_rdata_[4], &rvvi_pc_rdata_[5], &rvvi_pc_rdata_[6], &rvvi_pc_rdata_[7],
        &rvvi_pc_rdata_[8], &rvvi_pc_rdata_[9], &rvvi_pc_rdata_[10], &rvvi_pc_rdata_[11],
        &rvvi_pc_rdata_[12], &rvvi_pc_rdata_[13], &rvvi_pc_rdata_[14], &rvvi_pc_rdata_[15],
        &rvvi_pc_rdata_[16], &rvvi_pc_rdata_[17], &rvvi_pc_rdata_[18], &rvvi_pc_rdata_[19],
        &rvvi_pc_rdata_[20], &rvvi_pc_rdata_[21], &rvvi_pc_rdata_[22], &rvvi_pc_rdata_[23],
        &rvvi_pc_rdata_[24], &rvvi_pc_rdata_[25], &rvvi_pc_rdata_[26], &rvvi_pc_rdata_[27],
        &rvvi_pc_rdata_[28], &rvvi_pc_rdata_[29], &rvvi_pc_rdata_[30], &rvvi_pc_rdata_[31],
        &rvvi_insn_[0], &rvvi_insn_[1], &rvvi_insn_[2], &rvvi_insn_[3],
        &rvvi_insn_[4], &rvvi_insn_[5], &rvvi_insn_[6], &rvvi_insn_[7],
        &rvvi_insn_[8], &rvvi_insn_[9], &rvvi_insn_[10], &rvvi_insn_[11],
        &rvvi_insn_[12], &rvvi_insn_[13], &rvvi_insn_[14], &rvvi_insn_[15],
        &rvvi_insn_[16], &rvvi_insn_[17], &rvvi_insn_[18], &rvvi_insn_[19],
        &rvvi_insn_[20], &rvvi_insn_[21], &rvvi_insn_[22], &rvvi_insn_[23],
        &rvvi_insn_[24], &rvvi_insn_[25], &rvvi_insn_[26], &rvvi_insn_[27],
        &rvvi_insn_[28], &rvvi_insn_[29], &rvvi_insn_[30], &rvvi_insn_[31],
        &rvvi_rd_[0], &rvvi_rd_[1], &rvvi_rd_[2], &rvvi_rd_[3], &rvvi_rd_[4],
        &rvvi_rd_valid_,
        &rvvi_rd_data_[0], &rvvi_rd_data_[1], &rvvi_rd_data_[2], &rvvi_rd_data_[3],
        &rvvi_rd_data_[4], &rvvi_rd_data_[5], &rvvi_rd_data_[6], &rvvi_rd_data_[7],
        &rvvi_rd_data_[8], &rvvi_rd_data_[9], &rvvi_rd_data_[10], &rvvi_rd_data_[11],
        &rvvi_rd_data_[12], &rvvi_rd_data_[13], &rvvi_rd_data_[14], &rvvi_rd_data_[15],
        &rvvi_rd_data_[16], &rvvi_rd_data_[17], &rvvi_rd_data_[18], &rvvi_rd_data_[19],
        &rvvi_rd_data_[20], &rvvi_rd_data_[21], &rvvi_rd_data_[22], &rvvi_rd_data_[23],
        &rvvi_rd_data_[24], &rvvi_rd_data_[25], &rvvi_rd_data_[26], &rvvi_rd_data_[27],
        &rvvi_rd_data_[28], &rvvi_rd_data_[29], &rvvi_rd_data_[30], &rvvi_rd_data_[31],
        &rvvi_frd_[0], &rvvi_frd_[1], &rvvi_frd_[2], &rvvi_frd_[3], &rvvi_frd_[4],
        &rvvi_frd_valid_,
        &rvvi_frd_data_[0], &rvvi_frd_data_[1], &rvvi_frd_data_[2], &rvvi_frd_data_[3],
        &rvvi_frd_data_[4], &rvvi_frd_data_[5], &rvvi_frd_data_[6], &rvvi_frd_data_[7],
        &rvvi_frd_data_[8], &rvvi_frd_data_[9], &rvvi_frd_data_[10], &rvvi_frd_data_[11],
        &rvvi_frd_data_[12], &rvvi_frd_data_[13], &rvvi_frd_data_[14], &rvvi_frd_data_[15],
        &rvvi_frd_data_[16], &rvvi_frd_data_[17], &rvvi_frd_data_[18], &rvvi_frd_data_[19],
        &rvvi_frd_data_[20], &rvvi_frd_data_[21], &rvvi_frd_data_[22], &rvvi_frd_data_[23],
        &rvvi_frd_data_[24], &rvvi_frd_data_[25], &rvvi_frd_data_[26], &rvvi_frd_data_[27],
        &rvvi_frd_data_[28], &rvvi_frd_data_[29], &rvvi_frd_data_[30], &rvvi_frd_data_[31],
        &fflags_acc_[0], &fflags_acc_[1], &fflags_acc_[2], &fflags_acc_[3], &fflags_acc_[4],
    };

    ctx_ = cpu_create("cppsim", &reset_sig_, cpu_ports, 319);

    // Load ELF into memory
    load_elf(elf_path.c_str(), [this](uint32_t addr, uint32_t data) {
        uint32_t widx = addr / 4;
        if (widx < MEM_SIZE_WORDS) mem_[widx] = data;
    });

    // Reset phase
    reset_sig_ = true;
    dmem_req_ready_ = true;
    for (int i = 0; i < 5; i++) {
        cpu_eval_seq_sample_all(ctx_);
        cpu_eval_seq_all(ctx_);
        settle();
    }
    reset_sig_ = false;
    settle();
}

CppSimOracle::~CppSimOracle() {
    if (ctx_) cpu_delete(ctx_);
}

// ============================================================================
// Step: run cycles until next RVVI retirement
// ============================================================================

CppSimStepResult CppSimOracle::step() {
    while (cycle_ < MAX_CYCLES) {
        // Snapshot dmem inputs
        bool snap_req_valid = dmem_req_valid_;
        bool snap_req_we = dmem_req_we_;
        uint32_t snap_addr = read_bus(dmem_req_addr_sigs_, 32);
        uint32_t snap_data = read_bus(dmem_req_data_sigs_, 32);
        uint32_t snap_size = read_bus(dmem_req_size_sigs_, 2);

        // Two-phase DFF
        cpu_eval_seq_sample_all(ctx_);
        cpu_eval_seq_all(ctx_);

        // dmem tick with snapshots
        dmem_tick(snap_req_valid, snap_req_we, snap_addr, snap_data, snap_size);

        // Settle
        settle();
        cycle_++;

        // Check RVVI retirement
        if (rvvi_valid_) {
            CppSimStepResult r = {};
            r.pc       = read_bus(rvvi_pc_rdata_sigs_, 32);
            r.insn     = read_bus(rvvi_insn_sigs_, 32);
            r.rd       = read_bus(rvvi_rd_sigs_, 5);
            r.rd_valid = rvvi_rd_valid_;
            r.rd_data  = read_bus(rvvi_rd_data_sigs_, 32);
            r.frd      = read_bus(rvvi_frd_sigs_, 5);
            r.frd_valid = rvvi_frd_valid_;
            r.frd_data = read_bus(rvvi_frd_data_sigs_, 32);
            r.fflags   = read_bus(fflags_acc_sigs_, 5);
            r.done     = test_done_;
            r.tohost   = test_data_;
            return r;
        }

        if (test_done_) {
            CppSimStepResult r = {};
            r.done = true;
            r.tohost = test_data_;
            return r;
        }
    }

    // Timeout
    CppSimStepResult r = {};
    r.done = true;
    r.tohost = 0;
    return r;
}
