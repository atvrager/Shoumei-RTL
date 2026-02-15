#pragma once

#include <cstdint>
#include <queue>
#include <string>

struct CpuCtx;

struct CppSimStepResult {
    uint32_t pc;
    uint32_t insn;
    uint32_t rd;
    uint32_t rd_data;
    bool     rd_valid;
    uint32_t frd;
    uint32_t frd_data;
    bool     frd_valid;
    uint32_t fflags;
    bool     done;       // tohost written
    uint32_t tohost;
};

class CppSimOracle {
public:
    explicit CppSimOracle(const std::string& elf_path);
    ~CppSimOracle();

    // Run until the next RVVI retirement and return it.
    // Returns done=true if tohost written or timeout.
    CppSimStepResult step();

private:
    void tick();  // Run one cycle of the C++ sim

    // Memory (shared with sim_main approach)
    static constexpr uint32_t MEM_SIZE_WORDS = 16384;
    uint32_t mem_[MEM_SIZE_WORDS] = {};

    // CPU context
    CpuCtx* ctx_ = nullptr;

    // Signals (all the bools the CPU ports point to)
    bool clock_sig_ = false;
    bool reset_sig_ = false;
    bool zero_sig_ = false;
    bool one_sig_ = true;

    // imem
    bool imem_resp_data_[32] = {};

    // dmem request outputs (from CPU)
    bool dmem_req_valid_ = false;
    bool dmem_req_we_ = false;
    bool dmem_req_addr_[32] = {};
    bool dmem_req_data_[32] = {};
    bool dmem_req_size_[2] = {};

    // dmem response inputs (to CPU)
    bool dmem_req_ready_ = true;
    bool dmem_resp_valid_ = false;
    bool dmem_resp_data_[32] = {};

    // fetch
    bool fetch_pc_[32] = {};
    bool fetch_stalled_ = false;
    bool global_stall_ = false;
    bool rob_empty_ = false;

    // RVVI
    bool rvvi_valid_ = false;
    bool rvvi_trap_ = false;
    bool rvvi_pc_rdata_[32] = {};
    bool rvvi_insn_[32] = {};
    bool rvvi_rd_[5] = {};
    bool rvvi_rd_valid_ = false;
    bool rvvi_rd_data_[32] = {};
    bool rvvi_frd_[5] = {};
    bool rvvi_frd_valid_ = false;
    bool rvvi_frd_data_[32] = {};
    bool fflags_acc_[5] = {};

    // Signal pointer arrays
    bool* imem_resp_data_sigs_[32];
    bool* dmem_resp_data_sigs_[32];
    bool* fetch_pc_sigs_[32];
    bool* dmem_req_addr_sigs_[32];
    bool* dmem_req_data_sigs_[32];
    bool* dmem_req_size_sigs_[2];
    bool* rvvi_pc_rdata_sigs_[32];
    bool* rvvi_insn_sigs_[32];
    bool* rvvi_rd_sigs_[5];
    bool* rvvi_rd_data_sigs_[32];
    bool* rvvi_frd_sigs_[5];
    bool* rvvi_frd_data_sigs_[32];
    bool* fflags_acc_sigs_[5];

    // Dmem state (mirroring sim_main's DmemState)
    bool dmem_pending_ = false;
    uint32_t dmem_read_data_ = 0;
    bool test_done_ = false;
    uint32_t test_data_ = 0;

    uint32_t cycle_ = 0;
    static constexpr uint32_t MAX_CYCLES = 200000;

    // Helpers
    uint32_t read_bus(bool** sigs, int bits);
    void write_bus(bool** sigs, uint32_t val, int bits);
    void imem_update();
    void dmem_tick(bool req_valid, bool req_we, uint32_t addr, uint32_t data, uint32_t size);
    void settle();
};
