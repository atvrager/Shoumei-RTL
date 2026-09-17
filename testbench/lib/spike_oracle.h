#pragma once

#include <cstdint>
#include <memory>
#include <string>

// Forward declarations
class processor_t;
class simif_t;
struct cfg_t;

struct SpikeStepResult {
    uint64_t pc;        // PC of retired instruction
    uint32_t insn;      // Instruction word
    uint32_t rd;        // Destination register (0 if none)
    uint64_t rd_value;  // Written value (0 if rd==0)
    uint64_t rs1_value; // Pre-step rs1 value (for load address detection)
    bool     trap;      // Exception occurred
    // F/D extension
    uint32_t frd;       // FP destination register (0 if none)
    uint64_t frd_value; // FP written value (0 if frd==0)
    bool     frd_valid; // FP register was written
    uint32_t fflags;    // Accumulated FP exception flags (NV|DZ|OF|UF|NX)
};

class SpikeOracle {
public:
    // Load ELF and configure M-mode, memory at 0x0
    // isa defaults to "rv64g" if not specified
    explicit SpikeOracle(const std::string& elf_path,
                         const std::string& isa = "rv64g");
    ~SpikeOracle();

    // Step one instruction, return state for comparison
    SpikeStepResult step();

    // Read/write architectural register
    uint64_t get_xreg(int i) const;
    void set_xreg(int i, uint64_t val);

    // Read FP register (as raw bits)
    uint64_t get_freg(int i) const;

    // Read CSR
    uint64_t get_csr(int which) const;

    // Get/set current PC
    uint64_t get_pc() const;
    void set_pc(uint64_t pc);

    // Read instruction word at a given address
    uint32_t get_insn_at(uint64_t addr) const;

    // Force-unhalt after WFI (clears halted flag)
    void unhalt();

    // Save/restore full architectural state (PC + x0-x31 + f0-f31)
    struct ArchState {
        uint64_t pc;
        uint64_t xregs[32];
        uint64_t fregs[32];
    };
    ArchState save_state() const;
    void restore_state(const ArchState& s);

    // Timer: tick mtime, inject MIP.MTIP into Spike
    void tick_timer();

    // Set MIP.MTIP directly
    void set_mip_mtip(bool val);

private:
    std::string isa_storage_;  // keeps ISA string alive for cfg_->isa pointer
    std::unique_ptr<cfg_t> cfg_;
    std::unique_ptr<simif_t> simif_;
    std::unique_ptr<processor_t> proc_;
};
