#pragma once

#include <cstdint>
#include <memory>
#include <string>

// Forward declarations
class processor_t;
class simif_t;
struct cfg_t;

struct SpikeStepResult {
    uint32_t pc;        // PC of retired instruction
    uint32_t insn;      // Instruction word
    uint32_t rd;        // Destination register (0 if none)
    uint32_t rd_value;  // Written value (0 if rd==0)
    bool     trap;      // Exception occurred
    // F extension
    uint32_t frd;       // FP destination register (0 if none)
    uint32_t frd_value; // FP written value (0 if frd==0)
    bool     frd_valid; // FP register was written
};

class SpikeOracle {
public:
    // Load ELF and configure rv32im, M-mode, memory at 0x0
    explicit SpikeOracle(const std::string& elf_path);
    ~SpikeOracle();

    // Step one instruction, return state for comparison
    SpikeStepResult step();

    // Read architectural register
    uint32_t get_xreg(int i) const;

    // Read FP register (as raw bits)
    uint32_t get_freg(int i) const;

    // Get current PC
    uint32_t get_pc() const;

private:
    std::unique_ptr<cfg_t> cfg_;
    std::unique_ptr<simif_t> simif_;
    std::unique_ptr<processor_t> proc_;
};
