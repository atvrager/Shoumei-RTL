#pragma once

#include <cstdint>
#include <memory>
#include <string>

// Forward declarations to avoid pulling in Spike headers everywhere
class sim_t;
class processor_t;
struct cfg_t;

struct SpikeStepResult {
    uint32_t pc;        // PC of retired instruction
    uint32_t insn;      // Instruction word
    uint32_t rd;        // Destination register (0 if none)
    uint32_t rd_value;  // Written value (0 if rd==0)
    bool     trap;      // Exception occurred
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

    // Get current PC
    uint32_t get_pc() const;

private:
    std::unique_ptr<sim_t> sim_;
    processor_t* proc_;  // non-owning, owned by sim_
};
