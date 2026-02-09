#pragma once

#ifdef HAS_SYSTEMC

#include <cstdint>
#include <string>
#include <memory>
#include <systemc.h>

struct SystemCStepResult {
    uint32_t pc;
    uint32_t insn;
    uint32_t rd;
    uint32_t rd_value;
    bool     trap;
};

class SystemCOracle {
public:
    explicit SystemCOracle(const std::string& elf_path);
    ~SystemCOracle();

    // Step until an instruction retires (rvvi_valid goes high)
    // Returns the RVVI state at retirement
    SystemCStepResult step();

    // Read architectural register (via committed RAT + PRF)
    uint32_t get_xreg(int i) const;

    // Get current PC
    uint32_t get_pc() const;

    // Reset the model
    void reset(int cycles = 5);

private:
    // SystemC signals - opaque to avoid pulling in generated headers
    struct Impl;
    std::unique_ptr<Impl> impl_;
};

#endif // HAS_SYSTEMC
