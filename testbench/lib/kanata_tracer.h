//==============================================================================
// kanata_tracer.h - Kanata pipeline trace output for Konata viewer
//
// Generates a Kanata log file showing instruction flow through the
// Tomasulo OoO pipeline: F→D→Rn→Is→Xec→Cm→Rt
//
// Usage:
//   KanataTracer tracer("trace.log");
//   // each rising edge:
//   tracer.tick(cycle, signals);
//==============================================================================
#ifndef KANATA_TRACER_H
#define KANATA_TRACER_H

#include <cstdint>
#include <cstdio>
#include <array>

class KanataTracer {
public:
    // Signals sampled each cycle from RTL
    struct Signals {
        bool     alloc_valid;      // ROB tail write enable (new instruction allocated)
        uint32_t alloc_idx;        // ROB tail pointer (4-bit, 0-15)
        uint32_t alloc_physrd;     // Physical dest reg at alloc (6-bit)
        bool     cdb_valid;        // CDB broadcast (execution complete)
        uint32_t cdb_tag;          // CDB physical register tag (6-bit)
        bool     flush;            // pipeline_flush_comb
        bool     commit_valid;     // rvvi_valid (instruction retired)
        uint32_t head_idx;         // ROB head pointer (4-bit)
        uint32_t commit_pc;        // rvvi_pc_rdata
        uint32_t commit_insn;      // rvvi_insn
        // RS dispatch signals (5 functional units)
        struct { bool valid; uint32_t tag; } dispatch[5];
    };

    explicit KanataTracer(const char* filename);
    ~KanataTracer();
    KanataTracer(const KanataTracer&) = delete;
    KanataTracer& operator=(const KanataTracer&) = delete;

    bool is_open() const { return fp_ != nullptr; }

    // Call once per rising edge
    void tick(uint64_t cycle, const Signals& sig);

private:
    FILE* fp_;
    uint64_t next_id_;
    uint64_t last_cycle_;

    static constexpr int ROB_SIZE = 16;
    static constexpr int PHYS_REGS = 64;

    // Stage tracking — each stage lasts at least 1 cycle
    enum Stage : uint8_t {
        STAGE_NONE = 0,
        STAGE_FETCH,     // F  — synthetic (1 cycle before alloc observation)
        STAGE_DECODE,    // D  — synthetic (alloc cycle)
        STAGE_RENAME,    // Rn — rename/dispatch
        STAGE_ISSUE,     // Is — waiting in RS for operands
        STAGE_EXECUTE,   // Xec — executing (CDB fires at end)
        STAGE_COMPLETE,  // Cm — waiting for in-order commit
        STAGE_RETIRE,    // Rt — commit done, draining
        STAGE_DONE       // fully retired
    };

    struct RobEntry {
        uint64_t kanata_id;
        uint32_t physrd;
        Stage    stage;
        bool     active;
        bool     cdb_seen;      // CDB has fired for this instruction
        bool     commit_seen;   // commit has fired (may still be progressing visually)
        bool     dispatch_seen; // RS dispatch fired (may still be in frontend stages)
    };

    std::array<RobEntry, ROB_SIZE> rob_;
    std::array<uint64_t, PHYS_REGS> phys_to_kanata_;

    static const char* stage_name(Stage s);
    void advance_stages();
    void emit_flush();
};

#endif // KANATA_TRACER_H
