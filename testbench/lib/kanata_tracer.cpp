//==============================================================================
// kanata_tracer.cpp - Kanata pipeline trace implementation
//
// Stage machine with deferred event flags:
//   Auto-advance (1 cycle each): F→D, D→Rn, Rn→Is, Rt→done
//   Is→Xec: auto-advances when dispatch_seen is set
//   Xec→Cm: immediate on CDB, or auto-advances when cdb_seen/commit_seen
//   Cm→Rt:  immediate on commit, or auto-advances when commit_seen
//
// Events set flags; the stage machine advances naturally so every stage
// gets at least 1 cycle of visual width in Konata.
//==============================================================================

#include "kanata_tracer.h"
#include "rv32_disasm.h"

const char* KanataTracer::stage_name(Stage s) {
    switch (s) {
        case STAGE_FETCH:    return "F";
        case STAGE_DECODE:   return "D";
        case STAGE_RENAME:   return "Rn";
        case STAGE_ISSUE:    return "Is";
        case STAGE_EXECUTE:  return "Xec";
        case STAGE_COMPLETE: return "Cm";
        case STAGE_RETIRE:   return "Rt";
        default:             return "?";
    }
}

KanataTracer::KanataTracer(const char* filename)
    : fp_(nullptr), next_id_(0), last_cycle_(0)
{
    fp_ = fopen(filename, "w");
    if (!fp_) {
        fprintf(stderr, "KanataTracer: cannot open %s\n", filename);
        return;
    }
    fprintf(fp_, "Kanata\t0004\n");

    rob_.fill({0, 0, STAGE_NONE, false, false, false, false});
    phys_to_kanata_.fill(0);
}

KanataTracer::~KanataTracer() {
    if (fp_) fclose(fp_);
}

// Auto-advance stages. Each stage gets at least 1 cycle of visual width.
// Flags (dispatch_seen, cdb_seen, commit_seen) unlock "wait" stages:
//   Is waits until dispatch_seen or commit_seen
//   Cm waits until commit_seen
void KanataTracer::advance_stages() {
    for (int i = 0; i < ROB_SIZE; i++) {
        auto& e = rob_[i];
        if (!e.active) continue;

        Stage next = STAGE_NONE;
        switch (e.stage) {
            case STAGE_FETCH:    next = STAGE_DECODE;   break;
            case STAGE_DECODE:   next = STAGE_RENAME;   break;
            case STAGE_RENAME:   next = STAGE_ISSUE;    break;
            case STAGE_ISSUE:
                if (e.dispatch_seen || e.commit_seen) next = STAGE_EXECUTE;
                break;
            case STAGE_EXECUTE:
                if (e.cdb_seen || e.commit_seen) next = STAGE_COMPLETE;
                break;
            case STAGE_COMPLETE:
                if (e.commit_seen) next = STAGE_RETIRE;
                break;
            case STAGE_RETIRE:   next = STAGE_DONE;     break;
            default: break;
        }

        if (next == STAGE_DONE) {
            fprintf(fp_, "E\t%lu\t0\tRt\n", (unsigned long)e.kanata_id);
            fprintf(fp_, "R\t%lu\t%lu\t0\n", (unsigned long)e.kanata_id, (unsigned long)e.kanata_id);
            e.active = false;
            e.stage = STAGE_DONE;
        } else if (next != STAGE_NONE) {
            fprintf(fp_, "E\t%lu\t0\t%s\n", (unsigned long)e.kanata_id, stage_name(e.stage));
            e.stage = next;
            fprintf(fp_, "S\t%lu\t0\t%s\n", (unsigned long)e.kanata_id, stage_name(next));
        }
    }
}

void KanataTracer::tick(uint64_t cycle, const Signals& sig) {
    if (!fp_) return;

    // Emit cycle advance
    if (cycle > last_cycle_) {
        uint64_t delta = cycle - last_cycle_;
        fprintf(fp_, "C\t%lu\n", (unsigned long)delta);
        last_cycle_ = cycle;
    }

    // Process flush first
    if (sig.flush) {
        emit_flush();
    }

    // Advance auto-transitioning stages
    advance_stages();

    // Handle RS dispatch: set dispatch_seen flag.
    // If instruction is already in Is, immediately transition Is→Xec.
    // If still in F/D/Rn, the flag ensures Is→Xec happens when Is is reached.
    for (int d = 0; d < 5; d++) {
        if (sig.dispatch[d].valid && sig.dispatch[d].tag < PHYS_REGS) {
            uint64_t id = phys_to_kanata_[sig.dispatch[d].tag];
            for (int i = 0; i < ROB_SIZE; i++) {
                if (rob_[i].active && rob_[i].kanata_id == id &&
                    rob_[i].stage >= STAGE_FETCH && rob_[i].stage <= STAGE_ISSUE) {
                    rob_[i].dispatch_seen = true;
                    // If already in Is, immediately transition
                    if (rob_[i].stage == STAGE_ISSUE) {
                        fprintf(fp_, "E\t%lu\t0\tIs\n", (unsigned long)id);
                        rob_[i].stage = STAGE_EXECUTE;
                        fprintf(fp_, "S\t%lu\t0\tXec\n", (unsigned long)id);
                    }
                    break;
                }
            }
        }
    }

    // Handle CDB broadcast: set cdb_seen flag.
    // If instruction is in Xec, immediately transition Xec→Cm.
    // If still in earlier stage, flag ensures Xec→Cm when Xec is reached.
    if (sig.cdb_valid && sig.cdb_tag < PHYS_REGS) {
        uint64_t id = phys_to_kanata_[sig.cdb_tag];
        for (int i = 0; i < ROB_SIZE; i++) {
            if (rob_[i].active && rob_[i].kanata_id == id &&
                rob_[i].stage >= STAGE_FETCH && rob_[i].stage <= STAGE_EXECUTE) {
                rob_[i].cdb_seen = true;
                rob_[i].dispatch_seen = true; // CDB implies dispatch happened
                if (rob_[i].stage == STAGE_EXECUTE) {
                    fprintf(fp_, "E\t%lu\t0\tXec\n", (unsigned long)id);
                    rob_[i].stage = STAGE_COMPLETE;
                    fprintf(fp_, "S\t%lu\t0\tCm\n", (unsigned long)id);
                }
                break;
            }
        }
    }

    // Handle commit: set commit_seen + label update.
    // If instruction is in Cm, immediately transition Cm→Rt.
    // Otherwise flag ensures auto-advance through remaining stages.
    if (sig.commit_valid && sig.head_idx < ROB_SIZE) {
        auto& e = rob_[sig.head_idx];
        if (e.active) {
            uint64_t id = e.kanata_id;

            std::string dis = rv32_disasm::disasm(sig.commit_insn);
            fprintf(fp_, "L\t%lu\t0\t%08x: %s\n", (unsigned long)id, sig.commit_pc, dis.c_str());

            e.commit_seen = true;

            if (e.stage == STAGE_COMPLETE) {
                // Normal: CDB already fired, instruction waiting for commit
                fprintf(fp_, "E\t%lu\t0\tCm\n", (unsigned long)id);
                e.stage = STAGE_RETIRE;
                fprintf(fp_, "S\t%lu\t0\tRt\n", (unsigned long)id);
            }
            // Otherwise: stage machine will auto-advance through remaining
            // stages (1 cycle each) via the commit_seen flag.
        }
    }

    // Handle new allocation: create instruction, start F
    if (sig.alloc_valid) {
        uint64_t id = next_id_++;
        uint32_t idx = sig.alloc_idx % ROB_SIZE;

        fprintf(fp_, "I\t%lu\t0\t0\n", (unsigned long)id);
        fprintf(fp_, "L\t%lu\t0\tROB[%u] p%u\n", (unsigned long)id, idx, sig.alloc_physrd);
        fprintf(fp_, "S\t%lu\t0\tF\n", (unsigned long)id);

        rob_[idx] = {id, sig.alloc_physrd, STAGE_FETCH, true, false, false, false};

        if (sig.alloc_physrd < PHYS_REGS) {
            phys_to_kanata_[sig.alloc_physrd] = id;
        }
    }
}

void KanataTracer::emit_flush() {
    for (int i = 0; i < ROB_SIZE; i++) {
        if (rob_[i].active && rob_[i].stage != STAGE_RETIRE && rob_[i].stage != STAGE_DONE) {
            uint64_t id = rob_[i].kanata_id;
            fprintf(fp_, "E\t%lu\t0\t%s\n", (unsigned long)id, stage_name(rob_[i].stage));
            fprintf(fp_, "R\t%lu\t%lu\t1\n", (unsigned long)id, (unsigned long)id);
            rob_[i].active = false;
            rob_[i].stage = STAGE_NONE;
        }
    }
}
