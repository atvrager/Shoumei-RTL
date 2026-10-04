#include "spike_oracle.h"

#include <riscv/processor.h>
#include <riscv/mmu.h>
#include <riscv/simif.h>
#include <riscv/cfg.h>
#include <riscv/csrs.h>

#include <vector>
#include <map>
#include <cstring>
#include <cstdio>
#include <elf.h>

// Custom simif_t that provides flat memory at address 0x0
// Avoids sim_t's debug module / boot ROM conflicts
class flat_simif_t : public simif_t {
public:
    static constexpr size_t MEM_SIZE = 0x40000; // 256KB (matches RTL memSizeWords=65536)

    // UART transmit register.  The RTL harness accepts stores here and prints
    // the byte, so the reference model must accept them too; without this the
    // store faults and the two models diverge at the first character written.
    static constexpr reg_t UART_BASE = 0x10000000;
    static constexpr reg_t UART_SIZE = 0x100;

    // CLINT region, machine timer only.
    static constexpr reg_t CLINT_BASE = 0x02000000;
    static constexpr reg_t CLINT_SIZE = 0x00010000;

    explicit flat_simif_t(cfg_t* cfg) : cfg_(cfg), mem_(MEM_SIZE, 0) {}

    char* addr_to_mem(reg_t paddr) override {
        if (paddr < MEM_SIZE)
            return &mem_[paddr];
        return nullptr;
    }

    static bool is_uart(reg_t addr) {
        return addr >= UART_BASE && addr < UART_BASE + UART_SIZE;
    }

    // CLINT region (0x02000000-0x0200FFFF): accept loads/stores silently
    bool mmio_load(reg_t addr, size_t len, uint8_t* bytes) override {
        if (is_uart(addr)) {
            uint32_t zero = 0;
            memcpy(bytes, &zero, len);
            return true;
        }
        if (addr >= CLINT_BASE && addr < CLINT_BASE + CLINT_SIZE) {
            // Return CLINT register values
            uint64_t val = 0;
            if (addr == 0x0200BFF8) {
                if (len == 8) val = mtime_;
                else val = mtime_ & 0xFFFFFFFF;
            } else if (addr == 0x0200BFFC) {
                val = (mtime_ >> 32);
            } else if (addr == 0x02004000) {
                if (len == 8) val = mtimecmp_;
                else val = mtimecmp_ & 0xFFFFFFFF;
            } else if (addr == 0x02004004) {
                val = (mtimecmp_ >> 32);
            }
            memcpy(bytes, &val, len);
            return true;
        }
        return false;
    }
    bool mmio_store(reg_t addr, size_t len, const uint8_t* bytes) override {
        if (is_uart(addr)) {
            return true;  // Discarded; the cosim logs the RTL's UART writes.
        }
        if (addr >= CLINT_BASE && addr < CLINT_BASE + CLINT_SIZE) {
            if (len == 8) {
                if (addr == 0x02004000) memcpy(&mtimecmp_, bytes, 8);
                else if (addr == 0x0200BFF8) memcpy(&mtime_, bytes, 8);
            } else {
                uint32_t val = 0;
                memcpy(&val, bytes, std::min(len, sizeof(val)));
                if (addr == 0x02004000) mtimecmp_ = (mtimecmp_ & 0xFFFFFFFF00000000ULL) | val;
                else if (addr == 0x02004004) mtimecmp_ = (mtimecmp_ & 0xFFFFFFFF) | ((uint64_t)val << 32);
                else if (addr == 0x0200BFF8) mtime_ = (mtime_ & 0xFFFFFFFF00000000ULL) | val;
                else if (addr == 0x0200BFFC) mtime_ = (mtime_ & 0xFFFFFFFF) | ((uint64_t)val << 32);
            }
            return true;
        }
        return false;
    }

    // Tick mtime and return whether mtip changed
    bool tick_timer() {
        mtime_++;
        bool new_mtip = (mtime_ >= mtimecmp_);
        bool changed = (new_mtip != mtip_);
        mtip_ = new_mtip;
        return changed;
    }
    bool get_mtip() const { return mtip_; }
    void proc_reset(unsigned) override {}
    const cfg_t& get_cfg() const override { return *cfg_; }
    const std::map<size_t, processor_t*>& get_harts() const override { return harts_; }
    const char* get_symbol(uint64_t) override { return nullptr; }

    void register_hart(size_t id, processor_t* p) { harts_[id] = p; }

    // Load ELF segments into flat memory (supports both ELF32 and ELF64)
    int load_elf(const char* path) {
        FILE* f = fopen(path, "rb");
        if (!f) return -1;

        unsigned char e_ident[EI_NIDENT];
        if (fread(e_ident, 1, EI_NIDENT, f) != EI_NIDENT) {
            fclose(f);
            return -1;
        }
        fseek(f, 0, SEEK_SET);

        if (e_ident[EI_CLASS] == ELFCLASS64) {
            Elf64_Ehdr ehdr;
            if (fread(&ehdr, sizeof(ehdr), 1, f) != 1) { fclose(f); return -1; }

            for (int i = 0; i < ehdr.e_phnum; i++) {
                Elf64_Phdr phdr;
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
        } else if (e_ident[EI_CLASS] == ELFCLASS32) {
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
        } else {
            fclose(f);
            return -1;
        }
        fclose(f);
        return 0;
    }

private:
    cfg_t* cfg_;
    std::map<size_t, processor_t*> harts_;
    std::vector<char> mem_;
    uint64_t mtime_ = 0;
    uint64_t mtimecmp_ = 0xFFFFFFFFFFFFFFFFULL;
    bool mtip_ = false;
};

SpikeOracle::SpikeOracle(const std::string& elf_path, const std::string& isa)
    : isa_storage_(isa), cfg_(std::make_unique<cfg_t>()) {
    cfg_->isa = isa_storage_.c_str();
    cfg_->priv = "m";
    cfg_->hartids = {0};
    cfg_->start_pc = 0;

    auto* flat = new flat_simif_t(cfg_.get());
    flat->load_elf(elf_path.c_str());
    simif_.reset(flat);

    bool want_log = getenv("SPIKE_LOG_COMMITS") != nullptr;
    proc_ = std::make_unique<processor_t>(
        cfg_->isa, cfg_->priv, cfg_.get(), simif_.get(),
        /*hartid=*/0, /*halted=*/false, /*log_file=*/want_log ? stderr : nullptr,
        /*sout=*/std::cerr);
    if (want_log) {
        proc_->enable_log_commits();
    }

    flat->register_hart(0, proc_.get());
    proc_->get_state()->pc = 0;

    // Enable FP if ISA includes F or D extension
    if (isa.find('f') != std::string::npos || isa.find('F') != std::string::npos ||
        isa.find('d') != std::string::npos || isa.find('D') != std::string::npos) {
        // Set MSTATUS.FS = Dirty (bits 14:13 = 11)
        // Without this, Spike traps on any FP instruction with illegal-insn
        proc_->put_csr(/*CSR_MSTATUS*/ 0x300,
                       proc_->get_csr(/*CSR_MSTATUS*/ 0x300) | 0x6000);
    }
}

SpikeOracle::~SpikeOracle() = default;

SpikeStepResult SpikeOracle::step() {
    SpikeStepResult r = {};
    r.pc = static_cast<uint64_t>(proc_->get_state()->pc);

    uint64_t regs_before[32];
    for (int i = 0; i < 32; i++)
        regs_before[i] = static_cast<uint64_t>(proc_->get_state()->XPR[i]);

    try {
        r.insn = static_cast<uint32_t>(
            proc_->get_mmu()->load<uint32_t>(r.pc));
    } catch (...) {
        r.insn = 0;
    }

    // Save rs1 value before step (for CLINT load detection)
    uint32_t rs1_idx = (r.insn >> 15) & 0x1f;
    r.rs1_value = regs_before[rs1_idx];

    // Save FP source operands before step.  The fused multiply-add family
    // reads three: rs1, rs2 and the addend in bits[31:27].
    bool is_fma = (r.insn & 0x7f) == 0x43 || (r.insn & 0x7f) == 0x47
               || (r.insn & 0x7f) == 0x4B || (r.insn & 0x7f) == 0x4F;
    bool is_opfp = (r.insn & 0x7f) == 0x53;
    if (is_fma || is_opfp) {
        uint32_t fs1 = (r.insn >> 15) & 0x1f;
        uint32_t fs2 = (r.insn >> 20) & 0x1f;
        r.fs1_value = static_cast<uint64_t>(proc_->get_state()->FPR[fs1].v[0]);
        r.fs2_value = static_cast<uint64_t>(proc_->get_state()->FPR[fs2].v[0]);
        if (is_fma) {
            uint32_t fs3 = (r.insn >> 27) & 0x1f;
            r.fs3_value = static_cast<uint64_t>(proc_->get_state()->FPR[fs3].v[0]);
        }
    }

    try {
        proc_->step(1);
        r.trap = false;
    } catch (...) {
        r.trap = true;
    }

    // Decode integer rd from bits[11:7] only for opcodes that write an integer
    // register.  FP ops, stores, and branches all have non-zero bits[11:7] but
    // do not write an integer destination; reading XPR for those produces a
    // spurious diff in the trace.
    // Opcodes that write an integer destination register.
    // Low group fits in a 64-bit bitmask (opcodes 0x00..0x3F).
    // High group (JALR=0x67, JAL=0x6F, SYSTEM=0x73) checked explicitly.
    static constexpr uint64_t INT_RD_LOW =
        (1ull << 0x03) |  // LOAD
        (1ull << 0x13) |  // OP-IMM
        (1ull << 0x17) |  // AUIPC
        (1ull << 0x1B) |  // OP-IMM-32
        (1ull << 0x2F) |  // AMO
        (1ull << 0x33) |  // OP
        (1ull << 0x37) |  // LUI
        (1ull << 0x3B);   // OP-32
    uint32_t opcode  = r.insn & 0x7f;
    uint32_t rd_idx  = (r.insn >> 7) & 0x1f;
    // OP-FP (0x53): only certain funct7 values write an integer rd.
    // funct7 0x50-0x55 = comparisons (feq/flt/fle), 0x60-0x61 = fcvt->int,
    // 0x70-0x71 = fmv.x.w/d and fclass.  All others write an FP destination.
    uint32_t funct7 = r.insn >> 25;
    bool fp_writes_int = (opcode == 0x53) &&
        ((funct7 >= 0x50 && funct7 <= 0x55) || // comparisons
         (funct7 == 0x60 || funct7 == 0x61)  || // fcvt->int
         (funct7 == 0x70 || funct7 == 0x71));   // fmv.x, fclass
    bool writes_xrd  = ((opcode < 64) && ((INT_RD_LOW >> opcode) & 1ull))
                    || fp_writes_int
                    || (opcode == 0x67)   // JALR
                    || (opcode == 0x6F)   // JAL
                    || (opcode == 0x73);  // SYSTEM (CSR)
    if (writes_xrd && rd_idx != 0) {
        r.rd       = rd_idx;
        r.rd_value = static_cast<uint64_t>(proc_->get_state()->XPR[rd_idx]);
    }
    // Detect FP destination writes.  The destination is named by the
    // instruction, not inferred from a change of value: a rewrite of the value
    // the register already holds must still be reported, or the trace check
    // skips it and the RTL's write is never compared.
    uint32_t fp_op = r.insn & 0x7f;
    bool writes_frd = (fp_op == 0x07)                        // FLW, FLD
                   || (fp_op == 0x43 || fp_op == 0x47
                    || fp_op == 0x4B || fp_op == 0x4F)       // FMADD..FNMSUB
                   || (fp_op == 0x53 && !fp_writes_int);     // OP-FP
    r.frd_valid = false;
    if (writes_frd) {
        r.frd = rd_idx;
        r.frd_value = static_cast<uint64_t>(proc_->get_state()->FPR[rd_idx].v[0]);
        r.frd_valid = true;
    }

    // Read accumulated fflags (CSR 0x001)
    r.fflags = static_cast<uint32_t>(proc_->get_csr(0x001)) & 0x1F;

    return r;
}

uint64_t SpikeOracle::get_xreg(int i) const {
    return static_cast<uint64_t>(proc_->get_state()->XPR[i]);
}

void SpikeOracle::set_xreg(int i, uint64_t val) {
    if (i != 0) proc_->get_state()->XPR.write(i, val);
}

uint64_t SpikeOracle::get_freg(int i) const {
    return static_cast<uint64_t>(proc_->get_state()->FPR[i].v[0]);
}

uint64_t SpikeOracle::get_freg_hi(int i) const {
    return static_cast<uint64_t>(proc_->get_state()->FPR[i].v[1]);
}

void SpikeOracle::set_freg(int i, uint64_t val) {
    proc_->get_state()->FPR.write(i, freg_t{val, 0});
}

uint64_t SpikeOracle::get_csr(int which) const {
    return static_cast<uint64_t>(proc_->get_csr(which));
}

uint64_t SpikeOracle::get_pc() const {
    return static_cast<uint64_t>(proc_->get_state()->pc);
}

void SpikeOracle::set_pc(uint64_t pc) {
    proc_->get_state()->pc = pc;
}

uint32_t SpikeOracle::get_insn_at(uint64_t addr) const {
    return static_cast<uint32_t>(proc_->get_mmu()->load<uint32_t>(addr));
}

uint32_t SpikeOracle::read_mem(uint64_t addr) const {
    char* p = simif_->addr_to_mem(addr);
    if (p == nullptr)
        return 0;
    uint32_t word = 0;
    memcpy(&word, p, sizeof(word));
    return word;
}

void SpikeOracle::unhalt() {
    proc_->clear_waiting_for_interrupt();
}

SpikeOracle::ArchState SpikeOracle::save_state() const {
    ArchState s;
    s.pc = static_cast<uint64_t>(proc_->get_state()->pc);
    for (int i = 0; i < 32; i++)
        s.xregs[i] = static_cast<uint64_t>(proc_->get_state()->XPR[i]);
    for (int i = 0; i < 32; i++)
        s.fregs[i] = proc_->get_state()->FPR[i].v[0];
    return s;
}

void SpikeOracle::restore_state(const ArchState& s) {
    proc_->get_state()->pc = s.pc;
    for (int i = 1; i < 32; i++)
        proc_->get_state()->XPR.write(i, s.xregs[i]);
    for (int i = 0; i < 32; i++) {
        freg_t f; f.v[0] = s.fregs[i]; f.v[1] = 0;
        proc_->get_state()->FPR.write(i, f);
    }
}

void SpikeOracle::tick_timer() {
    auto* flat = static_cast<flat_simif_t*>(simif_.get());
    flat->tick_timer();
    set_mip_mtip(flat->get_mtip());
}

void SpikeOracle::set_mip_mtip(bool val) {
    // MIP.MTIP (bit 7) is read-only via CSR writes; use backdoor
    proc_->get_state()->mip->backdoor_write_with_mask(1ULL << 7, val ? (1ULL << 7) : 0);
}
