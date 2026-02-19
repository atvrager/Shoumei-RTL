//==============================================================================
// rv32_disasm.h - Lightweight RV32IMF_Zicsr_Zifencei disassembler
//
// Header-only. Returns human-readable disassembly strings for Kanata trace
// labels and debug output.
//
// Covers: RV32I base, M (mul/div), F (single-precision float),
//         Zicsr (csrrw/csrrs/csrrc/csrrwi/csrrsi/csrrci),
//         Zifencei (fence.i)
//==============================================================================
#ifndef RV32_DISASM_H
#define RV32_DISASM_H

#include <cstdint>
#include <cstdio>
#include <string>

namespace rv32_disasm {

// ABI register names
static const char* const x_names[32] = {
    "zero","ra","sp","gp","tp","t0","t1","t2",
    "s0","s1","a0","a1","a2","a3","a4","a5",
    "a6","a7","s2","s3","s4","s5","s6","s7",
    "s8","s9","s10","s11","t3","t4","t5","t6"
};
static const char* const f_names[32] = {
    "ft0","ft1","ft2","ft3","ft4","ft5","ft6","ft7",
    "fs0","fs1","fa0","fa1","fa2","fa3","fa4","fa5",
    "fa6","fa7","fs2","fs3","fs4","fs5","fs6","fs7",
    "fs8","fs9","fs10","fs11","ft8","ft9","ft10","ft11"
};

// Well-known CSR names
static inline const char* csr_name(uint32_t csr) {
    switch (csr) {
        case 0x001: return "fflags";
        case 0x002: return "frm";
        case 0x003: return "fcsr";
        case 0x300: return "mstatus";
        case 0x301: return "misa";
        case 0x304: return "mie";
        case 0x305: return "mtvec";
        case 0x340: return "mscratch";
        case 0x341: return "mepc";
        case 0x342: return "mcause";
        case 0x343: return "mtval";
        case 0x344: return "mip";
        case 0xB00: return "mcycle";
        case 0xB02: return "minstret";
        case 0xC00: return "cycle";
        case 0xC01: return "time";
        case 0xC02: return "instret";
        case 0xF11: return "mvendorid";
        case 0xF12: return "marchid";
        case 0xF13: return "mimpid";
        case 0xF14: return "mhartid";
        default: return nullptr;
    }
}

static inline std::string csr_str(uint32_t csr) {
    const char* n = csr_name(csr);
    if (n) return n;
    char buf[16];
    snprintf(buf, sizeof(buf), "0x%03x", csr);
    return buf;
}

// Extract fields
static inline uint32_t rd(uint32_t insn)  { return (insn >> 7) & 0x1F; }
static inline uint32_t rs1(uint32_t insn) { return (insn >> 15) & 0x1F; }
static inline uint32_t rs2(uint32_t insn) { return (insn >> 20) & 0x1F; }
static inline uint32_t rs3(uint32_t insn) { return (insn >> 27) & 0x1F; }
static inline uint32_t funct3(uint32_t insn) { return (insn >> 12) & 0x7; }
static inline uint32_t funct7(uint32_t insn) { return (insn >> 25) & 0x7F; }
static inline uint32_t opcode(uint32_t insn) { return insn & 0x7F; }

// Immediates (sign-extended)
static inline int32_t imm_i(uint32_t insn) { return (int32_t)insn >> 20; }
static inline int32_t imm_s(uint32_t insn) {
    return (int32_t)(((insn >> 25) << 5) | ((insn >> 7) & 0x1F)) << 20 >> 20;
}
static inline int32_t imm_b(uint32_t insn) {
    uint32_t v = (((insn >> 31) & 1) << 12) |
                 (((insn >> 7) & 1) << 11) |
                 (((insn >> 25) & 0x3F) << 5) |
                 (((insn >> 8) & 0xF) << 1);
    return (int32_t)(v << 19) >> 19;
}
static inline int32_t imm_u(uint32_t insn) { return (int32_t)(insn & 0xFFFFF000); }
static inline int32_t imm_j(uint32_t insn) {
    uint32_t v = (((insn >> 31) & 1) << 20) |
                 (((insn >> 12) & 0xFF) << 12) |
                 (((insn >> 20) & 1) << 11) |
                 (((insn >> 21) & 0x3FF) << 1);
    return (int32_t)(v << 11) >> 11;
}

// Rounding mode names for F extension
static inline const char* rm_name(uint32_t rm) {
    switch (rm) {
        case 0: return "rne"; case 1: return "rtz"; case 2: return "rdn";
        case 3: return "rup"; case 4: return "rmm"; case 7: return "dyn";
        default: return "?rm";
    }
}

static inline std::string disasm(uint32_t insn) {
    char buf[80];
    uint32_t op = opcode(insn);
    uint32_t f3 = funct3(insn);
    uint32_t f7 = funct7(insn);

    auto xd = x_names[rd(insn)];
    auto x1 = x_names[rs1(insn)];
    auto x2 = x_names[rs2(insn)];
    auto fd = f_names[rd(insn)];
    auto f1 = f_names[rs1(insn)];
    auto f2 = f_names[rs2(insn)];
    auto f3r = f_names[rs3(insn)];

    switch (op) {
    case 0x37: // LUI
        snprintf(buf, sizeof(buf), "lui %s, 0x%x", xd, (uint32_t)imm_u(insn) >> 12);
        return buf;
    case 0x17: // AUIPC
        snprintf(buf, sizeof(buf), "auipc %s, 0x%x", xd, (uint32_t)imm_u(insn) >> 12);
        return buf;
    case 0x6F: // JAL
        if (rd(insn) == 0)
            snprintf(buf, sizeof(buf), "j %d", imm_j(insn));
        else
            snprintf(buf, sizeof(buf), "jal %s, %d", xd, imm_j(insn));
        return buf;
    case 0x67: // JALR
        if (rd(insn) == 0 && rs1(insn) == 1 && imm_i(insn) == 0)
            return "ret";
        snprintf(buf, sizeof(buf), "jalr %s, %s, %d", xd, x1, imm_i(insn));
        return buf;
    case 0x63: { // B-type
        const char* names[] = {"beq","bne","?b2","?b3","blt","bge","bltu","bgeu"};
        snprintf(buf, sizeof(buf), "%s %s, %s, %d", names[f3], x1, x2, imm_b(insn));
        return buf;
    }
    case 0x03: { // Loads
        const char* names[] = {"lb","lh","lw","?l3","lbu","lhu","?l6","?l7"};
        snprintf(buf, sizeof(buf), "%s %s, %d(%s)", names[f3], xd, imm_i(insn), x1);
        return buf;
    }
    case 0x23: { // Stores
        const char* names[] = {"sb","sh","sw","?s3","?s4","?s5","?s6","?s7"};
        snprintf(buf, sizeof(buf), "%s %s, %d(%s)", names[f3], x2, imm_s(insn), x1);
        return buf;
    }
    case 0x13: { // I-type ALU
        int32_t imm = imm_i(insn);
        if (insn == 0x00000013) return "nop";
        if (f3 == 0 && rs1(insn) == 0)
            { snprintf(buf, sizeof(buf), "li %s, %d", xd, imm); return buf; }
        if (f3 == 0 && imm == 0)
            { snprintf(buf, sizeof(buf), "mv %s, %s", xd, x1); return buf; }
        const char* names[] = {"addi","slli","slti","sltiu","xori","srli","ori","andi"};
        if (f3 == 1) { snprintf(buf, sizeof(buf), "slli %s, %s, %u", xd, x1, rs2(insn)); return buf; }
        if (f3 == 5 && f7 == 0x20) { snprintf(buf, sizeof(buf), "srai %s, %s, %u", xd, x1, rs2(insn)); return buf; }
        if (f3 == 5) { snprintf(buf, sizeof(buf), "srli %s, %s, %u", xd, x1, rs2(insn)); return buf; }
        snprintf(buf, sizeof(buf), "%s %s, %s, %d", names[f3], xd, x1, imm);
        return buf;
    }
    case 0x33: { // R-type ALU
        if (f7 == 0x01) { // M extension
            const char* names[] = {"mul","mulh","mulhsu","mulhu","div","divu","rem","remu"};
            snprintf(buf, sizeof(buf), "%s %s, %s, %s", names[f3], xd, x1, x2);
            return buf;
        }
        if (f7 == 0x20 && f3 == 0) { snprintf(buf, sizeof(buf), "sub %s, %s, %s", xd, x1, x2); return buf; }
        if (f7 == 0x20 && f3 == 5) { snprintf(buf, sizeof(buf), "sra %s, %s, %s", xd, x1, x2); return buf; }
        const char* names[] = {"add","sll","slt","sltu","xor","srl","or","and"};
        snprintf(buf, sizeof(buf), "%s %s, %s, %s", names[f3], xd, x1, x2);
        return buf;
    }
    case 0x0F: // FENCE / FENCE.I
        if (f3 == 1) return "fence.i";
        return "fence";
    case 0x73: { // SYSTEM
        if (insn == 0x00000073) return "ecall";
        if (insn == 0x00100073) return "ebreak";
        if (insn == 0x30200073) return "mret";
        if (insn == 0x10500073) return "wfi";
        // CSR instructions
        uint32_t csr = insn >> 20;
        auto cs = csr_str(csr);
        if (f3 == 1) { snprintf(buf, sizeof(buf), "csrrw %s, %s, %s", xd, cs.c_str(), x1); return buf; }
        if (f3 == 2) { snprintf(buf, sizeof(buf), "csrrs %s, %s, %s", xd, cs.c_str(), x1); return buf; }
        if (f3 == 3) { snprintf(buf, sizeof(buf), "csrrc %s, %s, %s", xd, cs.c_str(), x1); return buf; }
        if (f3 == 5) { snprintf(buf, sizeof(buf), "csrrwi %s, %s, %u", xd, cs.c_str(), rs1(insn)); return buf; }
        if (f3 == 6) { snprintf(buf, sizeof(buf), "csrrsi %s, %s, %u", xd, cs.c_str(), rs1(insn)); return buf; }
        if (f3 == 7) { snprintf(buf, sizeof(buf), "csrrci %s, %s, %u", xd, cs.c_str(), rs1(insn)); return buf; }
        break;
    }
    // === F extension ===
    case 0x07: // FLW
        if (f3 == 2) { snprintf(buf, sizeof(buf), "flw %s, %d(%s)", fd, imm_i(insn), x1); return buf; }
        break;
    case 0x27: // FSW
        if (f3 == 2) { snprintf(buf, sizeof(buf), "fsw %s, %d(%s)", f2, imm_s(insn), x1); return buf; }
        break;
    case 0x43: // FMADD.S
        snprintf(buf, sizeof(buf), "fmadd.s %s, %s, %s, %s", fd, f1, f2, f3r);
        return buf;
    case 0x47: // FMSUB.S
        snprintf(buf, sizeof(buf), "fmsub.s %s, %s, %s, %s", fd, f1, f2, f3r);
        return buf;
    case 0x4B: // FNMSUB.S
        snprintf(buf, sizeof(buf), "fnmsub.s %s, %s, %s, %s", fd, f1, f2, f3r);
        return buf;
    case 0x4F: // FNMADD.S
        snprintf(buf, sizeof(buf), "fnmadd.s %s, %s, %s, %s", fd, f1, f2, f3r);
        return buf;
    case 0x53: { // F-type arithmetic
        switch (f7) {
        case 0x00: snprintf(buf, sizeof(buf), "fadd.s %s, %s, %s", fd, f1, f2); return buf;
        case 0x04: snprintf(buf, sizeof(buf), "fsub.s %s, %s, %s", fd, f1, f2); return buf;
        case 0x08: snprintf(buf, sizeof(buf), "fmul.s %s, %s, %s", fd, f1, f2); return buf;
        case 0x0C: snprintf(buf, sizeof(buf), "fdiv.s %s, %s, %s", fd, f1, f2); return buf;
        case 0x2C: snprintf(buf, sizeof(buf), "fsqrt.s %s, %s", fd, f1); return buf;
        case 0x10:
            if (f3 == 0) { snprintf(buf, sizeof(buf), "fsgnj.s %s, %s, %s", fd, f1, f2); return buf; }
            if (f3 == 1) { snprintf(buf, sizeof(buf), "fsgnjn.s %s, %s, %s", fd, f1, f2); return buf; }
            if (f3 == 2) { snprintf(buf, sizeof(buf), "fsgnjx.s %s, %s, %s", fd, f1, f2); return buf; }
            break;
        case 0x14:
            if (f3 == 0) { snprintf(buf, sizeof(buf), "fmin.s %s, %s, %s", fd, f1, f2); return buf; }
            if (f3 == 1) { snprintf(buf, sizeof(buf), "fmax.s %s, %s, %s", fd, f1, f2); return buf; }
            break;
        case 0x60:
            if (rs2(insn) == 0) { snprintf(buf, sizeof(buf), "fcvt.w.s %s, %s", xd, f1); return buf; }
            if (rs2(insn) == 1) { snprintf(buf, sizeof(buf), "fcvt.wu.s %s, %s", xd, f1); return buf; }
            break;
        case 0x70:
            if (rs2(insn) == 0 && f3 == 0) { snprintf(buf, sizeof(buf), "fmv.x.w %s, %s", xd, f1); return buf; }
            if (rs2(insn) == 0 && f3 == 1) { snprintf(buf, sizeof(buf), "fclass.s %s, %s", xd, f1); return buf; }
            break;
        case 0x50:
            if (f3 == 2) { snprintf(buf, sizeof(buf), "feq.s %s, %s, %s", xd, f1, f2); return buf; }
            if (f3 == 1) { snprintf(buf, sizeof(buf), "flt.s %s, %s, %s", xd, f1, f2); return buf; }
            if (f3 == 0) { snprintf(buf, sizeof(buf), "fle.s %s, %s, %s", xd, f1, f2); return buf; }
            break;
        case 0x68:
            if (rs2(insn) == 0) { snprintf(buf, sizeof(buf), "fcvt.s.w %s, %s", fd, x1); return buf; }
            if (rs2(insn) == 1) { snprintf(buf, sizeof(buf), "fcvt.s.wu %s, %s", fd, x1); return buf; }
            break;
        case 0x78:
            if (rs2(insn) == 0) { snprintf(buf, sizeof(buf), "fmv.w.x %s, %s", fd, x1); return buf; }
            break;
        }
        break;
    }
    }

    snprintf(buf, sizeof(buf), "unknown(0x%08x)", insn);
    return buf;
}

} // namespace rv32_disasm

#endif // RV32_DISASM_H
