//==============================================================================
// sc_main_CPU_RV32IM.cpp - Auto-generated SystemC testbench
// DO NOT EDIT - regenerate with: lake exe generate_all
//==============================================================================

#include <systemc.h>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include "CPU_RV32IM.h"
#include "elf_loader.h"

static const uint32_t MEM_SIZE_WORDS = 16384;
static const uint32_t TOHOST_ADDR = 0x1000;
static const uint32_t TIMEOUT_CYCLES = 100000;

// Memory model (shared between ImemModel and DmemModel)
static uint32_t mem[16384];

static void mem_write_cb(uint32_t addr, uint32_t data) {
    uint32_t widx = addr / 4;
    if (widx < MEM_SIZE_WORDS) mem[widx] = data;
}

// Bus pack/unpack helpers
void set_imem_resp_data(sc_signal<bool>* sigs[], uint32_t v) {
    sigs[0]->write((v >> 0) & 1);
    sigs[1]->write((v >> 1) & 1);
    sigs[2]->write((v >> 2) & 1);
    sigs[3]->write((v >> 3) & 1);
    sigs[4]->write((v >> 4) & 1);
    sigs[5]->write((v >> 5) & 1);
    sigs[6]->write((v >> 6) & 1);
    sigs[7]->write((v >> 7) & 1);
    sigs[8]->write((v >> 8) & 1);
    sigs[9]->write((v >> 9) & 1);
    sigs[10]->write((v >> 10) & 1);
    sigs[11]->write((v >> 11) & 1);
    sigs[12]->write((v >> 12) & 1);
    sigs[13]->write((v >> 13) & 1);
    sigs[14]->write((v >> 14) & 1);
    sigs[15]->write((v >> 15) & 1);
    sigs[16]->write((v >> 16) & 1);
    sigs[17]->write((v >> 17) & 1);
    sigs[18]->write((v >> 18) & 1);
    sigs[19]->write((v >> 19) & 1);
    sigs[20]->write((v >> 20) & 1);
    sigs[21]->write((v >> 21) & 1);
    sigs[22]->write((v >> 22) & 1);
    sigs[23]->write((v >> 23) & 1);
    sigs[24]->write((v >> 24) & 1);
    sigs[25]->write((v >> 25) & 1);
    sigs[26]->write((v >> 26) & 1);
    sigs[27]->write((v >> 27) & 1);
    sigs[28]->write((v >> 28) & 1);
    sigs[29]->write((v >> 29) & 1);
    sigs[30]->write((v >> 30) & 1);
    sigs[31]->write((v >> 31) & 1);
}


void set_dmem_resp_data(sc_signal<bool>* sigs[], uint32_t v) {
    sigs[0]->write((v >> 0) & 1);
    sigs[1]->write((v >> 1) & 1);
    sigs[2]->write((v >> 2) & 1);
    sigs[3]->write((v >> 3) & 1);
    sigs[4]->write((v >> 4) & 1);
    sigs[5]->write((v >> 5) & 1);
    sigs[6]->write((v >> 6) & 1);
    sigs[7]->write((v >> 7) & 1);
    sigs[8]->write((v >> 8) & 1);
    sigs[9]->write((v >> 9) & 1);
    sigs[10]->write((v >> 10) & 1);
    sigs[11]->write((v >> 11) & 1);
    sigs[12]->write((v >> 12) & 1);
    sigs[13]->write((v >> 13) & 1);
    sigs[14]->write((v >> 14) & 1);
    sigs[15]->write((v >> 15) & 1);
    sigs[16]->write((v >> 16) & 1);
    sigs[17]->write((v >> 17) & 1);
    sigs[18]->write((v >> 18) & 1);
    sigs[19]->write((v >> 19) & 1);
    sigs[20]->write((v >> 20) & 1);
    sigs[21]->write((v >> 21) & 1);
    sigs[22]->write((v >> 22) & 1);
    sigs[23]->write((v >> 23) & 1);
    sigs[24]->write((v >> 24) & 1);
    sigs[25]->write((v >> 25) & 1);
    sigs[26]->write((v >> 26) & 1);
    sigs[27]->write((v >> 27) & 1);
    sigs[28]->write((v >> 28) & 1);
    sigs[29]->write((v >> 29) & 1);
    sigs[30]->write((v >> 30) & 1);
    sigs[31]->write((v >> 31) & 1);
}


uint32_t get_fetch_pc(sc_signal<bool>* sigs[]) {
    return (uint32_t)sigs[0]->read() | ((uint32_t)sigs[1]->read() << 1) | ((uint32_t)sigs[2]->read() << 2) | ((uint32_t)sigs[3]->read() << 3) | ((uint32_t)sigs[4]->read() << 4) | ((uint32_t)sigs[5]->read() << 5) | ((uint32_t)sigs[6]->read() << 6) | ((uint32_t)sigs[7]->read() << 7) | ((uint32_t)sigs[8]->read() << 8) | ((uint32_t)sigs[9]->read() << 9) | ((uint32_t)sigs[10]->read() << 10) | ((uint32_t)sigs[11]->read() << 11) | ((uint32_t)sigs[12]->read() << 12) | ((uint32_t)sigs[13]->read() << 13) | ((uint32_t)sigs[14]->read() << 14) | ((uint32_t)sigs[15]->read() << 15) | ((uint32_t)sigs[16]->read() << 16) | ((uint32_t)sigs[17]->read() << 17) | ((uint32_t)sigs[18]->read() << 18) | ((uint32_t)sigs[19]->read() << 19) | ((uint32_t)sigs[20]->read() << 20) | ((uint32_t)sigs[21]->read() << 21) | ((uint32_t)sigs[22]->read() << 22) | ((uint32_t)sigs[23]->read() << 23) | ((uint32_t)sigs[24]->read() << 24) | ((uint32_t)sigs[25]->read() << 25) | ((uint32_t)sigs[26]->read() << 26) | ((uint32_t)sigs[27]->read() << 27) | ((uint32_t)sigs[28]->read() << 28) | ((uint32_t)sigs[29]->read() << 29) | ((uint32_t)sigs[30]->read() << 30) | ((uint32_t)sigs[31]->read() << 31);
}

uint32_t get_dmem_req_addr(sc_signal<bool>* sigs[]) {
    return (uint32_t)sigs[0]->read() | ((uint32_t)sigs[1]->read() << 1) | ((uint32_t)sigs[2]->read() << 2) | ((uint32_t)sigs[3]->read() << 3) | ((uint32_t)sigs[4]->read() << 4) | ((uint32_t)sigs[5]->read() << 5) | ((uint32_t)sigs[6]->read() << 6) | ((uint32_t)sigs[7]->read() << 7) | ((uint32_t)sigs[8]->read() << 8) | ((uint32_t)sigs[9]->read() << 9) | ((uint32_t)sigs[10]->read() << 10) | ((uint32_t)sigs[11]->read() << 11) | ((uint32_t)sigs[12]->read() << 12) | ((uint32_t)sigs[13]->read() << 13) | ((uint32_t)sigs[14]->read() << 14) | ((uint32_t)sigs[15]->read() << 15) | ((uint32_t)sigs[16]->read() << 16) | ((uint32_t)sigs[17]->read() << 17) | ((uint32_t)sigs[18]->read() << 18) | ((uint32_t)sigs[19]->read() << 19) | ((uint32_t)sigs[20]->read() << 20) | ((uint32_t)sigs[21]->read() << 21) | ((uint32_t)sigs[22]->read() << 22) | ((uint32_t)sigs[23]->read() << 23) | ((uint32_t)sigs[24]->read() << 24) | ((uint32_t)sigs[25]->read() << 25) | ((uint32_t)sigs[26]->read() << 26) | ((uint32_t)sigs[27]->read() << 27) | ((uint32_t)sigs[28]->read() << 28) | ((uint32_t)sigs[29]->read() << 29) | ((uint32_t)sigs[30]->read() << 30) | ((uint32_t)sigs[31]->read() << 31);
}

uint32_t get_dmem_req_data(sc_signal<bool>* sigs[]) {
    return (uint32_t)sigs[0]->read() | ((uint32_t)sigs[1]->read() << 1) | ((uint32_t)sigs[2]->read() << 2) | ((uint32_t)sigs[3]->read() << 3) | ((uint32_t)sigs[4]->read() << 4) | ((uint32_t)sigs[5]->read() << 5) | ((uint32_t)sigs[6]->read() << 6) | ((uint32_t)sigs[7]->read() << 7) | ((uint32_t)sigs[8]->read() << 8) | ((uint32_t)sigs[9]->read() << 9) | ((uint32_t)sigs[10]->read() << 10) | ((uint32_t)sigs[11]->read() << 11) | ((uint32_t)sigs[12]->read() << 12) | ((uint32_t)sigs[13]->read() << 13) | ((uint32_t)sigs[14]->read() << 14) | ((uint32_t)sigs[15]->read() << 15) | ((uint32_t)sigs[16]->read() << 16) | ((uint32_t)sigs[17]->read() << 17) | ((uint32_t)sigs[18]->read() << 18) | ((uint32_t)sigs[19]->read() << 19) | ((uint32_t)sigs[20]->read() << 20) | ((uint32_t)sigs[21]->read() << 21) | ((uint32_t)sigs[22]->read() << 22) | ((uint32_t)sigs[23]->read() << 23) | ((uint32_t)sigs[24]->read() << 24) | ((uint32_t)sigs[25]->read() << 25) | ((uint32_t)sigs[26]->read() << 26) | ((uint32_t)sigs[27]->read() << 27) | ((uint32_t)sigs[28]->read() << 28) | ((uint32_t)sigs[29]->read() << 29) | ((uint32_t)sigs[30]->read() << 30) | ((uint32_t)sigs[31]->read() << 31);
}


//------------------------------------------------------------------------------
// ImemModel: Combinational instruction memory
// Equivalent to SV: assign imem_resp_data = mem[fetch_pc >> 2];
// SC_METHOD sensitive to fetch_pc bits ensures delta-cycle feedback works.
//------------------------------------------------------------------------------
SC_MODULE(ImemModel) {
    sc_in<bool> fetch_pc_0;
    sc_in<bool> fetch_pc_1;
    sc_in<bool> fetch_pc_2;
    sc_in<bool> fetch_pc_3;
    sc_in<bool> fetch_pc_4;
    sc_in<bool> fetch_pc_5;
    sc_in<bool> fetch_pc_6;
    sc_in<bool> fetch_pc_7;
    sc_in<bool> fetch_pc_8;
    sc_in<bool> fetch_pc_9;
    sc_in<bool> fetch_pc_10;
    sc_in<bool> fetch_pc_11;
    sc_in<bool> fetch_pc_12;
    sc_in<bool> fetch_pc_13;
    sc_in<bool> fetch_pc_14;
    sc_in<bool> fetch_pc_15;
    sc_in<bool> fetch_pc_16;
    sc_in<bool> fetch_pc_17;
    sc_in<bool> fetch_pc_18;
    sc_in<bool> fetch_pc_19;
    sc_in<bool> fetch_pc_20;
    sc_in<bool> fetch_pc_21;
    sc_in<bool> fetch_pc_22;
    sc_in<bool> fetch_pc_23;
    sc_in<bool> fetch_pc_24;
    sc_in<bool> fetch_pc_25;
    sc_in<bool> fetch_pc_26;
    sc_in<bool> fetch_pc_27;
    sc_in<bool> fetch_pc_28;
    sc_in<bool> fetch_pc_29;
    sc_in<bool> fetch_pc_30;
    sc_in<bool> fetch_pc_31;
    sc_out<bool> imem_resp_data_0;
    sc_out<bool> imem_resp_data_1;
    sc_out<bool> imem_resp_data_2;
    sc_out<bool> imem_resp_data_3;
    sc_out<bool> imem_resp_data_4;
    sc_out<bool> imem_resp_data_5;
    sc_out<bool> imem_resp_data_6;
    sc_out<bool> imem_resp_data_7;
    sc_out<bool> imem_resp_data_8;
    sc_out<bool> imem_resp_data_9;
    sc_out<bool> imem_resp_data_10;
    sc_out<bool> imem_resp_data_11;
    sc_out<bool> imem_resp_data_12;
    sc_out<bool> imem_resp_data_13;
    sc_out<bool> imem_resp_data_14;
    sc_out<bool> imem_resp_data_15;
    sc_out<bool> imem_resp_data_16;
    sc_out<bool> imem_resp_data_17;
    sc_out<bool> imem_resp_data_18;
    sc_out<bool> imem_resp_data_19;
    sc_out<bool> imem_resp_data_20;
    sc_out<bool> imem_resp_data_21;
    sc_out<bool> imem_resp_data_22;
    sc_out<bool> imem_resp_data_23;
    sc_out<bool> imem_resp_data_24;
    sc_out<bool> imem_resp_data_25;
    sc_out<bool> imem_resp_data_26;
    sc_out<bool> imem_resp_data_27;
    sc_out<bool> imem_resp_data_28;
    sc_out<bool> imem_resp_data_29;
    sc_out<bool> imem_resp_data_30;
    sc_out<bool> imem_resp_data_31;

    void update() {
        uint32_t pc = (uint32_t)fetch_pc_0.read() | ((uint32_t)fetch_pc_1.read() << 1) | ((uint32_t)fetch_pc_2.read() << 2) | ((uint32_t)fetch_pc_3.read() << 3) | ((uint32_t)fetch_pc_4.read() << 4) | ((uint32_t)fetch_pc_5.read() << 5) | ((uint32_t)fetch_pc_6.read() << 6) | ((uint32_t)fetch_pc_7.read() << 7) | ((uint32_t)fetch_pc_8.read() << 8) | ((uint32_t)fetch_pc_9.read() << 9) | ((uint32_t)fetch_pc_10.read() << 10) | ((uint32_t)fetch_pc_11.read() << 11) | ((uint32_t)fetch_pc_12.read() << 12) | ((uint32_t)fetch_pc_13.read() << 13) | ((uint32_t)fetch_pc_14.read() << 14) | ((uint32_t)fetch_pc_15.read() << 15) | ((uint32_t)fetch_pc_16.read() << 16) | ((uint32_t)fetch_pc_17.read() << 17) | ((uint32_t)fetch_pc_18.read() << 18) | ((uint32_t)fetch_pc_19.read() << 19) | ((uint32_t)fetch_pc_20.read() << 20) | ((uint32_t)fetch_pc_21.read() << 21) | ((uint32_t)fetch_pc_22.read() << 22) | ((uint32_t)fetch_pc_23.read() << 23) | ((uint32_t)fetch_pc_24.read() << 24) | ((uint32_t)fetch_pc_25.read() << 25) | ((uint32_t)fetch_pc_26.read() << 26) | ((uint32_t)fetch_pc_27.read() << 27) | ((uint32_t)fetch_pc_28.read() << 28) | ((uint32_t)fetch_pc_29.read() << 29) | ((uint32_t)fetch_pc_30.read() << 30) | ((uint32_t)fetch_pc_31.read() << 31);
        uint32_t widx = pc >> 2;
        uint32_t data = (widx < MEM_SIZE_WORDS) ? mem[widx] : 0;
        imem_resp_data_0.write((data >> 0) & 1);
        imem_resp_data_1.write((data >> 1) & 1);
        imem_resp_data_2.write((data >> 2) & 1);
        imem_resp_data_3.write((data >> 3) & 1);
        imem_resp_data_4.write((data >> 4) & 1);
        imem_resp_data_5.write((data >> 5) & 1);
        imem_resp_data_6.write((data >> 6) & 1);
        imem_resp_data_7.write((data >> 7) & 1);
        imem_resp_data_8.write((data >> 8) & 1);
        imem_resp_data_9.write((data >> 9) & 1);
        imem_resp_data_10.write((data >> 10) & 1);
        imem_resp_data_11.write((data >> 11) & 1);
        imem_resp_data_12.write((data >> 12) & 1);
        imem_resp_data_13.write((data >> 13) & 1);
        imem_resp_data_14.write((data >> 14) & 1);
        imem_resp_data_15.write((data >> 15) & 1);
        imem_resp_data_16.write((data >> 16) & 1);
        imem_resp_data_17.write((data >> 17) & 1);
        imem_resp_data_18.write((data >> 18) & 1);
        imem_resp_data_19.write((data >> 19) & 1);
        imem_resp_data_20.write((data >> 20) & 1);
        imem_resp_data_21.write((data >> 21) & 1);
        imem_resp_data_22.write((data >> 22) & 1);
        imem_resp_data_23.write((data >> 23) & 1);
        imem_resp_data_24.write((data >> 24) & 1);
        imem_resp_data_25.write((data >> 25) & 1);
        imem_resp_data_26.write((data >> 26) & 1);
        imem_resp_data_27.write((data >> 27) & 1);
        imem_resp_data_28.write((data >> 28) & 1);
        imem_resp_data_29.write((data >> 29) & 1);
        imem_resp_data_30.write((data >> 30) & 1);
        imem_resp_data_31.write((data >> 31) & 1);
    }

    SC_CTOR(ImemModel) {
        SC_METHOD(update);
        sensitive << fetch_pc_0 << fetch_pc_1 << fetch_pc_2 << fetch_pc_3 << fetch_pc_4 << fetch_pc_5 << fetch_pc_6 << fetch_pc_7 << fetch_pc_8 << fetch_pc_9 << fetch_pc_10 << fetch_pc_11 << fetch_pc_12 << fetch_pc_13 << fetch_pc_14 << fetch_pc_15 << fetch_pc_16 << fetch_pc_17 << fetch_pc_18 << fetch_pc_19 << fetch_pc_20 << fetch_pc_21 << fetch_pc_22 << fetch_pc_23 << fetch_pc_24 << fetch_pc_25 << fetch_pc_26 << fetch_pc_27 << fetch_pc_28 << fetch_pc_29 << fetch_pc_30 << fetch_pc_31;
    }
};

//------------------------------------------------------------------------------
// DmemModel: Data memory with 1-cycle read latency (manually clocked)
// NOT an SC_MODULE - called explicitly from the simulation loop to avoid
// timing issues with SC_CTHREAD firing before CPU eval.
//------------------------------------------------------------------------------
struct DmemModel {
    sc_signal<bool>& dmem_req_valid_sig;
    sc_signal<bool>& dmem_req_we_sig;
    sc_signal<bool>& dmem_req_ready_sig;
    sc_signal<bool>& dmem_resp_valid_sig;
    sc_signal<bool>** dmem_req_addr_sigs;
    sc_signal<bool>** dmem_req_data_sigs;
    sc_signal<bool>** dmem_resp_data_sigs;

    bool pending;
    uint32_t read_data;
    bool test_done;
    uint32_t test_data;

    DmemModel(sc_signal<bool>& valid, sc_signal<bool>& we,
             sc_signal<bool>& ready, sc_signal<bool>& resp_valid,
             sc_signal<bool>** addr_sigs, sc_signal<bool>** data_out_sigs,
             sc_signal<bool>** resp_data_sigs)
        : dmem_req_valid_sig(valid), dmem_req_we_sig(we),
          dmem_req_ready_sig(ready), dmem_resp_valid_sig(resp_valid),
          dmem_req_addr_sigs(addr_sigs), dmem_req_data_sigs(data_out_sigs),
          dmem_resp_data_sigs(resp_data_sigs),
          pending(false), read_data(0), test_done(false), test_data(0)
    { dmem_req_ready_sig.write(true); }

    void tick() {
        // Respond to pending load from previous cycle
        if (pending) {
            dmem_resp_valid_sig.write(true);
            for (int i = 0; i < 32; i++) dmem_resp_data_sigs[i]->write((read_data >> i) & 1);
            pending = false;
        } else {
            dmem_resp_valid_sig.write(false);
            for (int i = 0; i < 32; i++) dmem_resp_data_sigs[i]->write(false);
        }

        // Handle new request
        if (dmem_req_valid_sig.read()) {
            uint32_t addr = get_dmem_req_addr(dmem_req_addr_sigs);
            if (dmem_req_we_sig.read()) {
                uint32_t data = get_dmem_req_data(dmem_req_data_sigs);
                if (addr == TOHOST_ADDR) {
                    test_done = true;
                    test_data = data;
                } else {
                    uint32_t widx = addr >> 2;
                    if (widx < MEM_SIZE_WORDS) mem[widx] = data;
                }
            } else {
                read_data = mem[addr >> 2];
                pending = true;
            }
        }
    }
};

int sc_main(int argc, char* argv[]) {
    // Suppress W571 (no activity for sc_start) — expected with manual eval
    sc_report_handler::set_actions(SC_ID_NO_SC_START_ACTIVITY_, SC_DO_NOTHING);

    const char* elf_path = nullptr;
    uint32_t timeout = TIMEOUT_CYCLES;
    for (int i = 1; i < argc; i++) {
        if (strncmp(argv[i], "+elf=", 5) == 0) elf_path = argv[i] + 5;
        if (strncmp(argv[i], "+timeout=", 9) == 0) timeout = atoi(argv[i] + 9);
    }

    if (!elf_path) {
        fprintf(stderr, "ERROR: No ELF file. Use +elf=path\n");
        return 1;
    }

    memset(mem, 0, sizeof(mem));
    if (load_elf(elf_path, mem_write_cb) < 0) return 1;

    // Create signals
    sc_clock clk("clk", 10, SC_NS);
    sc_signal<bool> reset_sig;
    sc_signal<bool> dmem_req_ready_sig;
    sc_signal<bool> dmem_resp_valid_sig;
    sc_signal<bool> fetch_stalled_sig;
    sc_signal<bool> global_stall_out_sig;
    sc_signal<bool> dmem_req_valid_sig;
    sc_signal<bool> dmem_req_we_sig;
    sc_signal<bool> rob_empty_sig;
    sc_signal<bool> zero_sig;
    sc_signal<bool> one_sig;
    sc_signal<bool> imem_resp_data_0_sig;
    sc_signal<bool> imem_resp_data_1_sig;
    sc_signal<bool> imem_resp_data_2_sig;
    sc_signal<bool> imem_resp_data_3_sig;
    sc_signal<bool> imem_resp_data_4_sig;
    sc_signal<bool> imem_resp_data_5_sig;
    sc_signal<bool> imem_resp_data_6_sig;
    sc_signal<bool> imem_resp_data_7_sig;
    sc_signal<bool> imem_resp_data_8_sig;
    sc_signal<bool> imem_resp_data_9_sig;
    sc_signal<bool> imem_resp_data_10_sig;
    sc_signal<bool> imem_resp_data_11_sig;
    sc_signal<bool> imem_resp_data_12_sig;
    sc_signal<bool> imem_resp_data_13_sig;
    sc_signal<bool> imem_resp_data_14_sig;
    sc_signal<bool> imem_resp_data_15_sig;
    sc_signal<bool> imem_resp_data_16_sig;
    sc_signal<bool> imem_resp_data_17_sig;
    sc_signal<bool> imem_resp_data_18_sig;
    sc_signal<bool> imem_resp_data_19_sig;
    sc_signal<bool> imem_resp_data_20_sig;
    sc_signal<bool> imem_resp_data_21_sig;
    sc_signal<bool> imem_resp_data_22_sig;
    sc_signal<bool> imem_resp_data_23_sig;
    sc_signal<bool> imem_resp_data_24_sig;
    sc_signal<bool> imem_resp_data_25_sig;
    sc_signal<bool> imem_resp_data_26_sig;
    sc_signal<bool> imem_resp_data_27_sig;
    sc_signal<bool> imem_resp_data_28_sig;
    sc_signal<bool> imem_resp_data_29_sig;
    sc_signal<bool> imem_resp_data_30_sig;
    sc_signal<bool> imem_resp_data_31_sig;
    sc_signal<bool> dmem_resp_data_0_sig;
    sc_signal<bool> dmem_resp_data_1_sig;
    sc_signal<bool> dmem_resp_data_2_sig;
    sc_signal<bool> dmem_resp_data_3_sig;
    sc_signal<bool> dmem_resp_data_4_sig;
    sc_signal<bool> dmem_resp_data_5_sig;
    sc_signal<bool> dmem_resp_data_6_sig;
    sc_signal<bool> dmem_resp_data_7_sig;
    sc_signal<bool> dmem_resp_data_8_sig;
    sc_signal<bool> dmem_resp_data_9_sig;
    sc_signal<bool> dmem_resp_data_10_sig;
    sc_signal<bool> dmem_resp_data_11_sig;
    sc_signal<bool> dmem_resp_data_12_sig;
    sc_signal<bool> dmem_resp_data_13_sig;
    sc_signal<bool> dmem_resp_data_14_sig;
    sc_signal<bool> dmem_resp_data_15_sig;
    sc_signal<bool> dmem_resp_data_16_sig;
    sc_signal<bool> dmem_resp_data_17_sig;
    sc_signal<bool> dmem_resp_data_18_sig;
    sc_signal<bool> dmem_resp_data_19_sig;
    sc_signal<bool> dmem_resp_data_20_sig;
    sc_signal<bool> dmem_resp_data_21_sig;
    sc_signal<bool> dmem_resp_data_22_sig;
    sc_signal<bool> dmem_resp_data_23_sig;
    sc_signal<bool> dmem_resp_data_24_sig;
    sc_signal<bool> dmem_resp_data_25_sig;
    sc_signal<bool> dmem_resp_data_26_sig;
    sc_signal<bool> dmem_resp_data_27_sig;
    sc_signal<bool> dmem_resp_data_28_sig;
    sc_signal<bool> dmem_resp_data_29_sig;
    sc_signal<bool> dmem_resp_data_30_sig;
    sc_signal<bool> dmem_resp_data_31_sig;
    sc_signal<bool> fetch_pc_0_sig;
    sc_signal<bool> fetch_pc_1_sig;
    sc_signal<bool> fetch_pc_2_sig;
    sc_signal<bool> fetch_pc_3_sig;
    sc_signal<bool> fetch_pc_4_sig;
    sc_signal<bool> fetch_pc_5_sig;
    sc_signal<bool> fetch_pc_6_sig;
    sc_signal<bool> fetch_pc_7_sig;
    sc_signal<bool> fetch_pc_8_sig;
    sc_signal<bool> fetch_pc_9_sig;
    sc_signal<bool> fetch_pc_10_sig;
    sc_signal<bool> fetch_pc_11_sig;
    sc_signal<bool> fetch_pc_12_sig;
    sc_signal<bool> fetch_pc_13_sig;
    sc_signal<bool> fetch_pc_14_sig;
    sc_signal<bool> fetch_pc_15_sig;
    sc_signal<bool> fetch_pc_16_sig;
    sc_signal<bool> fetch_pc_17_sig;
    sc_signal<bool> fetch_pc_18_sig;
    sc_signal<bool> fetch_pc_19_sig;
    sc_signal<bool> fetch_pc_20_sig;
    sc_signal<bool> fetch_pc_21_sig;
    sc_signal<bool> fetch_pc_22_sig;
    sc_signal<bool> fetch_pc_23_sig;
    sc_signal<bool> fetch_pc_24_sig;
    sc_signal<bool> fetch_pc_25_sig;
    sc_signal<bool> fetch_pc_26_sig;
    sc_signal<bool> fetch_pc_27_sig;
    sc_signal<bool> fetch_pc_28_sig;
    sc_signal<bool> fetch_pc_29_sig;
    sc_signal<bool> fetch_pc_30_sig;
    sc_signal<bool> fetch_pc_31_sig;
    sc_signal<bool> dmem_req_addr_0_sig;
    sc_signal<bool> dmem_req_addr_1_sig;
    sc_signal<bool> dmem_req_addr_2_sig;
    sc_signal<bool> dmem_req_addr_3_sig;
    sc_signal<bool> dmem_req_addr_4_sig;
    sc_signal<bool> dmem_req_addr_5_sig;
    sc_signal<bool> dmem_req_addr_6_sig;
    sc_signal<bool> dmem_req_addr_7_sig;
    sc_signal<bool> dmem_req_addr_8_sig;
    sc_signal<bool> dmem_req_addr_9_sig;
    sc_signal<bool> dmem_req_addr_10_sig;
    sc_signal<bool> dmem_req_addr_11_sig;
    sc_signal<bool> dmem_req_addr_12_sig;
    sc_signal<bool> dmem_req_addr_13_sig;
    sc_signal<bool> dmem_req_addr_14_sig;
    sc_signal<bool> dmem_req_addr_15_sig;
    sc_signal<bool> dmem_req_addr_16_sig;
    sc_signal<bool> dmem_req_addr_17_sig;
    sc_signal<bool> dmem_req_addr_18_sig;
    sc_signal<bool> dmem_req_addr_19_sig;
    sc_signal<bool> dmem_req_addr_20_sig;
    sc_signal<bool> dmem_req_addr_21_sig;
    sc_signal<bool> dmem_req_addr_22_sig;
    sc_signal<bool> dmem_req_addr_23_sig;
    sc_signal<bool> dmem_req_addr_24_sig;
    sc_signal<bool> dmem_req_addr_25_sig;
    sc_signal<bool> dmem_req_addr_26_sig;
    sc_signal<bool> dmem_req_addr_27_sig;
    sc_signal<bool> dmem_req_addr_28_sig;
    sc_signal<bool> dmem_req_addr_29_sig;
    sc_signal<bool> dmem_req_addr_30_sig;
    sc_signal<bool> dmem_req_addr_31_sig;
    sc_signal<bool> dmem_req_data_0_sig;
    sc_signal<bool> dmem_req_data_1_sig;
    sc_signal<bool> dmem_req_data_2_sig;
    sc_signal<bool> dmem_req_data_3_sig;
    sc_signal<bool> dmem_req_data_4_sig;
    sc_signal<bool> dmem_req_data_5_sig;
    sc_signal<bool> dmem_req_data_6_sig;
    sc_signal<bool> dmem_req_data_7_sig;
    sc_signal<bool> dmem_req_data_8_sig;
    sc_signal<bool> dmem_req_data_9_sig;
    sc_signal<bool> dmem_req_data_10_sig;
    sc_signal<bool> dmem_req_data_11_sig;
    sc_signal<bool> dmem_req_data_12_sig;
    sc_signal<bool> dmem_req_data_13_sig;
    sc_signal<bool> dmem_req_data_14_sig;
    sc_signal<bool> dmem_req_data_15_sig;
    sc_signal<bool> dmem_req_data_16_sig;
    sc_signal<bool> dmem_req_data_17_sig;
    sc_signal<bool> dmem_req_data_18_sig;
    sc_signal<bool> dmem_req_data_19_sig;
    sc_signal<bool> dmem_req_data_20_sig;
    sc_signal<bool> dmem_req_data_21_sig;
    sc_signal<bool> dmem_req_data_22_sig;
    sc_signal<bool> dmem_req_data_23_sig;
    sc_signal<bool> dmem_req_data_24_sig;
    sc_signal<bool> dmem_req_data_25_sig;
    sc_signal<bool> dmem_req_data_26_sig;
    sc_signal<bool> dmem_req_data_27_sig;
    sc_signal<bool> dmem_req_data_28_sig;
    sc_signal<bool> dmem_req_data_29_sig;
    sc_signal<bool> dmem_req_data_30_sig;
    sc_signal<bool> dmem_req_data_31_sig;

    // Signal arrays for bus helpers
    sc_signal<bool>* imem_resp_data_sigs[] = {&imem_resp_data_0_sig, &imem_resp_data_1_sig, &imem_resp_data_2_sig, &imem_resp_data_3_sig, &imem_resp_data_4_sig, &imem_resp_data_5_sig, &imem_resp_data_6_sig, &imem_resp_data_7_sig, &imem_resp_data_8_sig, &imem_resp_data_9_sig, &imem_resp_data_10_sig, &imem_resp_data_11_sig, &imem_resp_data_12_sig, &imem_resp_data_13_sig, &imem_resp_data_14_sig, &imem_resp_data_15_sig, &imem_resp_data_16_sig, &imem_resp_data_17_sig, &imem_resp_data_18_sig, &imem_resp_data_19_sig, &imem_resp_data_20_sig, &imem_resp_data_21_sig, &imem_resp_data_22_sig, &imem_resp_data_23_sig, &imem_resp_data_24_sig, &imem_resp_data_25_sig, &imem_resp_data_26_sig, &imem_resp_data_27_sig, &imem_resp_data_28_sig, &imem_resp_data_29_sig, &imem_resp_data_30_sig, &imem_resp_data_31_sig};
    sc_signal<bool>* dmem_resp_data_sigs[] = {&dmem_resp_data_0_sig, &dmem_resp_data_1_sig, &dmem_resp_data_2_sig, &dmem_resp_data_3_sig, &dmem_resp_data_4_sig, &dmem_resp_data_5_sig, &dmem_resp_data_6_sig, &dmem_resp_data_7_sig, &dmem_resp_data_8_sig, &dmem_resp_data_9_sig, &dmem_resp_data_10_sig, &dmem_resp_data_11_sig, &dmem_resp_data_12_sig, &dmem_resp_data_13_sig, &dmem_resp_data_14_sig, &dmem_resp_data_15_sig, &dmem_resp_data_16_sig, &dmem_resp_data_17_sig, &dmem_resp_data_18_sig, &dmem_resp_data_19_sig, &dmem_resp_data_20_sig, &dmem_resp_data_21_sig, &dmem_resp_data_22_sig, &dmem_resp_data_23_sig, &dmem_resp_data_24_sig, &dmem_resp_data_25_sig, &dmem_resp_data_26_sig, &dmem_resp_data_27_sig, &dmem_resp_data_28_sig, &dmem_resp_data_29_sig, &dmem_resp_data_30_sig, &dmem_resp_data_31_sig};
    sc_signal<bool>* fetch_pc_sigs[] = {&fetch_pc_0_sig, &fetch_pc_1_sig, &fetch_pc_2_sig, &fetch_pc_3_sig, &fetch_pc_4_sig, &fetch_pc_5_sig, &fetch_pc_6_sig, &fetch_pc_7_sig, &fetch_pc_8_sig, &fetch_pc_9_sig, &fetch_pc_10_sig, &fetch_pc_11_sig, &fetch_pc_12_sig, &fetch_pc_13_sig, &fetch_pc_14_sig, &fetch_pc_15_sig, &fetch_pc_16_sig, &fetch_pc_17_sig, &fetch_pc_18_sig, &fetch_pc_19_sig, &fetch_pc_20_sig, &fetch_pc_21_sig, &fetch_pc_22_sig, &fetch_pc_23_sig, &fetch_pc_24_sig, &fetch_pc_25_sig, &fetch_pc_26_sig, &fetch_pc_27_sig, &fetch_pc_28_sig, &fetch_pc_29_sig, &fetch_pc_30_sig, &fetch_pc_31_sig};
    sc_signal<bool>* dmem_req_addr_sigs[] = {&dmem_req_addr_0_sig, &dmem_req_addr_1_sig, &dmem_req_addr_2_sig, &dmem_req_addr_3_sig, &dmem_req_addr_4_sig, &dmem_req_addr_5_sig, &dmem_req_addr_6_sig, &dmem_req_addr_7_sig, &dmem_req_addr_8_sig, &dmem_req_addr_9_sig, &dmem_req_addr_10_sig, &dmem_req_addr_11_sig, &dmem_req_addr_12_sig, &dmem_req_addr_13_sig, &dmem_req_addr_14_sig, &dmem_req_addr_15_sig, &dmem_req_addr_16_sig, &dmem_req_addr_17_sig, &dmem_req_addr_18_sig, &dmem_req_addr_19_sig, &dmem_req_addr_20_sig, &dmem_req_addr_21_sig, &dmem_req_addr_22_sig, &dmem_req_addr_23_sig, &dmem_req_addr_24_sig, &dmem_req_addr_25_sig, &dmem_req_addr_26_sig, &dmem_req_addr_27_sig, &dmem_req_addr_28_sig, &dmem_req_addr_29_sig, &dmem_req_addr_30_sig, &dmem_req_addr_31_sig};
    sc_signal<bool>* dmem_req_data_sigs[] = {&dmem_req_data_0_sig, &dmem_req_data_1_sig, &dmem_req_data_2_sig, &dmem_req_data_3_sig, &dmem_req_data_4_sig, &dmem_req_data_5_sig, &dmem_req_data_6_sig, &dmem_req_data_7_sig, &dmem_req_data_8_sig, &dmem_req_data_9_sig, &dmem_req_data_10_sig, &dmem_req_data_11_sig, &dmem_req_data_12_sig, &dmem_req_data_13_sig, &dmem_req_data_14_sig, &dmem_req_data_15_sig, &dmem_req_data_16_sig, &dmem_req_data_17_sig, &dmem_req_data_18_sig, &dmem_req_data_19_sig, &dmem_req_data_20_sig, &dmem_req_data_21_sig, &dmem_req_data_22_sig, &dmem_req_data_23_sig, &dmem_req_data_24_sig, &dmem_req_data_25_sig, &dmem_req_data_26_sig, &dmem_req_data_27_sig, &dmem_req_data_28_sig, &dmem_req_data_29_sig, &dmem_req_data_30_sig, &dmem_req_data_31_sig};

    // Instantiate CPU (heap-allocated to avoid stack overflow)
    auto* u_cpu = new CPU_RV32IM("u_cpu");
    u_cpu->clock(clk);
    u_cpu->reset(reset_sig);
    u_cpu->dmem_req_ready(dmem_req_ready_sig);
    u_cpu->dmem_resp_valid(dmem_resp_valid_sig);
    u_cpu->fetch_stalled(fetch_stalled_sig);
    u_cpu->global_stall_out(global_stall_out_sig);
    u_cpu->dmem_req_valid(dmem_req_valid_sig);
    u_cpu->dmem_req_we(dmem_req_we_sig);
    u_cpu->rob_empty(rob_empty_sig);
    u_cpu->zero(zero_sig);
    u_cpu->one(one_sig);
    u_cpu->imem_resp_data_0(imem_resp_data_0_sig);
    u_cpu->imem_resp_data_1(imem_resp_data_1_sig);
    u_cpu->imem_resp_data_2(imem_resp_data_2_sig);
    u_cpu->imem_resp_data_3(imem_resp_data_3_sig);
    u_cpu->imem_resp_data_4(imem_resp_data_4_sig);
    u_cpu->imem_resp_data_5(imem_resp_data_5_sig);
    u_cpu->imem_resp_data_6(imem_resp_data_6_sig);
    u_cpu->imem_resp_data_7(imem_resp_data_7_sig);
    u_cpu->imem_resp_data_8(imem_resp_data_8_sig);
    u_cpu->imem_resp_data_9(imem_resp_data_9_sig);
    u_cpu->imem_resp_data_10(imem_resp_data_10_sig);
    u_cpu->imem_resp_data_11(imem_resp_data_11_sig);
    u_cpu->imem_resp_data_12(imem_resp_data_12_sig);
    u_cpu->imem_resp_data_13(imem_resp_data_13_sig);
    u_cpu->imem_resp_data_14(imem_resp_data_14_sig);
    u_cpu->imem_resp_data_15(imem_resp_data_15_sig);
    u_cpu->imem_resp_data_16(imem_resp_data_16_sig);
    u_cpu->imem_resp_data_17(imem_resp_data_17_sig);
    u_cpu->imem_resp_data_18(imem_resp_data_18_sig);
    u_cpu->imem_resp_data_19(imem_resp_data_19_sig);
    u_cpu->imem_resp_data_20(imem_resp_data_20_sig);
    u_cpu->imem_resp_data_21(imem_resp_data_21_sig);
    u_cpu->imem_resp_data_22(imem_resp_data_22_sig);
    u_cpu->imem_resp_data_23(imem_resp_data_23_sig);
    u_cpu->imem_resp_data_24(imem_resp_data_24_sig);
    u_cpu->imem_resp_data_25(imem_resp_data_25_sig);
    u_cpu->imem_resp_data_26(imem_resp_data_26_sig);
    u_cpu->imem_resp_data_27(imem_resp_data_27_sig);
    u_cpu->imem_resp_data_28(imem_resp_data_28_sig);
    u_cpu->imem_resp_data_29(imem_resp_data_29_sig);
    u_cpu->imem_resp_data_30(imem_resp_data_30_sig);
    u_cpu->imem_resp_data_31(imem_resp_data_31_sig);
    u_cpu->dmem_resp_data_0(dmem_resp_data_0_sig);
    u_cpu->dmem_resp_data_1(dmem_resp_data_1_sig);
    u_cpu->dmem_resp_data_2(dmem_resp_data_2_sig);
    u_cpu->dmem_resp_data_3(dmem_resp_data_3_sig);
    u_cpu->dmem_resp_data_4(dmem_resp_data_4_sig);
    u_cpu->dmem_resp_data_5(dmem_resp_data_5_sig);
    u_cpu->dmem_resp_data_6(dmem_resp_data_6_sig);
    u_cpu->dmem_resp_data_7(dmem_resp_data_7_sig);
    u_cpu->dmem_resp_data_8(dmem_resp_data_8_sig);
    u_cpu->dmem_resp_data_9(dmem_resp_data_9_sig);
    u_cpu->dmem_resp_data_10(dmem_resp_data_10_sig);
    u_cpu->dmem_resp_data_11(dmem_resp_data_11_sig);
    u_cpu->dmem_resp_data_12(dmem_resp_data_12_sig);
    u_cpu->dmem_resp_data_13(dmem_resp_data_13_sig);
    u_cpu->dmem_resp_data_14(dmem_resp_data_14_sig);
    u_cpu->dmem_resp_data_15(dmem_resp_data_15_sig);
    u_cpu->dmem_resp_data_16(dmem_resp_data_16_sig);
    u_cpu->dmem_resp_data_17(dmem_resp_data_17_sig);
    u_cpu->dmem_resp_data_18(dmem_resp_data_18_sig);
    u_cpu->dmem_resp_data_19(dmem_resp_data_19_sig);
    u_cpu->dmem_resp_data_20(dmem_resp_data_20_sig);
    u_cpu->dmem_resp_data_21(dmem_resp_data_21_sig);
    u_cpu->dmem_resp_data_22(dmem_resp_data_22_sig);
    u_cpu->dmem_resp_data_23(dmem_resp_data_23_sig);
    u_cpu->dmem_resp_data_24(dmem_resp_data_24_sig);
    u_cpu->dmem_resp_data_25(dmem_resp_data_25_sig);
    u_cpu->dmem_resp_data_26(dmem_resp_data_26_sig);
    u_cpu->dmem_resp_data_27(dmem_resp_data_27_sig);
    u_cpu->dmem_resp_data_28(dmem_resp_data_28_sig);
    u_cpu->dmem_resp_data_29(dmem_resp_data_29_sig);
    u_cpu->dmem_resp_data_30(dmem_resp_data_30_sig);
    u_cpu->dmem_resp_data_31(dmem_resp_data_31_sig);
    u_cpu->fetch_pc_0(fetch_pc_0_sig);
    u_cpu->fetch_pc_1(fetch_pc_1_sig);
    u_cpu->fetch_pc_2(fetch_pc_2_sig);
    u_cpu->fetch_pc_3(fetch_pc_3_sig);
    u_cpu->fetch_pc_4(fetch_pc_4_sig);
    u_cpu->fetch_pc_5(fetch_pc_5_sig);
    u_cpu->fetch_pc_6(fetch_pc_6_sig);
    u_cpu->fetch_pc_7(fetch_pc_7_sig);
    u_cpu->fetch_pc_8(fetch_pc_8_sig);
    u_cpu->fetch_pc_9(fetch_pc_9_sig);
    u_cpu->fetch_pc_10(fetch_pc_10_sig);
    u_cpu->fetch_pc_11(fetch_pc_11_sig);
    u_cpu->fetch_pc_12(fetch_pc_12_sig);
    u_cpu->fetch_pc_13(fetch_pc_13_sig);
    u_cpu->fetch_pc_14(fetch_pc_14_sig);
    u_cpu->fetch_pc_15(fetch_pc_15_sig);
    u_cpu->fetch_pc_16(fetch_pc_16_sig);
    u_cpu->fetch_pc_17(fetch_pc_17_sig);
    u_cpu->fetch_pc_18(fetch_pc_18_sig);
    u_cpu->fetch_pc_19(fetch_pc_19_sig);
    u_cpu->fetch_pc_20(fetch_pc_20_sig);
    u_cpu->fetch_pc_21(fetch_pc_21_sig);
    u_cpu->fetch_pc_22(fetch_pc_22_sig);
    u_cpu->fetch_pc_23(fetch_pc_23_sig);
    u_cpu->fetch_pc_24(fetch_pc_24_sig);
    u_cpu->fetch_pc_25(fetch_pc_25_sig);
    u_cpu->fetch_pc_26(fetch_pc_26_sig);
    u_cpu->fetch_pc_27(fetch_pc_27_sig);
    u_cpu->fetch_pc_28(fetch_pc_28_sig);
    u_cpu->fetch_pc_29(fetch_pc_29_sig);
    u_cpu->fetch_pc_30(fetch_pc_30_sig);
    u_cpu->fetch_pc_31(fetch_pc_31_sig);
    u_cpu->dmem_req_addr_0(dmem_req_addr_0_sig);
    u_cpu->dmem_req_addr_1(dmem_req_addr_1_sig);
    u_cpu->dmem_req_addr_2(dmem_req_addr_2_sig);
    u_cpu->dmem_req_addr_3(dmem_req_addr_3_sig);
    u_cpu->dmem_req_addr_4(dmem_req_addr_4_sig);
    u_cpu->dmem_req_addr_5(dmem_req_addr_5_sig);
    u_cpu->dmem_req_addr_6(dmem_req_addr_6_sig);
    u_cpu->dmem_req_addr_7(dmem_req_addr_7_sig);
    u_cpu->dmem_req_addr_8(dmem_req_addr_8_sig);
    u_cpu->dmem_req_addr_9(dmem_req_addr_9_sig);
    u_cpu->dmem_req_addr_10(dmem_req_addr_10_sig);
    u_cpu->dmem_req_addr_11(dmem_req_addr_11_sig);
    u_cpu->dmem_req_addr_12(dmem_req_addr_12_sig);
    u_cpu->dmem_req_addr_13(dmem_req_addr_13_sig);
    u_cpu->dmem_req_addr_14(dmem_req_addr_14_sig);
    u_cpu->dmem_req_addr_15(dmem_req_addr_15_sig);
    u_cpu->dmem_req_addr_16(dmem_req_addr_16_sig);
    u_cpu->dmem_req_addr_17(dmem_req_addr_17_sig);
    u_cpu->dmem_req_addr_18(dmem_req_addr_18_sig);
    u_cpu->dmem_req_addr_19(dmem_req_addr_19_sig);
    u_cpu->dmem_req_addr_20(dmem_req_addr_20_sig);
    u_cpu->dmem_req_addr_21(dmem_req_addr_21_sig);
    u_cpu->dmem_req_addr_22(dmem_req_addr_22_sig);
    u_cpu->dmem_req_addr_23(dmem_req_addr_23_sig);
    u_cpu->dmem_req_addr_24(dmem_req_addr_24_sig);
    u_cpu->dmem_req_addr_25(dmem_req_addr_25_sig);
    u_cpu->dmem_req_addr_26(dmem_req_addr_26_sig);
    u_cpu->dmem_req_addr_27(dmem_req_addr_27_sig);
    u_cpu->dmem_req_addr_28(dmem_req_addr_28_sig);
    u_cpu->dmem_req_addr_29(dmem_req_addr_29_sig);
    u_cpu->dmem_req_addr_30(dmem_req_addr_30_sig);
    u_cpu->dmem_req_addr_31(dmem_req_addr_31_sig);
    u_cpu->dmem_req_data_0(dmem_req_data_0_sig);
    u_cpu->dmem_req_data_1(dmem_req_data_1_sig);
    u_cpu->dmem_req_data_2(dmem_req_data_2_sig);
    u_cpu->dmem_req_data_3(dmem_req_data_3_sig);
    u_cpu->dmem_req_data_4(dmem_req_data_4_sig);
    u_cpu->dmem_req_data_5(dmem_req_data_5_sig);
    u_cpu->dmem_req_data_6(dmem_req_data_6_sig);
    u_cpu->dmem_req_data_7(dmem_req_data_7_sig);
    u_cpu->dmem_req_data_8(dmem_req_data_8_sig);
    u_cpu->dmem_req_data_9(dmem_req_data_9_sig);
    u_cpu->dmem_req_data_10(dmem_req_data_10_sig);
    u_cpu->dmem_req_data_11(dmem_req_data_11_sig);
    u_cpu->dmem_req_data_12(dmem_req_data_12_sig);
    u_cpu->dmem_req_data_13(dmem_req_data_13_sig);
    u_cpu->dmem_req_data_14(dmem_req_data_14_sig);
    u_cpu->dmem_req_data_15(dmem_req_data_15_sig);
    u_cpu->dmem_req_data_16(dmem_req_data_16_sig);
    u_cpu->dmem_req_data_17(dmem_req_data_17_sig);
    u_cpu->dmem_req_data_18(dmem_req_data_18_sig);
    u_cpu->dmem_req_data_19(dmem_req_data_19_sig);
    u_cpu->dmem_req_data_20(dmem_req_data_20_sig);
    u_cpu->dmem_req_data_21(dmem_req_data_21_sig);
    u_cpu->dmem_req_data_22(dmem_req_data_22_sig);
    u_cpu->dmem_req_data_23(dmem_req_data_23_sig);
    u_cpu->dmem_req_data_24(dmem_req_data_24_sig);
    u_cpu->dmem_req_data_25(dmem_req_data_25_sig);
    u_cpu->dmem_req_data_26(dmem_req_data_26_sig);
    u_cpu->dmem_req_data_27(dmem_req_data_27_sig);
    u_cpu->dmem_req_data_28(dmem_req_data_28_sig);
    u_cpu->dmem_req_data_29(dmem_req_data_29_sig);
    u_cpu->dmem_req_data_30(dmem_req_data_30_sig);
    u_cpu->dmem_req_data_31(dmem_req_data_31_sig);

    // Instantiate combinational imem model
    auto* u_imem = new ImemModel("u_imem");
    u_imem->fetch_pc_0(fetch_pc_0_sig);
    u_imem->fetch_pc_1(fetch_pc_1_sig);
    u_imem->fetch_pc_2(fetch_pc_2_sig);
    u_imem->fetch_pc_3(fetch_pc_3_sig);
    u_imem->fetch_pc_4(fetch_pc_4_sig);
    u_imem->fetch_pc_5(fetch_pc_5_sig);
    u_imem->fetch_pc_6(fetch_pc_6_sig);
    u_imem->fetch_pc_7(fetch_pc_7_sig);
    u_imem->fetch_pc_8(fetch_pc_8_sig);
    u_imem->fetch_pc_9(fetch_pc_9_sig);
    u_imem->fetch_pc_10(fetch_pc_10_sig);
    u_imem->fetch_pc_11(fetch_pc_11_sig);
    u_imem->fetch_pc_12(fetch_pc_12_sig);
    u_imem->fetch_pc_13(fetch_pc_13_sig);
    u_imem->fetch_pc_14(fetch_pc_14_sig);
    u_imem->fetch_pc_15(fetch_pc_15_sig);
    u_imem->fetch_pc_16(fetch_pc_16_sig);
    u_imem->fetch_pc_17(fetch_pc_17_sig);
    u_imem->fetch_pc_18(fetch_pc_18_sig);
    u_imem->fetch_pc_19(fetch_pc_19_sig);
    u_imem->fetch_pc_20(fetch_pc_20_sig);
    u_imem->fetch_pc_21(fetch_pc_21_sig);
    u_imem->fetch_pc_22(fetch_pc_22_sig);
    u_imem->fetch_pc_23(fetch_pc_23_sig);
    u_imem->fetch_pc_24(fetch_pc_24_sig);
    u_imem->fetch_pc_25(fetch_pc_25_sig);
    u_imem->fetch_pc_26(fetch_pc_26_sig);
    u_imem->fetch_pc_27(fetch_pc_27_sig);
    u_imem->fetch_pc_28(fetch_pc_28_sig);
    u_imem->fetch_pc_29(fetch_pc_29_sig);
    u_imem->fetch_pc_30(fetch_pc_30_sig);
    u_imem->fetch_pc_31(fetch_pc_31_sig);
    u_imem->imem_resp_data_0(imem_resp_data_0_sig);
    u_imem->imem_resp_data_1(imem_resp_data_1_sig);
    u_imem->imem_resp_data_2(imem_resp_data_2_sig);
    u_imem->imem_resp_data_3(imem_resp_data_3_sig);
    u_imem->imem_resp_data_4(imem_resp_data_4_sig);
    u_imem->imem_resp_data_5(imem_resp_data_5_sig);
    u_imem->imem_resp_data_6(imem_resp_data_6_sig);
    u_imem->imem_resp_data_7(imem_resp_data_7_sig);
    u_imem->imem_resp_data_8(imem_resp_data_8_sig);
    u_imem->imem_resp_data_9(imem_resp_data_9_sig);
    u_imem->imem_resp_data_10(imem_resp_data_10_sig);
    u_imem->imem_resp_data_11(imem_resp_data_11_sig);
    u_imem->imem_resp_data_12(imem_resp_data_12_sig);
    u_imem->imem_resp_data_13(imem_resp_data_13_sig);
    u_imem->imem_resp_data_14(imem_resp_data_14_sig);
    u_imem->imem_resp_data_15(imem_resp_data_15_sig);
    u_imem->imem_resp_data_16(imem_resp_data_16_sig);
    u_imem->imem_resp_data_17(imem_resp_data_17_sig);
    u_imem->imem_resp_data_18(imem_resp_data_18_sig);
    u_imem->imem_resp_data_19(imem_resp_data_19_sig);
    u_imem->imem_resp_data_20(imem_resp_data_20_sig);
    u_imem->imem_resp_data_21(imem_resp_data_21_sig);
    u_imem->imem_resp_data_22(imem_resp_data_22_sig);
    u_imem->imem_resp_data_23(imem_resp_data_23_sig);
    u_imem->imem_resp_data_24(imem_resp_data_24_sig);
    u_imem->imem_resp_data_25(imem_resp_data_25_sig);
    u_imem->imem_resp_data_26(imem_resp_data_26_sig);
    u_imem->imem_resp_data_27(imem_resp_data_27_sig);
    u_imem->imem_resp_data_28(imem_resp_data_28_sig);
    u_imem->imem_resp_data_29(imem_resp_data_29_sig);
    u_imem->imem_resp_data_30(imem_resp_data_30_sig);
    u_imem->imem_resp_data_31(imem_resp_data_31_sig);

    // Instantiate dmem model (manually clocked, not SC_MODULE)
    auto* u_dmem = new DmemModel(dmem_req_valid_sig, dmem_req_we_sig,
        dmem_req_ready_sig, dmem_resp_valid_sig,
        dmem_req_addr_sigs, dmem_req_data_sigs, dmem_resp_data_sigs);

    // Constants
    zero_sig.write(false);
    one_sig.write(true);

    // Trigger SystemC elaboration (binds all ports)
    sc_start(SC_ZERO_TIME);

    // Reset: hold reset high for 5 cycles
    reset_sig.write(true);
    for (int r = 0; r < 5; r++) {
        u_cpu->eval_seq_all();
        for (int s = 0; s < 50; s++) { u_cpu->eval_comb_all(); sc_start(SC_ZERO_TIME); }
    }
    reset_sig.write(false);

    // Simulation loop: fully manual Verilator-style evaluation.
    // No sc_clock needed — all timing is explicit.
    bool done = false;
    uint32_t cycle = 0;
    printf("Simulation started (timeout=%u)\n", timeout);

    while (!done && cycle < timeout) {
        // 1. DmemModel: respond to pending loads, handle new requests
        u_dmem->tick();
        sc_start(SC_ZERO_TIME);  // flush dmem writes

        // 2. Latch all CPU DFFs (captures comb outputs from prev cycle)
        u_cpu->eval_seq_all();
        sc_start(SC_ZERO_TIME);  // flush DFF outputs

        // 3. Settle combinational logic (multiple passes for hierarchy)
        // Each pass: CPU comb -> flush -> ImemModel reacts -> flush
        for (int settle = 0; settle < 50; settle++) {
            u_cpu->eval_comb_all();
            sc_start(SC_ZERO_TIME);
        }
        cycle++;

        // Check tohost from DmemModel
        if (u_dmem->test_done) {
            done = true;
            printf("\nTEST %s\n", u_dmem->test_data == 1 ? "PASS" : "FAIL");
            printf("  Cycle: %u\ntohost: 0x%08x\n", cycle, u_dmem->test_data);
        }

        if (cycle % 10000 == 0)
            printf("  [%u cycles] PC=0x%08x\n", cycle, get_fetch_pc(fetch_pc_sigs));
    }

    if (!done) {
        printf("TIMEOUT at cycle %u PC=0x%08x\n", cycle, get_fetch_pc(fetch_pc_sigs));
    }
    printf("Total cycles: %u\n", cycle);
    delete u_dmem;
    delete u_imem;
    delete u_cpu;
    // Note: sc_stop() not called; process exits directly.
    return done ? 0 : 1;
}
