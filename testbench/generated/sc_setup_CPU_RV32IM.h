// Auto-generated thin header for CPU setup. DO NOT EDIT.
#ifndef SC_SETUP_CPU_RV32IM_H
#define SC_SETUP_CPU_RV32IM_H

#include <systemc.h>

// Opaque handle to CPU_RV32IM instance + bound ports
struct CpuCtx {
    void* cpu;
    void eval_seq_all();
    void eval_comb_all();
};

// Create, bind ports (ports array order matches circuit definition), and return context
CpuCtx* cpu_create(const char* name, sc_clock& clk, sc_signal<bool>& reset_sig,
                    sc_signal<bool>* ports[], int num_ports);
void cpu_delete(CpuCtx* ctx);

#endif // SC_SETUP_CPU_RV32IM_H
