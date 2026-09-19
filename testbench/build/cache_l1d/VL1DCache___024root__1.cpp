// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VL1DCache.h for the primary calling header

#include "VL1DCache__pch.h"

void VL1DCache___024root___nba_comb__TOP__0(VL1DCache___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VL1DCache___024root___nba_comb__TOP__0\n"); );
    VL1DCache__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    vlSelfRef.L1DCache__DOT____Vcellinp__u_data_word_mux_w1__in1 
        = vlSelfRef.L1DCache__DOT__data_ram_w1[vlSelfRef.L1DCache__DOT__data_rd_addr][1U];
    vlSelfRef.L1DCache__DOT____Vcellinp__u_data_word_mux_w1__in3 
        = vlSelfRef.L1DCache__DOT__data_ram_w1[vlSelfRef.L1DCache__DOT__data_rd_addr][3U];
    vlSelfRef.L1DCache__DOT____Vcellinp__u_data_word_mux_w1__in5 
        = vlSelfRef.L1DCache__DOT__data_ram_w1[vlSelfRef.L1DCache__DOT__data_rd_addr][5U];
    vlSelfRef.L1DCache__DOT____Vcellinp__u_data_word_mux_w1__in7 
        = vlSelfRef.L1DCache__DOT__data_ram_w1[vlSelfRef.L1DCache__DOT__data_rd_addr][7U];
    vlSelfRef.L1DCache__DOT____Vcellinp__u_data_word_mux_w0__in1 
        = vlSelfRef.L1DCache__DOT__data_ram_w0[vlSelfRef.L1DCache__DOT__data_rd_addr][1U];
    vlSelfRef.L1DCache__DOT____Vcellinp__u_data_word_mux_w0__in3 
        = vlSelfRef.L1DCache__DOT__data_ram_w0[vlSelfRef.L1DCache__DOT__data_rd_addr][3U];
    vlSelfRef.L1DCache__DOT____Vcellinp__u_data_word_mux_w0__in5 
        = vlSelfRef.L1DCache__DOT__data_ram_w0[vlSelfRef.L1DCache__DOT__data_rd_addr][5U];
    vlSelfRef.L1DCache__DOT____Vcellinp__u_data_word_mux_w0__in7 
        = vlSelfRef.L1DCache__DOT__data_ram_w0[vlSelfRef.L1DCache__DOT__data_rd_addr][7U];
    if (vlSelfRef.L1DCache__DOT__pend_victim_q_reg) {
        vlSelfRef.wb_data[0U] = vlSelfRef.L1DCache__DOT__data_ram_w1
            [vlSelfRef.L1DCache__DOT__data_rd_addr][0U];
        vlSelfRef.wb_data[1U] = vlSelfRef.L1DCache__DOT__data_ram_w1
            [vlSelfRef.L1DCache__DOT__data_rd_addr][1U];
        vlSelfRef.wb_data[2U] = vlSelfRef.L1DCache__DOT__data_ram_w1
            [vlSelfRef.L1DCache__DOT__data_rd_addr][2U];
        vlSelfRef.wb_data[3U] = vlSelfRef.L1DCache__DOT__data_ram_w1
            [vlSelfRef.L1DCache__DOT__data_rd_addr][3U];
        vlSelfRef.wb_data[4U] = vlSelfRef.L1DCache__DOT__data_ram_w1
            [vlSelfRef.L1DCache__DOT__data_rd_addr][4U];
        vlSelfRef.wb_data[5U] = vlSelfRef.L1DCache__DOT__data_ram_w1
            [vlSelfRef.L1DCache__DOT__data_rd_addr][5U];
        vlSelfRef.wb_data[6U] = vlSelfRef.L1DCache__DOT__data_ram_w1
            [vlSelfRef.L1DCache__DOT__data_rd_addr][6U];
        vlSelfRef.wb_data[7U] = vlSelfRef.L1DCache__DOT__data_ram_w1
            [vlSelfRef.L1DCache__DOT__data_rd_addr][7U];
    } else {
        vlSelfRef.wb_data[0U] = vlSelfRef.L1DCache__DOT__data_ram_w0
            [vlSelfRef.L1DCache__DOT__data_rd_addr][0U];
        vlSelfRef.wb_data[1U] = vlSelfRef.L1DCache__DOT__data_ram_w0
            [vlSelfRef.L1DCache__DOT__data_rd_addr][1U];
        vlSelfRef.wb_data[2U] = vlSelfRef.L1DCache__DOT__data_ram_w0
            [vlSelfRef.L1DCache__DOT__data_rd_addr][2U];
        vlSelfRef.wb_data[3U] = vlSelfRef.L1DCache__DOT__data_ram_w0
            [vlSelfRef.L1DCache__DOT__data_rd_addr][3U];
        vlSelfRef.wb_data[4U] = vlSelfRef.L1DCache__DOT__data_ram_w0
            [vlSelfRef.L1DCache__DOT__data_rd_addr][4U];
        vlSelfRef.wb_data[5U] = vlSelfRef.L1DCache__DOT__data_ram_w0
            [vlSelfRef.L1DCache__DOT__data_rd_addr][5U];
        vlSelfRef.wb_data[6U] = vlSelfRef.L1DCache__DOT__data_ram_w0
            [vlSelfRef.L1DCache__DOT__data_rd_addr][6U];
        vlSelfRef.wb_data[7U] = vlSelfRef.L1DCache__DOT__data_ram_w0
            [vlSelfRef.L1DCache__DOT__data_rd_addr][7U];
    }
}

void VL1DCache___024root___trigger_orInto__act_vec_vec(VlUnpacked<QData/*63:0*/, 1> &out, const VlUnpacked<QData/*63:0*/, 1> &in) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VL1DCache___024root___trigger_orInto__act_vec_vec\n"); );
    // Locals
    IData/*31:0*/ n;
    // Body
    n = 0U;
    do {
        out[n] = (out[n] | in[n]);
        n = ((IData)(1U) + n);
    } while ((0U >= n));
}

void VL1DCache___024root___trigger_clear__act(VlUnpacked<QData/*63:0*/, 1> &out) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VL1DCache___024root___trigger_clear__act\n"); );
    // Locals
    IData/*31:0*/ n;
    // Body
    n = 0U;
    do {
        out[n] = 0ULL;
        n = ((IData)(1U) + n);
    } while ((1U > n));
}

#ifdef VL_DEBUG
void VL1DCache___024root___eval_debug_assertions(VL1DCache___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VL1DCache___024root___eval_debug_assertions\n"); );
    VL1DCache__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    if (VL_UNLIKELY(((vlSelfRef.req_valid & 0xfeU)))) {
        Verilated::overWidthError("req_valid");
    }
    if (VL_UNLIKELY(((vlSelfRef.req_we & 0xfeU)))) {
        Verilated::overWidthError("req_we");
    }
    if (VL_UNLIKELY(((vlSelfRef.req_size & 0xfcU)))) {
        Verilated::overWidthError("req_size");
    }
    if (VL_UNLIKELY(((vlSelfRef.refill_valid & 0xfeU)))) {
        Verilated::overWidthError("refill_valid");
    }
    if (VL_UNLIKELY(((vlSelfRef.wb_ack & 0xfeU)))) {
        Verilated::overWidthError("wb_ack");
    }
    if (VL_UNLIKELY(((vlSelfRef.fence_i & 0xfeU)))) {
        Verilated::overWidthError("fence_i");
    }
    if (VL_UNLIKELY(((vlSelfRef.clock & 0xfeU)))) {
        Verilated::overWidthError("clock");
    }
    if (VL_UNLIKELY(((vlSelfRef.reset & 0xfeU)))) {
        Verilated::overWidthError("reset");
    }
}
#endif  // VL_DEBUG
