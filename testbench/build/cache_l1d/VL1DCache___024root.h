// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See VL1DCache.h for the primary calling header

#ifndef VERILATED_VL1DCACHE___024ROOT_H_
#define VERILATED_VL1DCACHE___024ROOT_H_  // guard

#include "verilated.h"


class VL1DCache__Syms;

class alignas(VL_CACHE_LINE_BYTES) VL1DCache___024root final {
  public:

    // DESIGN SPECIFIC STATE
    // Anonymous structures to workaround compiler member-count bugs
    struct {
        VL_IN8(clock,0,0);
        VL_IN8(reset,0,0);
        VL_IN8(req_valid,0,0);
        VL_IN8(req_we,0,0);
        VL_IN8(req_size,1,0);
        VL_IN8(refill_valid,0,0);
        VL_IN8(wb_ack,0,0);
        VL_IN8(fence_i,0,0);
        VL_OUT8(resp_valid,0,0);
        VL_OUT8(miss_valid,0,0);
        VL_OUT8(wb_valid,0,0);
        VL_OUT8(stall,0,0);
        VL_OUT8(fence_i_busy,0,0);
        CData/*1:0*/ L1DCache__DOT__data_rd_addr;
        CData/*3:0*/ L1DCache__DOT__valid_dec_w0;
        CData/*0:0*/ L1DCache__DOT__way0_valid_sel;
        CData/*0:0*/ L1DCache__DOT__way1_valid_sel;
        CData/*0:0*/ L1DCache__DOT__victim_needs_wb;
        CData/*0:0*/ L1DCache__DOT__way1_hit;
        CData/*0:0*/ L1DCache__DOT__hit;
        CData/*0:0*/ L1DCache__DOT__miss_detect;
        CData/*0:0*/ L1DCache__DOT__miss_detect_clean;
        CData/*0:0*/ L1DCache__DOT__victim_lru;
        CData/*0:0*/ L1DCache__DOT__write_hit;
        CData/*7:0*/ L1DCache__DOT__wdc;
        CData/*3:0*/ L1DCache__DOT__rfs_0;
        CData/*3:0*/ L1DCache__DOT__rfe_0;
        CData/*3:0*/ L1DCache__DOT__whs_0;
        CData/*3:0*/ L1DCache__DOT__rfe_1;
        CData/*0:0*/ L1DCache__DOT__is_word;
        CData/*0:0*/ L1DCache__DOT__be0_h;
        CData/*0:0*/ L1DCache__DOT__be2_h;
        CData/*0:0*/ L1DCache__DOT__is_refill_wait;
        CData/*0:0*/ L1DCache__DOT__refill_done;
        CData/*1:0*/ L1DCache__DOT__data_wr_addr_w0;
        CData/*3:0*/ L1DCache__DOT__lru_en;
        CData/*3:0*/ L1DCache__DOT__lru_nv;
        CData/*2:0*/ L1DCache__DOT__fsm_q_reg;
        CData/*0:0*/ L1DCache__DOT__pend_victim_q_reg;
        CData/*3:0*/ L1DCache__DOT__lru_q_reg;
        CData/*7:0*/ L1DCache__DOT__valid_q_reg;
        CData/*7:0*/ L1DCache__DOT__dirty_q_reg;
        CData/*0:0*/ __VdfgRegularize_h6e95ff9d_0_1;
        CData/*0:0*/ __Vdly__L1DCache__DOT__pend_victim_q_reg;
        CData/*0:0*/ __Vtrigprevexpr___TOP__req_valid__0;
        CData/*0:0*/ __Vtrigprevexpr___TOP__req_we__0;
        CData/*1:0*/ __Vtrigprevexpr___TOP__req_size__0;
        CData/*0:0*/ __Vtrigprevexpr___TOP__refill_valid__0;
        CData/*0:0*/ __Vtrigprevexpr___TOP__wb_ack__0;
        CData/*0:0*/ __Vtrigprevexpr___TOP__fence_i__0;
        CData/*0:0*/ __Vtrigprevexpr___TOP__clock__0;
        CData/*0:0*/ __Vtrigprevexpr___TOP__reset__0;
        CData/*0:0*/ __VicoDidInit;
        CData/*0:0*/ __Vtrigprevexpr___TOP__clock__1;
        CData/*0:0*/ __Vtrigprevexpr___TOP__reset__1;
        SData/*15:0*/ __VdfgRegularize_h6e95ff9d_0_0;
        VL_IN(req_addr,31,0);
        VL_INW(refill_data,255,0,8);
        VL_OUT(miss_addr,31,0);
        VL_OUT(wb_addr,31,0);
        VL_OUTW(wb_data,255,0,8);
        VlWide<8>/*255:0*/ L1DCache__DOT__ram_be_w0;
        VlWide<8>/*255:0*/ L1DCache__DOT__wr_data_w0;
        IData/*24:0*/ L1DCache__DOT__tag_q_w0_s0;
    };
    struct {
        IData/*24:0*/ L1DCache__DOT__tag_q_w0_s1;
        IData/*24:0*/ L1DCache__DOT__tag_q_w0_s2;
        IData/*24:0*/ L1DCache__DOT__tag_q_w0_s3;
        IData/*24:0*/ L1DCache__DOT__tag_q_w1_s0;
        IData/*24:0*/ L1DCache__DOT__tag_q_w1_s1;
        IData/*24:0*/ L1DCache__DOT__tag_q_w1_s2;
        IData/*24:0*/ L1DCache__DOT__tag_q_w1_s3;
        IData/*31:0*/ L1DCache__DOT__pend_q_reg;
        IData/*31:0*/ L1DCache__DOT____Vcellinp__u_data_word_mux_w0__in7;
        IData/*31:0*/ L1DCache__DOT____Vcellinp__u_data_word_mux_w0__in5;
        IData/*31:0*/ L1DCache__DOT____Vcellinp__u_data_word_mux_w0__in3;
        IData/*31:0*/ L1DCache__DOT____Vcellinp__u_data_word_mux_w0__in1;
        IData/*31:0*/ L1DCache__DOT____Vcellinp__u_data_word_mux_w1__in7;
        IData/*31:0*/ L1DCache__DOT____Vcellinp__u_data_word_mux_w1__in5;
        IData/*31:0*/ L1DCache__DOT____Vcellinp__u_data_word_mux_w1__in3;
        IData/*31:0*/ L1DCache__DOT____Vcellinp__u_data_word_mux_w1__in1;
        IData/*31:0*/ __Vtrigprevexpr___TOP__req_addr__0;
        VlWide<8>/*255:0*/ __Vtrigprevexpr___TOP__refill_data__0;
        VL_IN64(req_wdata,63,0);
        VL_OUT64(resp_data,63,0);
        QData/*63:0*/ __Vtrigprevexpr___TOP__req_wdata__0;
        VlUnpacked<VlWide<8>/*255:0*/, 4> L1DCache__DOT__data_ram_w0;
        VlUnpacked<VlWide<8>/*255:0*/, 4> L1DCache__DOT__data_ram_w1;
        VlUnpacked<QData/*63:0*/, 1> __VstlTriggered;
        VlUnpacked<QData/*63:0*/, 2> __VicoTriggered;
        VlUnpacked<QData/*63:0*/, 1> __VactTriggered;
        VlUnpacked<QData/*63:0*/, 1> __VnbaTriggered;
    };

    // INTERNAL VARIABLES
    VL1DCache__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    VL1DCache___024root(VL1DCache__Syms* symsp, const char* namep);
    ~VL1DCache___024root();
    VL_UNCOPYABLE(VL1DCache___024root);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
};


#endif  // guard
