// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VL1DCache.h for the primary calling header

#include "VL1DCache__pch.h"

void VL1DCache___024root___eval_sample(VL1DCache___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VL1DCache___024root___eval_sample\n"); );
    VL1DCache__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
}

void VL1DCache___024root___eval_triggers_vec__ico(VL1DCache___024root* vlSelf);
#ifdef VL_DEBUG
VL_ATTR_COLD void VL1DCache___024root___dump_triggers__ico(const VlUnpacked<QData/*63:0*/, 2> &triggers, const std::string &tag);
#endif  // VL_DEBUG
bool VL1DCache___024root___trigger_anySet__ico(const VlUnpacked<QData/*63:0*/, 2> &in);
void VL1DCache___024root___eval_body__ico(VL1DCache___024root* vlSelf);

bool VL1DCache___024root___eval_ico(VL1DCache___024root* vlSelf, CData/*0:0*/ firstIteration) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VL1DCache___024root___eval_ico\n"); );
    VL1DCache__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Locals
    CData/*0:0*/ __VicoExecute;
    // Body
    vlSelfRef.__VicoTriggered[1U] = ((0xfffffffffffffffeULL 
                                      & vlSelfRef.__VicoTriggered[1U]) 
                                     | (IData)((IData)(firstIteration)));
    VL1DCache___024root___eval_triggers_vec__ico(vlSelf);
#ifdef VL_DEBUG
    if (VL_UNLIKELY(vlSymsp->_vm_contextp__->debug())) {
        VL1DCache___024root___dump_triggers__ico(vlSelfRef.__VicoTriggered, "ico"s);
    }
#endif
    __VicoExecute = VL1DCache___024root___trigger_anySet__ico(vlSelfRef.__VicoTriggered);
    if (__VicoExecute) {
        VL1DCache___024root___eval_body__ico(vlSelf);
    }
    return (__VicoExecute);
}

#ifdef VL_DEBUG
VL_ATTR_COLD void VL1DCache___024root___dump_triggers__act(const VlUnpacked<QData/*63:0*/, 1> &triggers, const std::string &tag);
#endif  // VL_DEBUG
void VL1DCache___024root___trigger_orInto__act_vec_vec(VlUnpacked<QData/*63:0*/, 1> &out, const VlUnpacked<QData/*63:0*/, 1> &in);

bool VL1DCache___024root___eval_act(VL1DCache___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VL1DCache___024root___eval_act\n"); );
    VL1DCache__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    {
        // Inlined CFunc: _eval_triggers_vec__act
        vlSelfRef.__VactTriggered[0U] = (QData)((IData)(
                                                        ((((IData)(vlSelfRef.reset) 
                                                           & (~ (IData)(vlSelfRef.__Vtrigprevexpr___TOP__reset__1))) 
                                                          << 1U) 
                                                         | ((IData)(vlSelfRef.clock) 
                                                            & (~ (IData)(vlSelfRef.__Vtrigprevexpr___TOP__clock__1))))));
        vlSelfRef.__Vtrigprevexpr___TOP__clock__1 = vlSelfRef.clock;
        vlSelfRef.__Vtrigprevexpr___TOP__reset__1 = vlSelfRef.reset;
    }
#ifdef VL_DEBUG
    if (VL_UNLIKELY(vlSymsp->_vm_contextp__->debug())) {
        VL1DCache___024root___dump_triggers__act(vlSelfRef.__VactTriggered, "act"s);
    }
#endif
    VL1DCache___024root___trigger_orInto__act_vec_vec(vlSelfRef.__VnbaTriggered, vlSelfRef.__VactTriggered);
    return (0U);
}

bool VL1DCache___024root___eval_inact(VL1DCache___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VL1DCache___024root___eval_inact\n"); );
    VL1DCache__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    return (0U);
}

bool VL1DCache___024root___trigger_anySet__act(const VlUnpacked<QData/*63:0*/, 1> &in);
void VL1DCache___024root___nba_sequent__TOP__0(VL1DCache___024root* vlSelf);
void VL1DCache___024root___nba_sequent__TOP__1(VL1DCache___024root* vlSelf);
void VL1DCache___024root___nba_sequent__TOP__2(VL1DCache___024root* vlSelf);
void VL1DCache___024root___nba_comb__TOP__0(VL1DCache___024root* vlSelf);
void VL1DCache___024root___trigger_clear__act(VlUnpacked<QData/*63:0*/, 1> &out);

bool VL1DCache___024root___eval_nba(VL1DCache___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VL1DCache___024root___eval_nba\n"); );
    VL1DCache__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Locals
    CData/*0:0*/ __VnbaExecute;
    // Body
    __VnbaExecute = VL1DCache___024root___trigger_anySet__act(vlSelfRef.__VnbaTriggered);
    if (__VnbaExecute) {
        {
            // Inlined CFunc: _eval_body__nba
            if ((3ULL & vlSelfRef.__VnbaTriggered[0U])) {
                VL1DCache___024root___nba_sequent__TOP__0(vlSelf);
            }
            if ((1ULL & vlSelfRef.__VnbaTriggered[0U])) {
                VL1DCache___024root___nba_sequent__TOP__1(vlSelf);
            }
            if ((3ULL & vlSelfRef.__VnbaTriggered[0U])) {
                VL1DCache___024root___nba_sequent__TOP__2(vlSelf);
            }
            if ((3ULL & vlSelfRef.__VnbaTriggered[0U])) {
                VL1DCache___024root___nba_comb__TOP__0(vlSelf);
            }
        }
        VL1DCache___024root___trigger_clear__act(vlSelfRef.__VnbaTriggered);
    }
    return (__VnbaExecute);
}

bool VL1DCache___024root___eval_obs(VL1DCache___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VL1DCache___024root___eval_obs\n"); );
    VL1DCache__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    return (0U);
}

bool VL1DCache___024root___eval_react(VL1DCache___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VL1DCache___024root___eval_react\n"); );
    VL1DCache__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    return (0U);
}

void VL1DCache___024root___eval_postponed(VL1DCache___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VL1DCache___024root___eval_postponed\n"); );
    VL1DCache__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
}

void VL1DCache___024root___eval_triggers_vec__ico(VL1DCache___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VL1DCache___024root___eval_triggers_vec__ico\n"); );
    VL1DCache__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    vlSelfRef.__VicoTriggered[0U] = (QData)((IData)(
                                                    (((((IData)(vlSelfRef.reset) 
                                                        != (IData)(vlSelfRef.__Vtrigprevexpr___TOP__reset__0)) 
                                                       << 0x0000000aU) 
                                                      | ((((IData)(vlSelfRef.clock) 
                                                           != (IData)(vlSelfRef.__Vtrigprevexpr___TOP__clock__0)) 
                                                          << 9U) 
                                                         | (((IData)(vlSelfRef.fence_i) 
                                                             != (IData)(vlSelfRef.__Vtrigprevexpr___TOP__fence_i__0)) 
                                                            << 8U))) 
                                                     | (((((((IData)(vlSelfRef.wb_ack) 
                                                             != (IData)(vlSelfRef.__Vtrigprevexpr___TOP__wb_ack__0)) 
                                                            << 3U) 
                                                           | ((0U 
                                                               != 
                                                               ((((((((vlSelfRef.refill_data[0U] 
                                                                       ^ vlSelfRef.__Vtrigprevexpr___TOP__refill_data__0[0U]) 
                                                                      | (vlSelfRef.refill_data[1U] 
                                                                         ^ vlSelfRef.__Vtrigprevexpr___TOP__refill_data__0[1U])) 
                                                                     | (vlSelfRef.refill_data[2U] 
                                                                        ^ vlSelfRef.__Vtrigprevexpr___TOP__refill_data__0[2U])) 
                                                                    | (vlSelfRef.refill_data[3U] 
                                                                       ^ vlSelfRef.__Vtrigprevexpr___TOP__refill_data__0[3U])) 
                                                                   | (vlSelfRef.refill_data[4U] 
                                                                      ^ vlSelfRef.__Vtrigprevexpr___TOP__refill_data__0[4U])) 
                                                                  | (vlSelfRef.refill_data[5U] 
                                                                     ^ vlSelfRef.__Vtrigprevexpr___TOP__refill_data__0[5U])) 
                                                                 | (vlSelfRef.refill_data[6U] 
                                                                    ^ vlSelfRef.__Vtrigprevexpr___TOP__refill_data__0[6U])) 
                                                                | (vlSelfRef.refill_data[7U] 
                                                                   ^ vlSelfRef.__Vtrigprevexpr___TOP__refill_data__0[7U]))) 
                                                              << 2U)) 
                                                          | ((((IData)(vlSelfRef.refill_valid) 
                                                               != (IData)(vlSelfRef.__Vtrigprevexpr___TOP__refill_valid__0)) 
                                                              << 1U) 
                                                             | ((IData)(vlSelfRef.req_size) 
                                                                != (IData)(vlSelfRef.__Vtrigprevexpr___TOP__req_size__0)))) 
                                                         << 4U) 
                                                        | ((((vlSelfRef.req_wdata 
                                                              != vlSelfRef.__Vtrigprevexpr___TOP__req_wdata__0) 
                                                             << 3U) 
                                                            | ((vlSelfRef.req_addr 
                                                                != vlSelfRef.__Vtrigprevexpr___TOP__req_addr__0) 
                                                               << 2U)) 
                                                           | ((((IData)(vlSelfRef.req_we) 
                                                                != (IData)(vlSelfRef.__Vtrigprevexpr___TOP__req_we__0)) 
                                                               << 1U) 
                                                              | ((IData)(vlSelfRef.req_valid) 
                                                                 != (IData)(vlSelfRef.__Vtrigprevexpr___TOP__req_valid__0))))))));
    vlSelfRef.__Vtrigprevexpr___TOP__req_valid__0 = vlSelfRef.req_valid;
    vlSelfRef.__Vtrigprevexpr___TOP__req_we__0 = vlSelfRef.req_we;
    vlSelfRef.__Vtrigprevexpr___TOP__req_addr__0 = vlSelfRef.req_addr;
    vlSelfRef.__Vtrigprevexpr___TOP__req_wdata__0 = vlSelfRef.req_wdata;
    vlSelfRef.__Vtrigprevexpr___TOP__req_size__0 = vlSelfRef.req_size;
    vlSelfRef.__Vtrigprevexpr___TOP__refill_valid__0 
        = vlSelfRef.refill_valid;
    vlSelfRef.__Vtrigprevexpr___TOP__refill_data__0[0U] 
        = vlSelfRef.refill_data[0U];
    vlSelfRef.__Vtrigprevexpr___TOP__refill_data__0[1U] 
        = vlSelfRef.refill_data[1U];
    vlSelfRef.__Vtrigprevexpr___TOP__refill_data__0[2U] 
        = vlSelfRef.refill_data[2U];
    vlSelfRef.__Vtrigprevexpr___TOP__refill_data__0[3U] 
        = vlSelfRef.refill_data[3U];
    vlSelfRef.__Vtrigprevexpr___TOP__refill_data__0[4U] 
        = vlSelfRef.refill_data[4U];
    vlSelfRef.__Vtrigprevexpr___TOP__refill_data__0[5U] 
        = vlSelfRef.refill_data[5U];
    vlSelfRef.__Vtrigprevexpr___TOP__refill_data__0[6U] 
        = vlSelfRef.refill_data[6U];
    vlSelfRef.__Vtrigprevexpr___TOP__refill_data__0[7U] 
        = vlSelfRef.refill_data[7U];
    vlSelfRef.__Vtrigprevexpr___TOP__wb_ack__0 = vlSelfRef.wb_ack;
    vlSelfRef.__Vtrigprevexpr___TOP__fence_i__0 = vlSelfRef.fence_i;
    vlSelfRef.__Vtrigprevexpr___TOP__clock__0 = vlSelfRef.clock;
    vlSelfRef.__Vtrigprevexpr___TOP__reset__0 = vlSelfRef.reset;
    if (VL_UNLIKELY(((1U & (~ (IData)(vlSelfRef.__VicoDidInit)))))) {
        vlSelfRef.__VicoDidInit = 1U;
        vlSelfRef.__VicoTriggered[0U] = (1ULL | vlSelfRef.__VicoTriggered[0U]);
        vlSelfRef.__VicoTriggered[0U] = (2ULL | vlSelfRef.__VicoTriggered[0U]);
        vlSelfRef.__VicoTriggered[0U] = (4ULL | vlSelfRef.__VicoTriggered[0U]);
        vlSelfRef.__VicoTriggered[0U] = (8ULL | vlSelfRef.__VicoTriggered[0U]);
        vlSelfRef.__VicoTriggered[0U] = (0x0000000000000010ULL 
                                         | vlSelfRef.__VicoTriggered[0U]);
        vlSelfRef.__VicoTriggered[0U] = (0x0000000000000020ULL 
                                         | vlSelfRef.__VicoTriggered[0U]);
        vlSelfRef.__VicoTriggered[0U] = (0x0000000000000040ULL 
                                         | vlSelfRef.__VicoTriggered[0U]);
        vlSelfRef.__VicoTriggered[0U] = (0x0000000000000080ULL 
                                         | vlSelfRef.__VicoTriggered[0U]);
        vlSelfRef.__VicoTriggered[0U] = (0x0000000000000100ULL 
                                         | vlSelfRef.__VicoTriggered[0U]);
        vlSelfRef.__VicoTriggered[0U] = (0x0000000000000200ULL 
                                         | vlSelfRef.__VicoTriggered[0U]);
        vlSelfRef.__VicoTriggered[0U] = (0x0000000000000400ULL 
                                         | vlSelfRef.__VicoTriggered[0U]);
    }
}

bool VL1DCache___024root___trigger_anySet__ico(const VlUnpacked<QData/*63:0*/, 2> &in) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VL1DCache___024root___trigger_anySet__ico\n"); );
    // Locals
    IData/*31:0*/ n;
    // Body
    n = 0U;
    do {
        if (in[n]) {
            return (1U);
        }
        n = ((IData)(1U) + n);
    } while ((2U > n));
    return (0U);
}

extern const VlUnpacked<CData/*2:0*/, 64> VL1DCache__ConstPool__TABLE_h8d06dde6_0;

void VL1DCache___024root___ico_sequent__TOP__0(VL1DCache___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VL1DCache___024root___ico_sequent__TOP__0\n"); );
    VL1DCache__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Locals
    IData/*24:0*/ L1DCache__DOT__sel_tag_w0;
    L1DCache__DOT__sel_tag_w0 = 0;
    IData/*24:0*/ L1DCache__DOT__sel_tag_w1;
    L1DCache__DOT__sel_tag_w1 = 0;
    IData/*24:0*/ L1DCache__DOT__u_tag_cmp_w1__DOT__diff;
    L1DCache__DOT__u_tag_cmp_w1__DOT__diff = 0;
    SData/*11:0*/ L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0;
    L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0 = 0;
    IData/*24:0*/ L1DCache__DOT__u_tag_cmp_w0__DOT__diff;
    L1DCache__DOT__u_tag_cmp_w0__DOT__diff = 0;
    SData/*11:0*/ L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0;
    L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0 = 0;
    // Body
    vlSelfRef.miss_addr = (((IData)(vlSelfRef.L1DCache__DOT__is_refill_wait)
                             ? (vlSelfRef.L1DCache__DOT__pend_q_reg 
                                >> 5U) : (vlSelfRef.req_addr 
                                          >> 5U)) << 5U);
    vlSelfRef.L1DCache__DOT__wdc = (((0x000000f0U & 
                                      ((- (IData)((1U 
                                                   & (vlSelfRef.req_addr 
                                                      >> 4U)))) 
                                       << 4U)) | (0x0000000fU 
                                                  & (- (IData)(
                                                               (1U 
                                                                & (~ 
                                                                   (vlSelfRef.req_addr 
                                                                    >> 4U))))))) 
                                    & (((((0x0000000cU 
                                           & ((- (IData)(
                                                         (1U 
                                                          & (vlSelfRef.req_addr 
                                                             >> 3U)))) 
                                              << 2U)) 
                                          | (3U & (- (IData)(
                                                             (1U 
                                                              & (~ 
                                                                 (vlSelfRef.req_addr 
                                                                  >> 3U))))))) 
                                         << 4U) | (
                                                   (0x0000000cU 
                                                    & ((- (IData)(
                                                                  (1U 
                                                                   & (vlSelfRef.req_addr 
                                                                      >> 3U)))) 
                                                       << 2U)) 
                                                   | (3U 
                                                      & (- (IData)(
                                                                   (1U 
                                                                    & (~ 
                                                                       (vlSelfRef.req_addr 
                                                                        >> 3U)))))))) 
                                       & ((((2U & (vlSelfRef.req_addr 
                                                   >> 1U)) 
                                            | (1U & 
                                               (~ (vlSelfRef.req_addr 
                                                   >> 2U)))) 
                                           << 6U) | 
                                          ((((2U & 
                                              (vlSelfRef.req_addr 
                                               >> 1U)) 
                                             | (1U 
                                                & (~ 
                                                   (vlSelfRef.req_addr 
                                                    >> 2U)))) 
                                            << 4U) 
                                           | ((((2U 
                                                 & (vlSelfRef.req_addr 
                                                    >> 1U)) 
                                                | (1U 
                                                   & (~ 
                                                      (vlSelfRef.req_addr 
                                                       >> 2U)))) 
                                               << 2U) 
                                              | ((2U 
                                                  & (vlSelfRef.req_addr 
                                                     >> 1U)) 
                                                 | (1U 
                                                    & (~ 
                                                       (vlSelfRef.req_addr 
                                                        >> 2U)))))))));
    vlSelfRef.L1DCache__DOT__valid_dec_w0 = (((0x0000000cU 
                                               & ((- (IData)(
                                                             (1U 
                                                              & (vlSelfRef.req_addr 
                                                                 >> 6U)))) 
                                                  << 2U)) 
                                              | (3U 
                                                 & (- (IData)(
                                                              (1U 
                                                               & (~ 
                                                                  (vlSelfRef.req_addr 
                                                                   >> 6U))))))) 
                                             & ((((2U 
                                                   & (vlSelfRef.req_addr 
                                                      >> 4U)) 
                                                  | (1U 
                                                     & (~ 
                                                        (vlSelfRef.req_addr 
                                                         >> 5U)))) 
                                                 << 2U) 
                                                | ((2U 
                                                    & (vlSelfRef.req_addr 
                                                       >> 4U)) 
                                                   | (1U 
                                                      & (~ 
                                                         (vlSelfRef.req_addr 
                                                          >> 5U))))));
    vlSelfRef.L1DCache__DOT__data_rd_addr = (3U & ((IData)(vlSelfRef.wb_valid)
                                                    ? 
                                                   (vlSelfRef.L1DCache__DOT__pend_q_reg 
                                                    >> 5U)
                                                    : 
                                                   (vlSelfRef.req_addr 
                                                    >> 5U)));
    vlSelfRef.L1DCache__DOT__victim_lru = (0U != ((IData)(vlSelfRef.L1DCache__DOT__lru_q_reg) 
                                                  & (IData)(vlSelfRef.L1DCache__DOT__valid_dec_w0)));
    vlSelfRef.L1DCache__DOT__way0_valid_sel = (0U != 
                                               ((IData)(vlSelfRef.L1DCache__DOT__valid_q_reg) 
                                                & (IData)(vlSelfRef.L1DCache__DOT__valid_dec_w0)));
    vlSelfRef.L1DCache__DOT__way1_valid_sel = (0U != 
                                               (((IData)(vlSelfRef.L1DCache__DOT__valid_q_reg) 
                                                 >> 4U) 
                                                & (IData)(vlSelfRef.L1DCache__DOT__valid_dec_w0)));
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
    L1DCache__DOT__sel_tag_w0 = (((~ (- (IData)((1U 
                                                 & ((IData)(vlSelfRef.L1DCache__DOT__data_rd_addr) 
                                                    >> 1U))))) 
                                  & (((~ (- (IData)(
                                                    (1U 
                                                     & (IData)(vlSelfRef.L1DCache__DOT__data_rd_addr))))) 
                                      & vlSelfRef.L1DCache__DOT__tag_q_w0_s0) 
                                     | (vlSelfRef.L1DCache__DOT__tag_q_w0_s1 
                                        & (- (IData)(
                                                     (1U 
                                                      & (IData)(vlSelfRef.L1DCache__DOT__data_rd_addr))))))) 
                                 | ((- (IData)((1U 
                                                & ((IData)(vlSelfRef.L1DCache__DOT__data_rd_addr) 
                                                   >> 1U)))) 
                                    & (((~ (- (IData)(
                                                      (1U 
                                                       & (IData)(vlSelfRef.L1DCache__DOT__data_rd_addr))))) 
                                        & vlSelfRef.L1DCache__DOT__tag_q_w0_s2) 
                                       | (vlSelfRef.L1DCache__DOT__tag_q_w0_s3 
                                          & (- (IData)(
                                                       (1U 
                                                        & (IData)(vlSelfRef.L1DCache__DOT__data_rd_addr))))))));
    L1DCache__DOT__sel_tag_w1 = (((~ (- (IData)((1U 
                                                 & ((IData)(vlSelfRef.L1DCache__DOT__data_rd_addr) 
                                                    >> 1U))))) 
                                  & (((~ (- (IData)(
                                                    (1U 
                                                     & (IData)(vlSelfRef.L1DCache__DOT__data_rd_addr))))) 
                                      & vlSelfRef.L1DCache__DOT__tag_q_w1_s0) 
                                     | (vlSelfRef.L1DCache__DOT__tag_q_w1_s1 
                                        & (- (IData)(
                                                     (1U 
                                                      & (IData)(vlSelfRef.L1DCache__DOT__data_rd_addr))))))) 
                                 | ((((~ (- (IData)(
                                                    (1U 
                                                     & (IData)(vlSelfRef.L1DCache__DOT__data_rd_addr))))) 
                                      & vlSelfRef.L1DCache__DOT__tag_q_w1_s2) 
                                     | (vlSelfRef.L1DCache__DOT__tag_q_w1_s3 
                                        & (- (IData)(
                                                     (1U 
                                                      & (IData)(vlSelfRef.L1DCache__DOT__data_rd_addr)))))) 
                                    & (- (IData)((1U 
                                                  & ((IData)(vlSelfRef.L1DCache__DOT__data_rd_addr) 
                                                     >> 1U))))));
    vlSelfRef.L1DCache__DOT__victim_needs_wb = (((IData)(vlSelfRef.L1DCache__DOT__victim_lru)
                                                  ? 
                                                 (0U 
                                                  != 
                                                  (((IData)(vlSelfRef.L1DCache__DOT__dirty_q_reg) 
                                                    >> 4U) 
                                                   & (IData)(vlSelfRef.L1DCache__DOT__valid_dec_w0)))
                                                  : 
                                                 (0U 
                                                  != 
                                                  ((IData)(vlSelfRef.L1DCache__DOT__dirty_q_reg) 
                                                   & (IData)(vlSelfRef.L1DCache__DOT__valid_dec_w0)))) 
                                                & ((IData)(vlSelfRef.L1DCache__DOT__victim_lru)
                                                    ? (IData)(vlSelfRef.L1DCache__DOT__way1_valid_sel)
                                                    : (IData)(vlSelfRef.L1DCache__DOT__way0_valid_sel)));
    L1DCache__DOT__u_tag_cmp_w0__DOT__diff = (0x01ffffffU 
                                              & ((vlSelfRef.req_addr 
                                                  >> 7U) 
                                                 ^ L1DCache__DOT__sel_tag_w0));
    vlSelfRef.wb_addr = ((((IData)(vlSelfRef.L1DCache__DOT__pend_victim_q_reg)
                            ? L1DCache__DOT__sel_tag_w1
                            : L1DCache__DOT__sel_tag_w0) 
                          << 7U) | ((IData)(vlSelfRef.L1DCache__DOT__data_rd_addr) 
                                    << 5U));
    L1DCache__DOT__u_tag_cmp_w1__DOT__diff = (0x01ffffffU 
                                              & ((vlSelfRef.req_addr 
                                                  >> 7U) 
                                                 ^ L1DCache__DOT__sel_tag_w1));
    L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0 
        = ((((((4U & (L1DCache__DOT__u_tag_cmp_w0__DOT__diff 
                      >> 0x00000014U)) | ((2U & (L1DCache__DOT__u_tag_cmp_w0__DOT__diff 
                                                 >> 0x00000013U)) 
                                          | (1U & (L1DCache__DOT__u_tag_cmp_w0__DOT__diff 
                                                   >> 0x00000012U)))) 
              << 9U) | (((4U & (L1DCache__DOT__u_tag_cmp_w0__DOT__diff 
                                >> 0x0000000eU)) | 
                         ((2U & (L1DCache__DOT__u_tag_cmp_w0__DOT__diff 
                                 >> 0x0000000dU)) | 
                          (1U & (L1DCache__DOT__u_tag_cmp_w0__DOT__diff 
                                 >> 0x0000000cU)))) 
                        << 6U)) | ((((4U & (L1DCache__DOT__u_tag_cmp_w0__DOT__diff 
                                            >> 8U)) 
                                     | ((2U & (L1DCache__DOT__u_tag_cmp_w0__DOT__diff 
                                               >> 7U)) 
                                        | (1U & (L1DCache__DOT__u_tag_cmp_w0__DOT__diff 
                                                 >> 6U)))) 
                                    << 3U) | ((4U & 
                                               (L1DCache__DOT__u_tag_cmp_w0__DOT__diff 
                                                >> 2U)) 
                                              | ((2U 
                                                  & (L1DCache__DOT__u_tag_cmp_w0__DOT__diff 
                                                     >> 1U)) 
                                                 | (1U 
                                                    & L1DCache__DOT__u_tag_cmp_w0__DOT__diff))))) 
           | (((((4U & (L1DCache__DOT__u_tag_cmp_w0__DOT__diff 
                        >> 0x00000015U)) | ((2U & (L1DCache__DOT__u_tag_cmp_w0__DOT__diff 
                                                   >> 0x00000014U)) 
                                            | (1U & 
                                               (L1DCache__DOT__u_tag_cmp_w0__DOT__diff 
                                                >> 0x00000013U)))) 
                << 9U) | (((4U & (L1DCache__DOT__u_tag_cmp_w0__DOT__diff 
                                  >> 0x0000000fU)) 
                           | ((2U & (L1DCache__DOT__u_tag_cmp_w0__DOT__diff 
                                     >> 0x0000000eU)) 
                              | (1U & (L1DCache__DOT__u_tag_cmp_w0__DOT__diff 
                                       >> 0x0000000dU)))) 
                          << 6U)) | ((((4U & (L1DCache__DOT__u_tag_cmp_w0__DOT__diff 
                                              >> 9U)) 
                                       | ((2U & (L1DCache__DOT__u_tag_cmp_w0__DOT__diff 
                                                 >> 8U)) 
                                          | (1U & (L1DCache__DOT__u_tag_cmp_w0__DOT__diff 
                                                   >> 7U)))) 
                                      << 3U) | ((4U 
                                                 & (L1DCache__DOT__u_tag_cmp_w0__DOT__diff 
                                                    >> 3U)) 
                                                | ((2U 
                                                    & (L1DCache__DOT__u_tag_cmp_w0__DOT__diff 
                                                       >> 2U)) 
                                                   | (1U 
                                                      & (L1DCache__DOT__u_tag_cmp_w0__DOT__diff 
                                                         >> 1U)))))));
    L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0 
        = ((((((4U & (L1DCache__DOT__u_tag_cmp_w1__DOT__diff 
                      >> 0x00000014U)) | ((2U & (L1DCache__DOT__u_tag_cmp_w1__DOT__diff 
                                                 >> 0x00000013U)) 
                                          | (1U & (L1DCache__DOT__u_tag_cmp_w1__DOT__diff 
                                                   >> 0x00000012U)))) 
              << 9U) | (((4U & (L1DCache__DOT__u_tag_cmp_w1__DOT__diff 
                                >> 0x0000000eU)) | 
                         ((2U & (L1DCache__DOT__u_tag_cmp_w1__DOT__diff 
                                 >> 0x0000000dU)) | 
                          (1U & (L1DCache__DOT__u_tag_cmp_w1__DOT__diff 
                                 >> 0x0000000cU)))) 
                        << 6U)) | ((((4U & (L1DCache__DOT__u_tag_cmp_w1__DOT__diff 
                                            >> 8U)) 
                                     | ((2U & (L1DCache__DOT__u_tag_cmp_w1__DOT__diff 
                                               >> 7U)) 
                                        | (1U & (L1DCache__DOT__u_tag_cmp_w1__DOT__diff 
                                                 >> 6U)))) 
                                    << 3U) | ((4U & 
                                               (L1DCache__DOT__u_tag_cmp_w1__DOT__diff 
                                                >> 2U)) 
                                              | ((2U 
                                                  & (L1DCache__DOT__u_tag_cmp_w1__DOT__diff 
                                                     >> 1U)) 
                                                 | (1U 
                                                    & L1DCache__DOT__u_tag_cmp_w1__DOT__diff))))) 
           | (((((4U & (L1DCache__DOT__u_tag_cmp_w1__DOT__diff 
                        >> 0x00000015U)) | ((2U & (L1DCache__DOT__u_tag_cmp_w1__DOT__diff 
                                                   >> 0x00000014U)) 
                                            | (1U & 
                                               (L1DCache__DOT__u_tag_cmp_w1__DOT__diff 
                                                >> 0x00000013U)))) 
                << 9U) | (((4U & (L1DCache__DOT__u_tag_cmp_w1__DOT__diff 
                                  >> 0x0000000fU)) 
                           | ((2U & (L1DCache__DOT__u_tag_cmp_w1__DOT__diff 
                                     >> 0x0000000eU)) 
                              | (1U & (L1DCache__DOT__u_tag_cmp_w1__DOT__diff 
                                       >> 0x0000000dU)))) 
                          << 6U)) | ((((4U & (L1DCache__DOT__u_tag_cmp_w1__DOT__diff 
                                              >> 9U)) 
                                       | ((2U & (L1DCache__DOT__u_tag_cmp_w1__DOT__diff 
                                                 >> 8U)) 
                                          | (1U & (L1DCache__DOT__u_tag_cmp_w1__DOT__diff 
                                                   >> 7U)))) 
                                      << 3U) | ((4U 
                                                 & (L1DCache__DOT__u_tag_cmp_w1__DOT__diff 
                                                    >> 3U)) 
                                                | ((2U 
                                                    & (L1DCache__DOT__u_tag_cmp_w1__DOT__diff 
                                                       >> 2U)) 
                                                   | (1U 
                                                      & (L1DCache__DOT__u_tag_cmp_w1__DOT__diff 
                                                         >> 1U)))))));
    vlSelfRef.L1DCache__DOT__way1_hit = ((~ ((VL1DCache__ConstPool__TABLE_h8d06dde6_0
                                              [((((
                                                   (4U 
                                                    & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                       >> 8U)) 
                                                   | ((2U 
                                                       & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                          >> 7U)) 
                                                      | (1U 
                                                         & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                            >> 6U)))) 
                                                  << 3U) 
                                                 | ((4U 
                                                     & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                        >> 2U)) 
                                                    | ((2U 
                                                        & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                           >> 1U)) 
                                                       | (1U 
                                                          & (IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0))))) 
                                                | ((((4U 
                                                      & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                         >> 9U)) 
                                                     | ((2U 
                                                         & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                            >> 8U)) 
                                                        | (1U 
                                                           & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                              >> 7U)))) 
                                                    << 3U) 
                                                   | ((4U 
                                                       & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                          >> 3U)) 
                                                      | ((2U 
                                                          & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                             >> 2U)) 
                                                         | (1U 
                                                            & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                               >> 1U))))))] 
                                              >> 2U) 
                                             | (VL1DCache__ConstPool__TABLE_h8d06dde6_0
                                                [((
                                                   (((4U 
                                                      & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                         >> 8U)) 
                                                     | ((2U 
                                                         & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                            >> 7U)) 
                                                        | (1U 
                                                           & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                              >> 6U)))) 
                                                    << 3U) 
                                                   | ((4U 
                                                       & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                          >> 2U)) 
                                                      | ((2U 
                                                          & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                             >> 1U)) 
                                                         | (1U 
                                                            & (IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0))))) 
                                                  | ((((4U 
                                                        & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                           >> 9U)) 
                                                       | ((2U 
                                                           & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                              >> 8U)) 
                                                          | (1U 
                                                             & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                                >> 7U)))) 
                                                      << 3U) 
                                                     | ((4U 
                                                         & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                            >> 3U)) 
                                                        | ((2U 
                                                            & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                               >> 2U)) 
                                                           | (1U 
                                                              & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                                 >> 1U))))))] 
                                                | ((L1DCache__DOT__u_tag_cmp_w1__DOT__diff 
                                                    >> 0x00000018U) 
                                                   | (VL1DCache__ConstPool__TABLE_h8d06dde6_0
                                                      [
                                                      (((((4U 
                                                           & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                              >> 8U)) 
                                                          | ((2U 
                                                              & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                                 >> 7U)) 
                                                             | (1U 
                                                                & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                                   >> 6U)))) 
                                                         << 3U) 
                                                        | ((4U 
                                                            & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                               >> 2U)) 
                                                           | ((2U 
                                                               & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                                  >> 1U)) 
                                                              | (1U 
                                                                 & (IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0))))) 
                                                       | ((((4U 
                                                             & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                                >> 9U)) 
                                                            | ((2U 
                                                                & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                                   >> 8U)) 
                                                               | (1U 
                                                                  & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                                     >> 7U)))) 
                                                           << 3U) 
                                                          | ((4U 
                                                              & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                                 >> 3U)) 
                                                             | ((2U 
                                                                 & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                                    >> 2U)) 
                                                                | (1U 
                                                                   & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                                      >> 1U))))))] 
                                                      >> 1U))))) 
                                         & (IData)(vlSelfRef.L1DCache__DOT__way1_valid_sel));
    vlSelfRef.L1DCache__DOT__hit = ((IData)(vlSelfRef.L1DCache__DOT__way1_hit) 
                                    | ((~ ((VL1DCache__ConstPool__TABLE_h8d06dde6_0
                                            [(((((4U 
                                                  & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                     >> 8U)) 
                                                 | ((2U 
                                                     & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                        >> 7U)) 
                                                    | (1U 
                                                       & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                          >> 6U)))) 
                                                << 3U) 
                                               | ((4U 
                                                   & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                      >> 2U)) 
                                                  | ((2U 
                                                      & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                         >> 1U)) 
                                                     | (1U 
                                                        & (IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0))))) 
                                              | ((((4U 
                                                    & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                       >> 9U)) 
                                                   | ((2U 
                                                       & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                          >> 8U)) 
                                                      | (1U 
                                                         & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                            >> 7U)))) 
                                                  << 3U) 
                                                 | ((4U 
                                                     & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                        >> 3U)) 
                                                    | ((2U 
                                                        & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                           >> 2U)) 
                                                       | (1U 
                                                          & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                             >> 1U))))))] 
                                            >> 2U) 
                                           | (VL1DCache__ConstPool__TABLE_h8d06dde6_0
                                              [((((
                                                   (4U 
                                                    & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                       >> 8U)) 
                                                   | ((2U 
                                                       & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                          >> 7U)) 
                                                      | (1U 
                                                         & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                            >> 6U)))) 
                                                  << 3U) 
                                                 | ((4U 
                                                     & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                        >> 2U)) 
                                                    | ((2U 
                                                        & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                           >> 1U)) 
                                                       | (1U 
                                                          & (IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0))))) 
                                                | ((((4U 
                                                      & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                         >> 9U)) 
                                                     | ((2U 
                                                         & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                            >> 8U)) 
                                                        | (1U 
                                                           & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                              >> 7U)))) 
                                                    << 3U) 
                                                   | ((4U 
                                                       & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                          >> 3U)) 
                                                      | ((2U 
                                                          & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                             >> 2U)) 
                                                         | (1U 
                                                            & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                               >> 1U))))))] 
                                              | ((L1DCache__DOT__u_tag_cmp_w0__DOT__diff 
                                                  >> 0x00000018U) 
                                                 | (VL1DCache__ConstPool__TABLE_h8d06dde6_0
                                                    [
                                                    (((((4U 
                                                         & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                            >> 8U)) 
                                                        | ((2U 
                                                            & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                               >> 7U)) 
                                                           | (1U 
                                                              & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                                 >> 6U)))) 
                                                       << 3U) 
                                                      | ((4U 
                                                          & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                             >> 2U)) 
                                                         | ((2U 
                                                             & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                                >> 1U)) 
                                                            | (1U 
                                                               & (IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0))))) 
                                                     | ((((4U 
                                                           & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                              >> 9U)) 
                                                          | ((2U 
                                                              & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                                 >> 8U)) 
                                                             | (1U 
                                                                & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                                   >> 7U)))) 
                                                         << 3U) 
                                                        | ((4U 
                                                            & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                               >> 3U)) 
                                                           | ((2U 
                                                               & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                                  >> 2U)) 
                                                              | (1U 
                                                                 & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                                    >> 1U))))))] 
                                                    >> 1U))))) 
                                       & (IData)(vlSelfRef.L1DCache__DOT__way0_valid_sel)));
}

extern const VlUnpacked<CData/*3:0*/, 256> VL1DCache__ConstPool__TABLE_h9783ab34_0;

void VL1DCache___024root___ico_comb__TOP__5(VL1DCache___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VL1DCache___024root___ico_comb__TOP__5\n"); );
    VL1DCache__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Locals
    CData/*3:0*/ L1DCache__DOT__be;
    L1DCache__DOT__be = 0;
    // Body
    L1DCache__DOT__be = (0x0000000fU & ((((((IData)(vlSelfRef.L1DCache__DOT__be2_h) 
                                            | ((3U 
                                                == 
                                                (3U 
                                                 & vlSelfRef.req_addr)) 
                                               & (3U 
                                                  == 
                                                  (3U 
                                                   & (~ (IData)(vlSelfRef.req_size)))))) 
                                           << 3U) | 
                                          (((IData)(vlSelfRef.L1DCache__DOT__be2_h) 
                                            | (IData)(
                                                      ((2U 
                                                        == 
                                                        (3U 
                                                         & vlSelfRef.req_addr)) 
                                                       & (3U 
                                                          == 
                                                          (3U 
                                                           & (~ (IData)(vlSelfRef.req_size))))))) 
                                           << 2U)) 
                                         | ((((IData)(vlSelfRef.L1DCache__DOT__be0_h) 
                                              | ((~ (IData)(vlSelfRef.req_size)) 
                                                 & (vlSelfRef.req_addr 
                                                    & (IData)(vlSelfRef.__VdfgRegularize_h6e95ff9d_0_1)))) 
                                             << 1U) 
                                            | ((IData)(vlSelfRef.L1DCache__DOT__be0_h) 
                                               | ((3U 
                                                   == 
                                                   (3U 
                                                    & (~ vlSelfRef.req_addr))) 
                                                  & (3U 
                                                     == 
                                                     (3U 
                                                      & (~ (IData)(vlSelfRef.req_size)))))))) 
                                        | (- (IData)((IData)(vlSelfRef.L1DCache__DOT__is_word)))));
    if ((3U == (IData)(vlSelfRef.req_size))) {
        vlSelfRef.L1DCache__DOT__ram_be_w0[0U] = (IData)(
                                                         (- (QData)((IData)(
                                                                            (1U 
                                                                             & VL1DCache__ConstPool__TABLE_h9783ab34_0
                                                                             [vlSelfRef.L1DCache__DOT__wdc])))));
        vlSelfRef.L1DCache__DOT__ram_be_w0[1U] = (IData)(
                                                         ((- (QData)((IData)(
                                                                             (1U 
                                                                              & VL1DCache__ConstPool__TABLE_h9783ab34_0
                                                                              [vlSelfRef.L1DCache__DOT__wdc])))) 
                                                          >> 0x00000020U));
        vlSelfRef.L1DCache__DOT__ram_be_w0[2U] = (IData)(
                                                         (- (QData)((IData)(
                                                                            (1U 
                                                                             & (VL1DCache__ConstPool__TABLE_h9783ab34_0
                                                                                [vlSelfRef.L1DCache__DOT__wdc] 
                                                                                >> 1U))))));
        vlSelfRef.L1DCache__DOT__ram_be_w0[3U] = (IData)(
                                                         ((- (QData)((IData)(
                                                                             (1U 
                                                                              & (VL1DCache__ConstPool__TABLE_h9783ab34_0
                                                                                [vlSelfRef.L1DCache__DOT__wdc] 
                                                                                >> 1U))))) 
                                                          >> 0x00000020U));
        vlSelfRef.L1DCache__DOT__ram_be_w0[4U] = (IData)(
                                                         (- (QData)((IData)(
                                                                            (1U 
                                                                             & (VL1DCache__ConstPool__TABLE_h9783ab34_0
                                                                                [vlSelfRef.L1DCache__DOT__wdc] 
                                                                                >> 2U))))));
        vlSelfRef.L1DCache__DOT__ram_be_w0[5U] = (IData)(
                                                         ((- (QData)((IData)(
                                                                             (1U 
                                                                              & (VL1DCache__ConstPool__TABLE_h9783ab34_0
                                                                                [vlSelfRef.L1DCache__DOT__wdc] 
                                                                                >> 2U))))) 
                                                          >> 0x00000020U));
        vlSelfRef.L1DCache__DOT__ram_be_w0[6U] = (IData)(
                                                         (- (QData)((IData)(
                                                                            (1U 
                                                                             & (VL1DCache__ConstPool__TABLE_h9783ab34_0
                                                                                [vlSelfRef.L1DCache__DOT__wdc] 
                                                                                >> 3U))))));
        vlSelfRef.L1DCache__DOT__ram_be_w0[7U] = (IData)(
                                                         ((- (QData)((IData)(
                                                                             (1U 
                                                                              & (VL1DCache__ConstPool__TABLE_h9783ab34_0
                                                                                [vlSelfRef.L1DCache__DOT__wdc] 
                                                                                >> 3U))))) 
                                                          >> 0x00000020U));
    } else {
        vlSelfRef.L1DCache__DOT__ram_be_w0[0U] = ((
                                                   (((0x0000ff00U 
                                                      & ((- (IData)(
                                                                    (1U 
                                                                     & ((IData)(L1DCache__DOT__be) 
                                                                        >> 3U)))) 
                                                         << 8U)) 
                                                     | (0x000000ffU 
                                                        & (- (IData)(
                                                                     (1U 
                                                                      & ((IData)(L1DCache__DOT__be) 
                                                                         >> 2U)))))) 
                                                    << 0x00000010U) 
                                                   | ((0x0000ff00U 
                                                       & ((- (IData)(
                                                                     (1U 
                                                                      & ((IData)(L1DCache__DOT__be) 
                                                                         >> 1U)))) 
                                                          << 8U)) 
                                                      | (0x000000ffU 
                                                         & (- (IData)(
                                                                      (1U 
                                                                       & (IData)(L1DCache__DOT__be))))))) 
                                                  & (- (IData)(
                                                               (1U 
                                                                & (IData)(vlSelfRef.L1DCache__DOT__wdc)))));
        vlSelfRef.L1DCache__DOT__ram_be_w0[1U] = ((
                                                   (((0x0000ff00U 
                                                      & ((- (IData)(
                                                                    (1U 
                                                                     & ((IData)(L1DCache__DOT__be) 
                                                                        >> 3U)))) 
                                                         << 8U)) 
                                                     | (0x000000ffU 
                                                        & (- (IData)(
                                                                     (1U 
                                                                      & ((IData)(L1DCache__DOT__be) 
                                                                         >> 2U)))))) 
                                                    << 0x00000010U) 
                                                   | ((0x0000ff00U 
                                                       & ((- (IData)(
                                                                     (1U 
                                                                      & ((IData)(L1DCache__DOT__be) 
                                                                         >> 1U)))) 
                                                          << 8U)) 
                                                      | (0x000000ffU 
                                                         & (- (IData)(
                                                                      (1U 
                                                                       & (IData)(L1DCache__DOT__be))))))) 
                                                  & (- (IData)(
                                                               (1U 
                                                                & ((IData)(vlSelfRef.L1DCache__DOT__wdc) 
                                                                   >> 1U)))));
        vlSelfRef.L1DCache__DOT__ram_be_w0[2U] = ((
                                                   (((0x0000ff00U 
                                                      & ((- (IData)(
                                                                    (1U 
                                                                     & ((IData)(L1DCache__DOT__be) 
                                                                        >> 3U)))) 
                                                         << 8U)) 
                                                     | (0x000000ffU 
                                                        & (- (IData)(
                                                                     (1U 
                                                                      & ((IData)(L1DCache__DOT__be) 
                                                                         >> 2U)))))) 
                                                    << 0x00000010U) 
                                                   | ((0x0000ff00U 
                                                       & ((- (IData)(
                                                                     (1U 
                                                                      & ((IData)(L1DCache__DOT__be) 
                                                                         >> 1U)))) 
                                                          << 8U)) 
                                                      | (0x000000ffU 
                                                         & (- (IData)(
                                                                      (1U 
                                                                       & (IData)(L1DCache__DOT__be))))))) 
                                                  & (- (IData)(
                                                               (1U 
                                                                & ((IData)(vlSelfRef.L1DCache__DOT__wdc) 
                                                                   >> 2U)))));
        vlSelfRef.L1DCache__DOT__ram_be_w0[3U] = ((
                                                   (((0x0000ff00U 
                                                      & ((- (IData)(
                                                                    (1U 
                                                                     & ((IData)(L1DCache__DOT__be) 
                                                                        >> 3U)))) 
                                                         << 8U)) 
                                                     | (0x000000ffU 
                                                        & (- (IData)(
                                                                     (1U 
                                                                      & ((IData)(L1DCache__DOT__be) 
                                                                         >> 2U)))))) 
                                                    << 0x00000010U) 
                                                   | ((0x0000ff00U 
                                                       & ((- (IData)(
                                                                     (1U 
                                                                      & ((IData)(L1DCache__DOT__be) 
                                                                         >> 1U)))) 
                                                          << 8U)) 
                                                      | (0x000000ffU 
                                                         & (- (IData)(
                                                                      (1U 
                                                                       & (IData)(L1DCache__DOT__be))))))) 
                                                  & (- (IData)(
                                                               (1U 
                                                                & ((IData)(vlSelfRef.L1DCache__DOT__wdc) 
                                                                   >> 3U)))));
        vlSelfRef.L1DCache__DOT__ram_be_w0[4U] = ((
                                                   (((0x0000ff00U 
                                                      & ((- (IData)(
                                                                    (1U 
                                                                     & ((IData)(L1DCache__DOT__be) 
                                                                        >> 3U)))) 
                                                         << 8U)) 
                                                     | (0x000000ffU 
                                                        & (- (IData)(
                                                                     (1U 
                                                                      & ((IData)(L1DCache__DOT__be) 
                                                                         >> 2U)))))) 
                                                    << 0x00000010U) 
                                                   | ((0x0000ff00U 
                                                       & ((- (IData)(
                                                                     (1U 
                                                                      & ((IData)(L1DCache__DOT__be) 
                                                                         >> 1U)))) 
                                                          << 8U)) 
                                                      | (0x000000ffU 
                                                         & (- (IData)(
                                                                      (1U 
                                                                       & (IData)(L1DCache__DOT__be))))))) 
                                                  & (- (IData)(
                                                               (1U 
                                                                & ((IData)(vlSelfRef.L1DCache__DOT__wdc) 
                                                                   >> 4U)))));
        vlSelfRef.L1DCache__DOT__ram_be_w0[5U] = ((
                                                   (((0x0000ff00U 
                                                      & ((- (IData)(
                                                                    (1U 
                                                                     & ((IData)(L1DCache__DOT__be) 
                                                                        >> 3U)))) 
                                                         << 8U)) 
                                                     | (0x000000ffU 
                                                        & (- (IData)(
                                                                     (1U 
                                                                      & ((IData)(L1DCache__DOT__be) 
                                                                         >> 2U)))))) 
                                                    << 0x00000010U) 
                                                   | ((0x0000ff00U 
                                                       & ((- (IData)(
                                                                     (1U 
                                                                      & ((IData)(L1DCache__DOT__be) 
                                                                         >> 1U)))) 
                                                          << 8U)) 
                                                      | (0x000000ffU 
                                                         & (- (IData)(
                                                                      (1U 
                                                                       & (IData)(L1DCache__DOT__be))))))) 
                                                  & (- (IData)(
                                                               (1U 
                                                                & ((IData)(vlSelfRef.L1DCache__DOT__wdc) 
                                                                   >> 5U)))));
        vlSelfRef.L1DCache__DOT__ram_be_w0[6U] = ((
                                                   (((0x0000ff00U 
                                                      & ((- (IData)(
                                                                    (1U 
                                                                     & ((IData)(L1DCache__DOT__be) 
                                                                        >> 3U)))) 
                                                         << 8U)) 
                                                     | (0x000000ffU 
                                                        & (- (IData)(
                                                                     (1U 
                                                                      & ((IData)(L1DCache__DOT__be) 
                                                                         >> 2U)))))) 
                                                    << 0x00000010U) 
                                                   | ((0x0000ff00U 
                                                       & ((- (IData)(
                                                                     (1U 
                                                                      & ((IData)(L1DCache__DOT__be) 
                                                                         >> 1U)))) 
                                                          << 8U)) 
                                                      | (0x000000ffU 
                                                         & (- (IData)(
                                                                      (1U 
                                                                       & (IData)(L1DCache__DOT__be))))))) 
                                                  & (IData)(
                                                            (((QData)((IData)(
                                                                              (- (IData)(
                                                                                (1U 
                                                                                & ((IData)(vlSelfRef.L1DCache__DOT__wdc) 
                                                                                >> 7U)))))) 
                                                              << 0x00000020U) 
                                                             | (QData)((IData)(
                                                                               (- (IData)(
                                                                                (1U 
                                                                                & ((IData)(vlSelfRef.L1DCache__DOT__wdc) 
                                                                                >> 6U)))))))));
        vlSelfRef.L1DCache__DOT__ram_be_w0[7U] = ((
                                                   (((0x0000ff00U 
                                                      & ((- (IData)(
                                                                    (1U 
                                                                     & ((IData)(L1DCache__DOT__be) 
                                                                        >> 3U)))) 
                                                         << 8U)) 
                                                     | (0x000000ffU 
                                                        & (- (IData)(
                                                                     (1U 
                                                                      & ((IData)(L1DCache__DOT__be) 
                                                                         >> 2U)))))) 
                                                    << 0x00000010U) 
                                                   | ((0x0000ff00U 
                                                       & ((- (IData)(
                                                                     (1U 
                                                                      & ((IData)(L1DCache__DOT__be) 
                                                                         >> 1U)))) 
                                                          << 8U)) 
                                                      | (0x000000ffU 
                                                         & (- (IData)(
                                                                      (1U 
                                                                       & (IData)(L1DCache__DOT__be))))))) 
                                                  & (IData)(
                                                            ((((QData)((IData)(
                                                                               (- (IData)(
                                                                                (1U 
                                                                                & ((IData)(vlSelfRef.L1DCache__DOT__wdc) 
                                                                                >> 7U)))))) 
                                                               << 0x00000020U) 
                                                              | (QData)((IData)(
                                                                                (- (IData)(
                                                                                (1U 
                                                                                & ((IData)(vlSelfRef.L1DCache__DOT__wdc) 
                                                                                >> 6U))))))) 
                                                             >> 0x00000020U)));
    }
}

void VL1DCache___024root___eval_body__ico(VL1DCache___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VL1DCache___024root___eval_body__ico\n"); );
    VL1DCache__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    if ((4ULL & vlSelfRef.__VicoTriggered[0U])) {
        VL1DCache___024root___ico_sequent__TOP__0(vlSelf);
    }
    if ((0x0000000000000018ULL & vlSelfRef.__VicoTriggered[0U])) {
        {
            // Inlined CFunc: _ico_comb__TOP__0
            vlSelfRef.__VdfgRegularize_h6e95ff9d_0_0 
                = ((0x0000ff00U & (((3U == (3U & (~ (IData)(vlSelfRef.req_size))))
                                     ? (IData)(vlSelfRef.req_wdata)
                                     : (IData)((vlSelfRef.req_wdata 
                                                >> 8U))) 
                                   << 8U)) | (0x000000ffU 
                                              & (IData)(vlSelfRef.req_wdata)));
        }
    }
    if ((0x0000000000000014ULL & vlSelfRef.__VicoTriggered[0U])) {
        {
            // Inlined CFunc: _ico_comb__TOP__1
            vlSelfRef.L1DCache__DOT__be2_h = ((vlSelfRef.req_addr 
                                               >> 1U) 
                                              & (1U 
                                                 == (IData)(vlSelfRef.req_size)));
            vlSelfRef.__VdfgRegularize_h6e95ff9d_0_1 
                = (1U & ((~ (vlSelfRef.req_addr >> 1U)) 
                         & (~ ((IData)(vlSelfRef.req_size) 
                               >> 1U))));
            vlSelfRef.L1DCache__DOT__be0_h = ((IData)(vlSelfRef.req_size) 
                                              & (IData)(vlSelfRef.__VdfgRegularize_h6e95ff9d_0_1));
        }
    }
    if ((0x0000000000000010ULL & vlSelfRef.__VicoTriggered[0U])) {
        {
            // Inlined CFunc: _ico_sequent__TOP__1
            vlSelfRef.L1DCache__DOT__is_word = (IData)(
                                                       (2U 
                                                        == (IData)(vlSelfRef.req_size)));
        }
    }
    if ((0x0000000000000020ULL & vlSelfRef.__VicoTriggered[0U])) {
        {
            // Inlined CFunc: _ico_sequent__TOP__2
            vlSelfRef.L1DCache__DOT__refill_done = 
                ((IData)(vlSelfRef.refill_valid) & (IData)(vlSelfRef.L1DCache__DOT__is_refill_wait));
            vlSelfRef.L1DCache__DOT__rfs_0 = ((- (IData)((IData)(vlSelfRef.L1DCache__DOT__refill_done))) 
                                              & (((0x0000000cU 
                                                   & ((- (IData)(
                                                                 (1U 
                                                                  & (vlSelfRef.L1DCache__DOT__pend_q_reg 
                                                                     >> 6U)))) 
                                                      << 2U)) 
                                                  | (3U 
                                                     & (- (IData)(
                                                                  (1U 
                                                                   & (~ 
                                                                      (vlSelfRef.L1DCache__DOT__pend_q_reg 
                                                                       >> 6U))))))) 
                                                 & ((((2U 
                                                       & (vlSelfRef.L1DCache__DOT__pend_q_reg 
                                                          >> 4U)) 
                                                      | (1U 
                                                         & (~ 
                                                            (vlSelfRef.L1DCache__DOT__pend_q_reg 
                                                             >> 5U)))) 
                                                     << 2U) 
                                                    | ((2U 
                                                        & (vlSelfRef.L1DCache__DOT__pend_q_reg 
                                                           >> 4U)) 
                                                       | (1U 
                                                          & (~ 
                                                             (vlSelfRef.L1DCache__DOT__pend_q_reg 
                                                              >> 5U)))))));
            vlSelfRef.L1DCache__DOT__rfe_0 = ((- (IData)(
                                                         (1U 
                                                          & (~ (IData)(vlSelfRef.L1DCache__DOT__pend_victim_q_reg))))) 
                                              & (IData)(vlSelfRef.L1DCache__DOT__rfs_0));
            vlSelfRef.L1DCache__DOT__rfe_1 = ((- (IData)((IData)(vlSelfRef.L1DCache__DOT__pend_victim_q_reg))) 
                                              & (IData)(vlSelfRef.L1DCache__DOT__rfs_0));
        }
    }
    if ((7ULL & vlSelfRef.__VicoTriggered[0U])) {
        {
            // Inlined CFunc: _ico_comb__TOP__2
            vlSelfRef.L1DCache__DOT__write_hit = ((7U 
                                                   == 
                                                   (7U 
                                                    & (~ (IData)(vlSelfRef.L1DCache__DOT__fsm_q_reg)))) 
                                                  & ((IData)(vlSelfRef.L1DCache__DOT__hit) 
                                                     & ((IData)(vlSelfRef.req_valid) 
                                                        & (IData)(vlSelfRef.req_we))));
            vlSelfRef.L1DCache__DOT__whs_0 = ((- (IData)((IData)(vlSelfRef.L1DCache__DOT__write_hit))) 
                                              & (IData)(vlSelfRef.L1DCache__DOT__valid_dec_w0));
        }
    }
    if ((5ULL & vlSelfRef.__VicoTriggered[0U])) {
        {
            // Inlined CFunc: _ico_comb__TOP__3
            vlSelfRef.L1DCache__DOT__miss_detect = 
                ((IData)(vlSelfRef.req_valid) & ((~ (IData)(vlSelfRef.L1DCache__DOT__hit)) 
                                                 & (7U 
                                                    == 
                                                    (7U 
                                                     & (~ (IData)(vlSelfRef.L1DCache__DOT__fsm_q_reg))))));
            vlSelfRef.stall = (1U & ((~ (7U == (7U 
                                                & (~ (IData)(vlSelfRef.L1DCache__DOT__fsm_q_reg))))) 
                                     | (IData)(vlSelfRef.L1DCache__DOT__miss_detect)));
            vlSelfRef.L1DCache__DOT__miss_detect_clean 
                = ((~ (IData)(vlSelfRef.L1DCache__DOT__victim_needs_wb)) 
                   & (IData)(vlSelfRef.L1DCache__DOT__miss_detect));
            vlSelfRef.miss_valid = ((IData)(vlSelfRef.L1DCache__DOT__is_refill_wait) 
                                    | (IData)(vlSelfRef.L1DCache__DOT__miss_detect_clean));
        }
    }
    if ((0x0000000000000018ULL & vlSelfRef.__VicoTriggered[0U])) {
        {
            // Inlined CFunc: _ico_comb__TOP__4
            if ((3U == (IData)(vlSelfRef.req_size))) {
                vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                    = (IData)(vlSelfRef.req_wdata);
                vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                    = (IData)((vlSelfRef.req_wdata 
                               >> 0x00000020U));
                vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                    = (IData)(vlSelfRef.req_wdata);
                vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                    = (IData)((vlSelfRef.req_wdata 
                               >> 0x00000020U));
                vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                    = (IData)(vlSelfRef.req_wdata);
                vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                    = (IData)((vlSelfRef.req_wdata 
                               >> 0x00000020U));
                vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                    = (IData)(vlSelfRef.req_wdata);
                vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                    = (IData)((vlSelfRef.req_wdata 
                               >> 0x00000020U));
            } else {
                vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                    = ((((IData)(vlSelfRef.L1DCache__DOT__is_word)
                          ? (IData)((vlSelfRef.req_wdata 
                                     >> 0x00000010U))
                          : (IData)(vlSelfRef.__VdfgRegularize_h6e95ff9d_0_0)) 
                        << 0x00000010U) | (IData)(vlSelfRef.__VdfgRegularize_h6e95ff9d_0_0));
                vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                    = ((((IData)(vlSelfRef.L1DCache__DOT__is_word)
                          ? (IData)((vlSelfRef.req_wdata 
                                     >> 0x00000010U))
                          : (IData)(vlSelfRef.__VdfgRegularize_h6e95ff9d_0_0)) 
                        << 0x00000010U) | (IData)(vlSelfRef.__VdfgRegularize_h6e95ff9d_0_0));
                vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                    = ((((IData)(vlSelfRef.L1DCache__DOT__is_word)
                          ? (IData)((vlSelfRef.req_wdata 
                                     >> 0x00000010U))
                          : (IData)(vlSelfRef.__VdfgRegularize_h6e95ff9d_0_0)) 
                        << 0x00000010U) | (IData)(vlSelfRef.__VdfgRegularize_h6e95ff9d_0_0));
                vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                    = ((((IData)(vlSelfRef.L1DCache__DOT__is_word)
                          ? (IData)((vlSelfRef.req_wdata 
                                     >> 0x00000010U))
                          : (IData)(vlSelfRef.__VdfgRegularize_h6e95ff9d_0_0)) 
                        << 0x00000010U) | (IData)(vlSelfRef.__VdfgRegularize_h6e95ff9d_0_0));
                vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                    = ((((IData)(vlSelfRef.L1DCache__DOT__is_word)
                          ? (IData)((vlSelfRef.req_wdata 
                                     >> 0x00000010U))
                          : (IData)(vlSelfRef.__VdfgRegularize_h6e95ff9d_0_0)) 
                        << 0x00000010U) | (IData)(vlSelfRef.__VdfgRegularize_h6e95ff9d_0_0));
                vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                    = ((((IData)(vlSelfRef.L1DCache__DOT__is_word)
                          ? (IData)((vlSelfRef.req_wdata 
                                     >> 0x00000010U))
                          : (IData)(vlSelfRef.__VdfgRegularize_h6e95ff9d_0_0)) 
                        << 0x00000010U) | (IData)(vlSelfRef.__VdfgRegularize_h6e95ff9d_0_0));
                vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                    = ((((IData)(vlSelfRef.L1DCache__DOT__is_word)
                          ? (IData)((vlSelfRef.req_wdata 
                                     >> 0x00000010U))
                          : (IData)(vlSelfRef.__VdfgRegularize_h6e95ff9d_0_0)) 
                        << 0x00000010U) | (IData)(vlSelfRef.__VdfgRegularize_h6e95ff9d_0_0));
                vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                    = ((((IData)(vlSelfRef.L1DCache__DOT__is_word)
                          ? (IData)((vlSelfRef.req_wdata 
                                     >> 0x00000010U))
                          : (IData)(vlSelfRef.__VdfgRegularize_h6e95ff9d_0_0)) 
                        << 0x00000010U) | (IData)(vlSelfRef.__VdfgRegularize_h6e95ff9d_0_0));
            }
        }
    }
    if ((0x0000000000000014ULL & vlSelfRef.__VicoTriggered[0U])) {
        VL1DCache___024root___ico_comb__TOP__5(vlSelf);
    }
    if ((0x0000000000000024ULL & vlSelfRef.__VicoTriggered[0U])) {
        {
            // Inlined CFunc: _ico_comb__TOP__6
            if (vlSelfRef.L1DCache__DOT__refill_done) {
                vlSelfRef.L1DCache__DOT__data_wr_addr_w0 
                    = (3U & (vlSelfRef.L1DCache__DOT__pend_q_reg 
                             >> 5U));
                vlSelfRef.L1DCache__DOT__lru_nv = (0x0000000fU 
                                                   & (- (IData)(
                                                                (1U 
                                                                 & (~ (IData)(vlSelfRef.L1DCache__DOT__pend_victim_q_reg))))));
            } else {
                vlSelfRef.L1DCache__DOT__data_wr_addr_w0 
                    = (3U & (vlSelfRef.req_addr >> 5U));
                vlSelfRef.L1DCache__DOT__lru_nv = (0x0000000fU 
                                                   & (- (IData)(
                                                                (1U 
                                                                 & (~ (IData)(vlSelfRef.L1DCache__DOT__way1_hit))))));
            }
        }
    }
    if ((0x0000000000000027ULL & vlSelfRef.__VicoTriggered[0U])) {
        {
            // Inlined CFunc: _ico_comb__TOP__7
            vlSelfRef.L1DCache__DOT__lru_en = ((IData)(vlSelfRef.L1DCache__DOT__rfs_0) 
                                               | (IData)(vlSelfRef.L1DCache__DOT__whs_0));
        }
    }
}

bool VL1DCache___024root___trigger_anySet__act(const VlUnpacked<QData/*63:0*/, 1> &in) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VL1DCache___024root___trigger_anySet__act\n"); );
    // Locals
    IData/*31:0*/ n;
    // Body
    n = 0U;
    do {
        if (in[n]) {
            return (1U);
        }
        n = ((IData)(1U) + n);
    } while ((1U > n));
    return (0U);
}

void VL1DCache___024root___nba_sequent__TOP__0(VL1DCache___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VL1DCache___024root___nba_sequent__TOP__0\n"); );
    VL1DCache__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Locals
    IData/*31:0*/ __Vdly__L1DCache__DOT__pend_q_reg;
    __Vdly__L1DCache__DOT__pend_q_reg = 0;
    // Body
    vlSelfRef.__Vdly__L1DCache__DOT__pend_victim_q_reg 
        = vlSelfRef.L1DCache__DOT__pend_victim_q_reg;
    __Vdly__L1DCache__DOT__pend_q_reg = vlSelfRef.L1DCache__DOT__pend_q_reg;
    vlSelfRef.__Vdly__L1DCache__DOT__pend_victim_q_reg 
        = ((1U & (~ (IData)(vlSelfRef.reset))) && ((IData)(vlSelfRef.L1DCache__DOT__miss_detect)
                                                    ? (IData)(vlSelfRef.L1DCache__DOT__victim_lru)
                                                    : (IData)(vlSelfRef.L1DCache__DOT__pend_victim_q_reg)));
    vlSelfRef.resp_valid = ((1U & (~ (IData)(vlSelfRef.reset))) 
                            && ((IData)(vlSelfRef.L1DCache__DOT__refill_done) 
                                | ((7U == (7U & (~ (IData)(vlSelfRef.L1DCache__DOT__fsm_q_reg)))) 
                                   & ((IData)(vlSelfRef.req_valid) 
                                      & ((~ (IData)(vlSelfRef.req_we)) 
                                         & (IData)(vlSelfRef.L1DCache__DOT__hit))))));
    if (vlSelfRef.reset) {
        vlSelfRef.L1DCache__DOT__lru_q_reg = 0U;
        vlSelfRef.L1DCache__DOT__dirty_q_reg = 0U;
        vlSelfRef.L1DCache__DOT__valid_q_reg = 0U;
        vlSelfRef.L1DCache__DOT__tag_q_w0_s3 = 0U;
        vlSelfRef.L1DCache__DOT__tag_q_w0_s2 = 0U;
        vlSelfRef.L1DCache__DOT__tag_q_w0_s1 = 0U;
        vlSelfRef.L1DCache__DOT__tag_q_w0_s0 = 0U;
        vlSelfRef.L1DCache__DOT__tag_q_w1_s3 = 0U;
        vlSelfRef.L1DCache__DOT__tag_q_w1_s2 = 0U;
        vlSelfRef.L1DCache__DOT__tag_q_w1_s1 = 0U;
        vlSelfRef.L1DCache__DOT__tag_q_w1_s0 = 0U;
        __Vdly__L1DCache__DOT__pend_q_reg = 0U;
        vlSelfRef.resp_data = 0ULL;
        vlSelfRef.L1DCache__DOT__fsm_q_reg = 0U;
    } else {
        vlSelfRef.L1DCache__DOT__lru_q_reg = ((((2U 
                                                 & (((8U 
                                                      & (IData)(vlSelfRef.L1DCache__DOT__lru_en))
                                                      ? 
                                                     ((IData)(vlSelfRef.L1DCache__DOT__lru_nv) 
                                                      >> 3U)
                                                      : 
                                                     ((IData)(vlSelfRef.L1DCache__DOT__lru_q_reg) 
                                                      >> 3U)) 
                                                    << 1U)) 
                                                | (1U 
                                                   & ((4U 
                                                       & (IData)(vlSelfRef.L1DCache__DOT__lru_en))
                                                       ? 
                                                      ((IData)(vlSelfRef.L1DCache__DOT__lru_nv) 
                                                       >> 2U)
                                                       : 
                                                      ((IData)(vlSelfRef.L1DCache__DOT__lru_q_reg) 
                                                       >> 2U)))) 
                                               << 2U) 
                                              | ((2U 
                                                  & (((2U 
                                                       & (IData)(vlSelfRef.L1DCache__DOT__lru_en))
                                                       ? 
                                                      ((IData)(vlSelfRef.L1DCache__DOT__lru_nv) 
                                                       >> 1U)
                                                       : 
                                                      ((IData)(vlSelfRef.L1DCache__DOT__lru_q_reg) 
                                                       >> 1U)) 
                                                     << 1U)) 
                                                 | (1U 
                                                    & ((1U 
                                                        & (IData)(vlSelfRef.L1DCache__DOT__lru_en))
                                                        ? (IData)(vlSelfRef.L1DCache__DOT__lru_nv)
                                                        : (IData)(vlSelfRef.L1DCache__DOT__lru_q_reg)))));
        vlSelfRef.L1DCache__DOT__dirty_q_reg = (((0x000000f0U 
                                                  & (((~ (IData)(vlSelfRef.L1DCache__DOT__rfe_1)) 
                                                      << 4U) 
                                                     & (IData)(vlSelfRef.L1DCache__DOT__dirty_q_reg))) 
                                                 | (0x0000000fU 
                                                    & ((~ (IData)(vlSelfRef.L1DCache__DOT__rfe_0)) 
                                                       & (IData)(vlSelfRef.L1DCache__DOT__dirty_q_reg)))) 
                                                | ((((- (IData)((IData)(vlSelfRef.L1DCache__DOT__way1_hit))) 
                                                     & (IData)(vlSelfRef.L1DCache__DOT__whs_0)) 
                                                    << 4U) 
                                                   | ((- (IData)(
                                                                 (1U 
                                                                  & (~ (IData)(vlSelfRef.L1DCache__DOT__way1_hit))))) 
                                                      & (IData)(vlSelfRef.L1DCache__DOT__whs_0))));
        vlSelfRef.L1DCache__DOT__valid_q_reg = ((IData)(vlSelfRef.L1DCache__DOT__valid_q_reg) 
                                                | (((IData)(vlSelfRef.L1DCache__DOT__rfe_1) 
                                                    << 4U) 
                                                   | (IData)(vlSelfRef.L1DCache__DOT__rfe_0)));
        vlSelfRef.L1DCache__DOT__tag_q_w0_s3 = (0x01ffffffU 
                                                & ((8U 
                                                    & (IData)(vlSelfRef.L1DCache__DOT__rfe_0))
                                                    ? 
                                                   (vlSelfRef.L1DCache__DOT__pend_q_reg 
                                                    >> 7U)
                                                    : vlSelfRef.L1DCache__DOT__tag_q_w0_s3));
        vlSelfRef.L1DCache__DOT__tag_q_w0_s2 = (0x01ffffffU 
                                                & ((4U 
                                                    & (IData)(vlSelfRef.L1DCache__DOT__rfe_0))
                                                    ? 
                                                   (vlSelfRef.L1DCache__DOT__pend_q_reg 
                                                    >> 7U)
                                                    : vlSelfRef.L1DCache__DOT__tag_q_w0_s2));
        vlSelfRef.L1DCache__DOT__tag_q_w0_s1 = (0x01ffffffU 
                                                & ((2U 
                                                    & (IData)(vlSelfRef.L1DCache__DOT__rfe_0))
                                                    ? 
                                                   (vlSelfRef.L1DCache__DOT__pend_q_reg 
                                                    >> 7U)
                                                    : vlSelfRef.L1DCache__DOT__tag_q_w0_s1));
        vlSelfRef.L1DCache__DOT__tag_q_w0_s0 = (0x01ffffffU 
                                                & ((1U 
                                                    & (IData)(vlSelfRef.L1DCache__DOT__rfe_0))
                                                    ? 
                                                   (vlSelfRef.L1DCache__DOT__pend_q_reg 
                                                    >> 7U)
                                                    : vlSelfRef.L1DCache__DOT__tag_q_w0_s0));
        vlSelfRef.L1DCache__DOT__tag_q_w1_s3 = (0x01ffffffU 
                                                & ((8U 
                                                    & (IData)(vlSelfRef.L1DCache__DOT__rfe_1))
                                                    ? 
                                                   (vlSelfRef.L1DCache__DOT__pend_q_reg 
                                                    >> 7U)
                                                    : vlSelfRef.L1DCache__DOT__tag_q_w1_s3));
        vlSelfRef.L1DCache__DOT__tag_q_w1_s2 = (0x01ffffffU 
                                                & ((4U 
                                                    & (IData)(vlSelfRef.L1DCache__DOT__rfe_1))
                                                    ? 
                                                   (vlSelfRef.L1DCache__DOT__pend_q_reg 
                                                    >> 7U)
                                                    : vlSelfRef.L1DCache__DOT__tag_q_w1_s2));
        vlSelfRef.L1DCache__DOT__tag_q_w1_s1 = (0x01ffffffU 
                                                & ((2U 
                                                    & (IData)(vlSelfRef.L1DCache__DOT__rfe_1))
                                                    ? 
                                                   (vlSelfRef.L1DCache__DOT__pend_q_reg 
                                                    >> 7U)
                                                    : vlSelfRef.L1DCache__DOT__tag_q_w1_s1));
        vlSelfRef.L1DCache__DOT__tag_q_w1_s0 = (0x01ffffffU 
                                                & ((1U 
                                                    & (IData)(vlSelfRef.L1DCache__DOT__rfe_1))
                                                    ? 
                                                   (vlSelfRef.L1DCache__DOT__pend_q_reg 
                                                    >> 7U)
                                                    : vlSelfRef.L1DCache__DOT__tag_q_w1_s0));
        __Vdly__L1DCache__DOT__pend_q_reg = ((IData)(vlSelfRef.L1DCache__DOT__miss_detect)
                                              ? vlSelfRef.req_addr
                                              : vlSelfRef.L1DCache__DOT__pend_q_reg);
        vlSelfRef.resp_data = ((IData)(vlSelfRef.L1DCache__DOT__refill_done)
                                ? (((QData)((IData)(
                                                    (((~ 
                                                       (- (IData)(
                                                                  (1U 
                                                                   & (vlSelfRef.L1DCache__DOT__pend_q_reg 
                                                                      >> 4U))))) 
                                                      & (((~ 
                                                           (- (IData)(
                                                                      (1U 
                                                                       & (vlSelfRef.L1DCache__DOT__pend_q_reg 
                                                                          >> 3U))))) 
                                                          & vlSelfRef.refill_data[1U]) 
                                                         | (vlSelfRef.refill_data[3U] 
                                                            & (- (IData)(
                                                                         (1U 
                                                                          & (vlSelfRef.L1DCache__DOT__pend_q_reg 
                                                                             >> 3U))))))) 
                                                     | ((((~ 
                                                           (- (IData)(
                                                                      (1U 
                                                                       & (vlSelfRef.L1DCache__DOT__pend_q_reg 
                                                                          >> 3U))))) 
                                                          & vlSelfRef.refill_data[5U]) 
                                                         | (vlSelfRef.refill_data[7U] 
                                                            & (- (IData)(
                                                                         (1U 
                                                                          & (vlSelfRef.L1DCache__DOT__pend_q_reg 
                                                                             >> 3U)))))) 
                                                        & (- (IData)(
                                                                     (1U 
                                                                      & (vlSelfRef.L1DCache__DOT__pend_q_reg 
                                                                         >> 4U)))))))) 
                                    << 0x00000020U) 
                                   | (QData)((IData)(
                                                     ((0x00000010U 
                                                       & vlSelfRef.L1DCache__DOT__pend_q_reg)
                                                       ? 
                                                      (((~ 
                                                         (- (IData)(
                                                                    (1U 
                                                                     & (vlSelfRef.L1DCache__DOT__pend_q_reg 
                                                                        >> 3U))))) 
                                                        & (((~ 
                                                             (- (IData)(
                                                                        (1U 
                                                                         & (vlSelfRef.L1DCache__DOT__pend_q_reg 
                                                                            >> 2U))))) 
                                                            & vlSelfRef.refill_data[4U]) 
                                                           | (vlSelfRef.refill_data[5U] 
                                                              & (- (IData)(
                                                                           (1U 
                                                                            & (vlSelfRef.L1DCache__DOT__pend_q_reg 
                                                                               >> 2U))))))) 
                                                       | ((((~ 
                                                             (- (IData)(
                                                                        (1U 
                                                                         & (vlSelfRef.L1DCache__DOT__pend_q_reg 
                                                                            >> 2U))))) 
                                                            & vlSelfRef.refill_data[6U]) 
                                                           | (vlSelfRef.refill_data[7U] 
                                                              & (- (IData)(
                                                                           (1U 
                                                                            & (vlSelfRef.L1DCache__DOT__pend_q_reg 
                                                                               >> 2U)))))) 
                                                          & (- (IData)(
                                                                       (1U 
                                                                        & (vlSelfRef.L1DCache__DOT__pend_q_reg 
                                                                           >> 3U))))))
                                                       : 
                                                      (((~ 
                                                         (- (IData)(
                                                                    (1U 
                                                                     & (vlSelfRef.L1DCache__DOT__pend_q_reg 
                                                                        >> 3U))))) 
                                                        & (((~ 
                                                             (- (IData)(
                                                                        (1U 
                                                                         & (vlSelfRef.L1DCache__DOT__pend_q_reg 
                                                                            >> 2U))))) 
                                                            & vlSelfRef.refill_data[0U]) 
                                                           | (vlSelfRef.refill_data[1U] 
                                                              & (- (IData)(
                                                                           (1U 
                                                                            & (vlSelfRef.L1DCache__DOT__pend_q_reg 
                                                                               >> 2U))))))) 
                                                       | ((((~ 
                                                             (- (IData)(
                                                                        (1U 
                                                                         & (vlSelfRef.L1DCache__DOT__pend_q_reg 
                                                                            >> 2U))))) 
                                                            & vlSelfRef.refill_data[2U]) 
                                                           | (vlSelfRef.refill_data[3U] 
                                                              & (- (IData)(
                                                                           (1U 
                                                                            & (vlSelfRef.L1DCache__DOT__pend_q_reg 
                                                                               >> 2U)))))) 
                                                          & (- (IData)(
                                                                       (1U 
                                                                        & (vlSelfRef.L1DCache__DOT__pend_q_reg 
                                                                           >> 3U))))))))))
                                : ((IData)(vlSelfRef.L1DCache__DOT__way1_hit)
                                    ? (((QData)((IData)(
                                                        (((~ 
                                                           (- (IData)(
                                                                      (1U 
                                                                       & (vlSelfRef.req_addr 
                                                                          >> 4U))))) 
                                                          & (((~ 
                                                               (- (IData)(
                                                                          (1U 
                                                                           & (vlSelfRef.req_addr 
                                                                              >> 3U))))) 
                                                              & vlSelfRef.L1DCache__DOT____Vcellinp__u_data_word_mux_w1__in1) 
                                                             | (vlSelfRef.L1DCache__DOT____Vcellinp__u_data_word_mux_w1__in3 
                                                                & (- (IData)(
                                                                             (1U 
                                                                              & (vlSelfRef.req_addr 
                                                                                >> 3U))))))) 
                                                         | ((((~ 
                                                               (- (IData)(
                                                                          (1U 
                                                                           & (vlSelfRef.req_addr 
                                                                              >> 3U))))) 
                                                              & vlSelfRef.L1DCache__DOT____Vcellinp__u_data_word_mux_w1__in5) 
                                                             | (vlSelfRef.L1DCache__DOT____Vcellinp__u_data_word_mux_w1__in7 
                                                                & (- (IData)(
                                                                             (1U 
                                                                              & (vlSelfRef.req_addr 
                                                                                >> 3U)))))) 
                                                            & (- (IData)(
                                                                         (1U 
                                                                          & (vlSelfRef.req_addr 
                                                                             >> 4U)))))))) 
                                        << 0x00000020U) 
                                       | (QData)((IData)(
                                                         ((0x00000010U 
                                                           & vlSelfRef.req_addr)
                                                           ? 
                                                          (((~ 
                                                             (- (IData)(
                                                                        (1U 
                                                                         & (vlSelfRef.req_addr 
                                                                            >> 3U))))) 
                                                            & (((~ 
                                                                 (- (IData)(
                                                                            (1U 
                                                                             & (vlSelfRef.req_addr 
                                                                                >> 2U))))) 
                                                                & vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                [vlSelfRef.L1DCache__DOT__data_rd_addr][4U]) 
                                                               | (vlSelfRef.L1DCache__DOT____Vcellinp__u_data_word_mux_w1__in5 
                                                                  & (- (IData)(
                                                                               (1U 
                                                                                & (vlSelfRef.req_addr 
                                                                                >> 2U))))))) 
                                                           | ((((~ 
                                                                 (- (IData)(
                                                                            (1U 
                                                                             & (vlSelfRef.req_addr 
                                                                                >> 2U))))) 
                                                                & vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                [vlSelfRef.L1DCache__DOT__data_rd_addr][6U]) 
                                                               | (vlSelfRef.L1DCache__DOT____Vcellinp__u_data_word_mux_w1__in7 
                                                                  & (- (IData)(
                                                                               (1U 
                                                                                & (vlSelfRef.req_addr 
                                                                                >> 2U)))))) 
                                                              & (- (IData)(
                                                                           (1U 
                                                                            & (vlSelfRef.req_addr 
                                                                               >> 3U))))))
                                                           : 
                                                          (((~ 
                                                             (- (IData)(
                                                                        (1U 
                                                                         & (vlSelfRef.req_addr 
                                                                            >> 3U))))) 
                                                            & (((~ 
                                                                 (- (IData)(
                                                                            (1U 
                                                                             & (vlSelfRef.req_addr 
                                                                                >> 2U))))) 
                                                                & vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                [vlSelfRef.L1DCache__DOT__data_rd_addr][0U]) 
                                                               | (vlSelfRef.L1DCache__DOT____Vcellinp__u_data_word_mux_w1__in1 
                                                                  & (- (IData)(
                                                                               (1U 
                                                                                & (vlSelfRef.req_addr 
                                                                                >> 2U))))))) 
                                                           | ((((~ 
                                                                 (- (IData)(
                                                                            (1U 
                                                                             & (vlSelfRef.req_addr 
                                                                                >> 2U))))) 
                                                                & vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                [vlSelfRef.L1DCache__DOT__data_rd_addr][2U]) 
                                                               | (vlSelfRef.L1DCache__DOT____Vcellinp__u_data_word_mux_w1__in3 
                                                                  & (- (IData)(
                                                                               (1U 
                                                                                & (vlSelfRef.req_addr 
                                                                                >> 2U)))))) 
                                                              & (- (IData)(
                                                                           (1U 
                                                                            & (vlSelfRef.req_addr 
                                                                               >> 3U))))))))))
                                    : (((QData)((IData)(
                                                        (((~ 
                                                           (- (IData)(
                                                                      (1U 
                                                                       & (vlSelfRef.req_addr 
                                                                          >> 4U))))) 
                                                          & (((~ 
                                                               (- (IData)(
                                                                          (1U 
                                                                           & (vlSelfRef.req_addr 
                                                                              >> 3U))))) 
                                                              & vlSelfRef.L1DCache__DOT____Vcellinp__u_data_word_mux_w0__in1) 
                                                             | (vlSelfRef.L1DCache__DOT____Vcellinp__u_data_word_mux_w0__in3 
                                                                & (- (IData)(
                                                                             (1U 
                                                                              & (vlSelfRef.req_addr 
                                                                                >> 3U))))))) 
                                                         | ((- (IData)(
                                                                       (1U 
                                                                        & (vlSelfRef.req_addr 
                                                                           >> 4U)))) 
                                                            & (((~ 
                                                                 (- (IData)(
                                                                            (1U 
                                                                             & (vlSelfRef.req_addr 
                                                                                >> 3U))))) 
                                                                & vlSelfRef.L1DCache__DOT____Vcellinp__u_data_word_mux_w0__in5) 
                                                               | (vlSelfRef.L1DCache__DOT____Vcellinp__u_data_word_mux_w0__in7 
                                                                  & (- (IData)(
                                                                               (1U 
                                                                                & (vlSelfRef.req_addr 
                                                                                >> 3U)))))))))) 
                                        << 0x00000020U) 
                                       | (QData)((IData)(
                                                         ((0x00000010U 
                                                           & vlSelfRef.req_addr)
                                                           ? 
                                                          (((~ 
                                                             (- (IData)(
                                                                        (1U 
                                                                         & (vlSelfRef.req_addr 
                                                                            >> 3U))))) 
                                                            & (((~ 
                                                                 (- (IData)(
                                                                            (1U 
                                                                             & (vlSelfRef.req_addr 
                                                                                >> 2U))))) 
                                                                & vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                [vlSelfRef.L1DCache__DOT__data_rd_addr][4U]) 
                                                               | (vlSelfRef.L1DCache__DOT____Vcellinp__u_data_word_mux_w0__in5 
                                                                  & (- (IData)(
                                                                               (1U 
                                                                                & (vlSelfRef.req_addr 
                                                                                >> 2U))))))) 
                                                           | ((((~ 
                                                                 (- (IData)(
                                                                            (1U 
                                                                             & (vlSelfRef.req_addr 
                                                                                >> 2U))))) 
                                                                & vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                [vlSelfRef.L1DCache__DOT__data_rd_addr][6U]) 
                                                               | (vlSelfRef.L1DCache__DOT____Vcellinp__u_data_word_mux_w0__in7 
                                                                  & (- (IData)(
                                                                               (1U 
                                                                                & (vlSelfRef.req_addr 
                                                                                >> 2U)))))) 
                                                              & (- (IData)(
                                                                           (1U 
                                                                            & (vlSelfRef.req_addr 
                                                                               >> 3U))))))
                                                           : 
                                                          (((~ 
                                                             (- (IData)(
                                                                        (1U 
                                                                         & (vlSelfRef.req_addr 
                                                                            >> 3U))))) 
                                                            & (((~ 
                                                                 (- (IData)(
                                                                            (1U 
                                                                             & (vlSelfRef.req_addr 
                                                                                >> 2U))))) 
                                                                & vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                [vlSelfRef.L1DCache__DOT__data_rd_addr][0U]) 
                                                               | (vlSelfRef.L1DCache__DOT____Vcellinp__u_data_word_mux_w0__in1 
                                                                  & (- (IData)(
                                                                               (1U 
                                                                                & (vlSelfRef.req_addr 
                                                                                >> 2U))))))) 
                                                           | ((((~ 
                                                                 (- (IData)(
                                                                            (1U 
                                                                             & (vlSelfRef.req_addr 
                                                                                >> 2U))))) 
                                                                & vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                [vlSelfRef.L1DCache__DOT__data_rd_addr][2U]) 
                                                               | (vlSelfRef.L1DCache__DOT____Vcellinp__u_data_word_mux_w0__in3 
                                                                  & (- (IData)(
                                                                               (1U 
                                                                                & (vlSelfRef.req_addr 
                                                                                >> 2U)))))) 
                                                              & (- (IData)(
                                                                           (1U 
                                                                            & (vlSelfRef.req_addr 
                                                                               >> 3U))))))))))));
        vlSelfRef.L1DCache__DOT__fsm_q_reg = (((((IData)(vlSelfRef.L1DCache__DOT__miss_detect) 
                                                 & (IData)(vlSelfRef.L1DCache__DOT__victim_needs_wb)) 
                                                << 1U) 
                                               | (((~ (IData)(vlSelfRef.refill_valid)) 
                                                   & (IData)(vlSelfRef.L1DCache__DOT__is_refill_wait)) 
                                                  | (IData)(vlSelfRef.L1DCache__DOT__miss_detect_clean))) 
                                              | ((((~ (IData)(vlSelfRef.wb_ack)) 
                                                   & (IData)(vlSelfRef.wb_valid)) 
                                                  << 1U) 
                                                 | ((IData)(vlSelfRef.wb_ack) 
                                                    & (IData)(vlSelfRef.wb_valid))));
    }
    vlSelfRef.L1DCache__DOT__pend_q_reg = __Vdly__L1DCache__DOT__pend_q_reg;
    vlSelfRef.L1DCache__DOT__victim_lru = (0U != ((IData)(vlSelfRef.L1DCache__DOT__lru_q_reg) 
                                                  & (IData)(vlSelfRef.L1DCache__DOT__valid_dec_w0)));
    vlSelfRef.L1DCache__DOT__way0_valid_sel = (0U != 
                                               ((IData)(vlSelfRef.L1DCache__DOT__valid_q_reg) 
                                                & (IData)(vlSelfRef.L1DCache__DOT__valid_dec_w0)));
    vlSelfRef.L1DCache__DOT__way1_valid_sel = (0U != 
                                               (((IData)(vlSelfRef.L1DCache__DOT__valid_q_reg) 
                                                 >> 4U) 
                                                & (IData)(vlSelfRef.L1DCache__DOT__valid_dec_w0)));
    vlSelfRef.L1DCache__DOT__victim_needs_wb = (((IData)(vlSelfRef.L1DCache__DOT__victim_lru)
                                                  ? 
                                                 (0U 
                                                  != 
                                                  (((IData)(vlSelfRef.L1DCache__DOT__dirty_q_reg) 
                                                    >> 4U) 
                                                   & (IData)(vlSelfRef.L1DCache__DOT__valid_dec_w0)))
                                                  : 
                                                 (0U 
                                                  != 
                                                  ((IData)(vlSelfRef.L1DCache__DOT__dirty_q_reg) 
                                                   & (IData)(vlSelfRef.L1DCache__DOT__valid_dec_w0)))) 
                                                & ((IData)(vlSelfRef.L1DCache__DOT__victim_lru)
                                                    ? (IData)(vlSelfRef.L1DCache__DOT__way1_valid_sel)
                                                    : (IData)(vlSelfRef.L1DCache__DOT__way0_valid_sel)));
    vlSelfRef.L1DCache__DOT__is_refill_wait = ((IData)(vlSelfRef.L1DCache__DOT__fsm_q_reg) 
                                               & (3U 
                                                  == 
                                                  (3U 
                                                   & (~ 
                                                      ((IData)(vlSelfRef.L1DCache__DOT__fsm_q_reg) 
                                                       >> 1U)))));
    vlSelfRef.wb_valid = (IData)((2U == (IData)(vlSelfRef.L1DCache__DOT__fsm_q_reg)));
    vlSelfRef.miss_addr = (((IData)(vlSelfRef.L1DCache__DOT__is_refill_wait)
                             ? (vlSelfRef.L1DCache__DOT__pend_q_reg 
                                >> 5U) : (vlSelfRef.req_addr 
                                          >> 5U)) << 5U);
}

void VL1DCache___024root___nba_sequent__TOP__1(VL1DCache___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VL1DCache___024root___nba_sequent__TOP__1\n"); );
    VL1DCache__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Locals
    VlWide<8>/*255:0*/ __VdlyVal__L1DCache__DOT__data_ram_w0__v0;
    VL_ZERO_W(256, __VdlyVal__L1DCache__DOT__data_ram_w0__v0);
    CData/*1:0*/ __VdlyDim0__L1DCache__DOT__data_ram_w0__v0;
    __VdlyDim0__L1DCache__DOT__data_ram_w0__v0 = 0;
    CData/*0:0*/ __VdlySet__L1DCache__DOT__data_ram_w0__v0;
    __VdlySet__L1DCache__DOT__data_ram_w0__v0 = 0;
    VlWide<8>/*255:0*/ __VdlyVal__L1DCache__DOT__data_ram_w1__v0;
    VL_ZERO_W(256, __VdlyVal__L1DCache__DOT__data_ram_w1__v0);
    CData/*1:0*/ __VdlyDim0__L1DCache__DOT__data_ram_w1__v0;
    __VdlyDim0__L1DCache__DOT__data_ram_w1__v0 = 0;
    CData/*0:0*/ __VdlySet__L1DCache__DOT__data_ram_w1__v0;
    __VdlySet__L1DCache__DOT__data_ram_w1__v0 = 0;
    VlWide<3>/*95:0*/ __Vtemp_1;
    VlWide<4>/*127:0*/ __Vtemp_2;
    VlWide<5>/*159:0*/ __Vtemp_3;
    VlWide<6>/*191:0*/ __Vtemp_4;
    VlWide<7>/*223:0*/ __Vtemp_5;
    VlWide<3>/*95:0*/ __Vtemp_6;
    VlWide<4>/*127:0*/ __Vtemp_7;
    VlWide<5>/*159:0*/ __Vtemp_8;
    VlWide<6>/*191:0*/ __Vtemp_9;
    VlWide<7>/*223:0*/ __Vtemp_10;
    // Body
    __VdlySet__L1DCache__DOT__data_ram_w0__v0 = 0U;
    __VdlySet__L1DCache__DOT__data_ram_w1__v0 = 0U;
    if ((((~ (IData)(vlSelfRef.L1DCache__DOT__way1_hit)) 
          & (IData)(vlSelfRef.L1DCache__DOT__write_hit)) 
         | ((~ (IData)(vlSelfRef.L1DCache__DOT__pend_victim_q_reg)) 
            & (IData)(vlSelfRef.L1DCache__DOT__refill_done)))) {
        if (vlSelfRef.L1DCache__DOT__refill_done) {
            __VdlyVal__L1DCache__DOT__data_ram_w0__v0[0U] 
                = vlSelfRef.refill_data[0U];
            __VdlyVal__L1DCache__DOT__data_ram_w0__v0[1U] 
                = vlSelfRef.refill_data[1U];
            __VdlyVal__L1DCache__DOT__data_ram_w0__v0[2U] 
                = vlSelfRef.refill_data[2U];
            __VdlyVal__L1DCache__DOT__data_ram_w0__v0[3U] 
                = vlSelfRef.refill_data[3U];
            __VdlyVal__L1DCache__DOT__data_ram_w0__v0[4U] 
                = vlSelfRef.refill_data[4U];
            __VdlyVal__L1DCache__DOT__data_ram_w0__v0[5U] 
                = vlSelfRef.refill_data[5U];
            __VdlyVal__L1DCache__DOT__data_ram_w0__v0[6U] 
                = vlSelfRef.refill_data[6U];
            __VdlyVal__L1DCache__DOT__data_ram_w0__v0[7U] 
                = vlSelfRef.refill_data[7U];
        } else {
            __Vtemp_1[0U] = ((((((((2U & (((vlSelfRef.L1DCache__DOT__ram_be_w0[5U] 
                                            >> 0x0000001fU)
                                            ? (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                               >> 0x0000001fU)
                                            : (vlSelfRef.L1DCache__DOT__data_ram_w0
                                               [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                               >> 0x0000001fU)) 
                                          << 1U)) | 
                                   (1U & ((0x40000000U 
                                           & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                           ? (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                              >> 0x0000001eU)
                                           : (vlSelfRef.L1DCache__DOT__data_ram_w0
                                              [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                              >> 0x0000001eU)))) 
                                  << 6U) | (((2U & 
                                              (((0x20000000U 
                                                 & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                                 ? 
                                                (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                                 >> 0x0000001dU)
                                                 : 
                                                (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                 [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                                 >> 0x0000001dU)) 
                                               << 1U)) 
                                             | (1U 
                                                & ((0x10000000U 
                                                    & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                                    ? 
                                                   (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                                    >> 0x0000001cU)
                                                    : 
                                                   (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                    [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                                    >> 0x0000001cU)))) 
                                            << 4U)) 
                                | ((((2U & (((0x08000000U 
                                              & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                              ? (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                                 >> 0x0000001bU)
                                              : (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                 [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                                 >> 0x0000001bU)) 
                                            << 1U)) 
                                     | (1U & ((0x04000000U 
                                               & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                               ? (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                                  >> 0x0000001aU)
                                               : (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                  [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                                  >> 0x0000001aU)))) 
                                    << 2U) | ((2U & 
                                               (((0x02000000U 
                                                  & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                                  ? 
                                                 (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                                  >> 0x00000019U)
                                                  : 
                                                 (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                  [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                                  >> 0x00000019U)) 
                                                << 1U)) 
                                              | (1U 
                                                 & ((0x01000000U 
                                                     & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                                     ? 
                                                    (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                                     >> 0x00000018U)
                                                     : 
                                                    (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                                     >> 0x00000018U)))))) 
                               << 0x00000018U) | ((
                                                   ((((2U 
                                                       & (((0x00800000U 
                                                            & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                                            ? 
                                                           (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                                            >> 0x00000017U)
                                                            : 
                                                           (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                            [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                                            >> 0x00000017U)) 
                                                          << 1U)) 
                                                      | (1U 
                                                         & ((0x00400000U 
                                                             & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                                             ? 
                                                            (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                                             >> 0x00000016U)
                                                             : 
                                                            (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                             [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                                             >> 0x00000016U)))) 
                                                     << 6U) 
                                                    | (((2U 
                                                         & (((0x00200000U 
                                                              & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                                              ? 
                                                             (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                                              >> 0x00000015U)
                                                              : 
                                                             (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                              [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                                              >> 0x00000015U)) 
                                                            << 1U)) 
                                                        | (1U 
                                                           & ((0x00100000U 
                                                               & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                                               ? 
                                                              (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                                               >> 0x00000014U)
                                                               : 
                                                              (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                               [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                                               >> 0x00000014U)))) 
                                                       << 4U)) 
                                                   | ((((2U 
                                                         & (((0x00080000U 
                                                              & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                                              ? 
                                                             (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                                              >> 0x00000013U)
                                                              : 
                                                             (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                              [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                                              >> 0x00000013U)) 
                                                            << 1U)) 
                                                        | (1U 
                                                           & ((0x00040000U 
                                                               & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                                               ? 
                                                              (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                                               >> 0x00000012U)
                                                               : 
                                                              (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                               [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                                               >> 0x00000012U)))) 
                                                       << 2U) 
                                                      | ((2U 
                                                          & (((0x00020000U 
                                                               & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                                               ? 
                                                              (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                                               >> 0x00000011U)
                                                               : 
                                                              (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                               [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                                               >> 0x00000011U)) 
                                                             << 1U)) 
                                                         | (1U 
                                                            & ((0x00010000U 
                                                                & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                                                ? 
                                                               (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                                                >> 0x00000010U)
                                                                : 
                                                               (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                                                >> 0x00000010U)))))) 
                                                  << 0x00000010U)) 
                             | (((((((2U & (((0x00008000U 
                                              & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                              ? (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                                 >> 0x0000000fU)
                                              : (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                 [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                                 >> 0x0000000fU)) 
                                            << 1U)) 
                                     | (1U & ((0x00004000U 
                                               & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                               ? (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                                  >> 0x0000000eU)
                                               : (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                  [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                                  >> 0x0000000eU)))) 
                                    << 6U) | (((2U 
                                                & (((0x00002000U 
                                                     & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                                     ? 
                                                    (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                                     >> 0x0000000dU)
                                                     : 
                                                    (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                                     >> 0x0000000dU)) 
                                                   << 1U)) 
                                               | (1U 
                                                  & ((0x00001000U 
                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                                      ? 
                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                                      >> 0x0000000cU)
                                                      : 
                                                     (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                                      >> 0x0000000cU)))) 
                                              << 4U)) 
                                  | ((((2U & (((0x00000800U 
                                                & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                                ? (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                                   >> 0x0000000bU)
                                                : (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                   [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                                   >> 0x0000000bU)) 
                                              << 1U)) 
                                       | (1U & ((0x00000400U 
                                                 & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                                 ? 
                                                (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                                 >> 0x0000000aU)
                                                 : 
                                                (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                 [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                                 >> 0x0000000aU)))) 
                                      << 2U) | ((2U 
                                                 & (((0x00000200U 
                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                                      ? 
                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                                      >> 9U)
                                                      : 
                                                     (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                                      >> 9U)) 
                                                    << 1U)) 
                                                | (1U 
                                                   & ((0x00000100U 
                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                                       ? 
                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                                       >> 8U)
                                                       : 
                                                      (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                                       >> 8U)))))) 
                                 << 8U) | (((((2U & 
                                               (((0x00000080U 
                                                  & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                                  ? 
                                                 (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                                  >> 7U)
                                                  : 
                                                 (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                  [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                                  >> 7U)) 
                                                << 1U)) 
                                              | (1U 
                                                 & ((0x00000040U 
                                                     & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                                     ? 
                                                    (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                                     >> 6U)
                                                     : 
                                                    (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                                     >> 6U)))) 
                                             << 6U) 
                                            | (((2U 
                                                 & (((0x00000020U 
                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                                      ? 
                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                                      >> 5U)
                                                      : 
                                                     (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                                      >> 5U)) 
                                                    << 1U)) 
                                                | (1U 
                                                   & ((0x00000010U 
                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                                       ? 
                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                                       >> 4U)
                                                       : 
                                                      (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                                       >> 4U)))) 
                                               << 4U)) 
                                           | ((((2U 
                                                 & (((8U 
                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                                      ? 
                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                                      >> 3U)
                                                      : 
                                                     (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                                      >> 3U)) 
                                                    << 1U)) 
                                                | (1U 
                                                   & ((4U 
                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                                       ? 
                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                                       >> 2U)
                                                       : 
                                                      (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                                       >> 2U)))) 
                                               << 2U) 
                                              | ((2U 
                                                  & (((2U 
                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                                       ? 
                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                                       >> 1U)
                                                       : 
                                                      (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                                       >> 1U)) 
                                                     << 1U)) 
                                                 | (1U 
                                                    & ((1U 
                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                                        ? vlSelfRef.L1DCache__DOT__wr_data_w0[5U]
                                                        : vlSelfRef.L1DCache__DOT__data_ram_w0
                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][5U])))))));
            __Vtemp_1[1U] = (IData)((((QData)((IData)(
                                                      ((((((((2U 
                                                              & (((vlSelfRef.L1DCache__DOT__ram_be_w0[7U] 
                                                                   >> 0x0000001fU)
                                                                   ? 
                                                                  (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                   >> 0x0000001fU)
                                                                   : 
                                                                  (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                   [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                   >> 0x0000001fU)) 
                                                                 << 1U)) 
                                                             | (1U 
                                                                & ((0x40000000U 
                                                                    & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                    ? 
                                                                   (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                    >> 0x0000001eU)
                                                                    : 
                                                                   (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                    [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                    >> 0x0000001eU)))) 
                                                            << 6U) 
                                                           | (((2U 
                                                                & (((0x20000000U 
                                                                     & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                     ? 
                                                                    (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                     >> 0x0000001dU)
                                                                     : 
                                                                    (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                     >> 0x0000001dU)) 
                                                                   << 1U)) 
                                                               | (1U 
                                                                  & ((0x10000000U 
                                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                      ? 
                                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                      >> 0x0000001cU)
                                                                      : 
                                                                     (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                      >> 0x0000001cU)))) 
                                                              << 4U)) 
                                                          | ((((2U 
                                                                & (((0x08000000U 
                                                                     & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                     ? 
                                                                    (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                     >> 0x0000001bU)
                                                                     : 
                                                                    (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                     >> 0x0000001bU)) 
                                                                   << 1U)) 
                                                               | (1U 
                                                                  & ((0x04000000U 
                                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                      ? 
                                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                      >> 0x0000001aU)
                                                                      : 
                                                                     (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                      >> 0x0000001aU)))) 
                                                              << 2U) 
                                                             | ((2U 
                                                                 & (((0x02000000U 
                                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                      ? 
                                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                      >> 0x00000019U)
                                                                      : 
                                                                     (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                      >> 0x00000019U)) 
                                                                    << 1U)) 
                                                                | (1U 
                                                                   & ((0x01000000U 
                                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                       ? 
                                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                       >> 0x00000018U)
                                                                       : 
                                                                      (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                       >> 0x00000018U)))))) 
                                                         << 0x00000018U) 
                                                        | ((((((2U 
                                                                & (((0x00800000U 
                                                                     & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                     ? 
                                                                    (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                     >> 0x00000017U)
                                                                     : 
                                                                    (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                     >> 0x00000017U)) 
                                                                   << 1U)) 
                                                               | (1U 
                                                                  & ((0x00400000U 
                                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                      ? 
                                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                      >> 0x00000016U)
                                                                      : 
                                                                     (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                      >> 0x00000016U)))) 
                                                              << 6U) 
                                                             | (((2U 
                                                                  & (((0x00200000U 
                                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                       ? 
                                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                       >> 0x00000015U)
                                                                       : 
                                                                      (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                       >> 0x00000015U)) 
                                                                     << 1U)) 
                                                                 | (1U 
                                                                    & ((0x00100000U 
                                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                        ? 
                                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                        >> 0x00000014U)
                                                                        : 
                                                                       (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                        >> 0x00000014U)))) 
                                                                << 4U)) 
                                                            | ((((2U 
                                                                  & (((0x00080000U 
                                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                       ? 
                                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                       >> 0x00000013U)
                                                                       : 
                                                                      (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                       >> 0x00000013U)) 
                                                                     << 1U)) 
                                                                 | (1U 
                                                                    & ((0x00040000U 
                                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                        ? 
                                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                        >> 0x00000012U)
                                                                        : 
                                                                       (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                        >> 0x00000012U)))) 
                                                                << 2U) 
                                                               | ((2U 
                                                                   & (((0x00020000U 
                                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                        ? 
                                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                        >> 0x00000011U)
                                                                        : 
                                                                       (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                        >> 0x00000011U)) 
                                                                      << 1U)) 
                                                                  | (1U 
                                                                     & ((0x00010000U 
                                                                         & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                         ? 
                                                                        (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                         >> 0x00000010U)
                                                                         : 
                                                                        (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                         [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                         >> 0x00000010U)))))) 
                                                           << 0x00000010U)) 
                                                       | (((((((2U 
                                                                & (((0x00008000U 
                                                                     & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                     ? 
                                                                    (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                     >> 0x0000000fU)
                                                                     : 
                                                                    (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                     >> 0x0000000fU)) 
                                                                   << 1U)) 
                                                               | (1U 
                                                                  & ((0x00004000U 
                                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                      ? 
                                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                      >> 0x0000000eU)
                                                                      : 
                                                                     (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                      >> 0x0000000eU)))) 
                                                              << 6U) 
                                                             | (((2U 
                                                                  & (((0x00002000U 
                                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                       ? 
                                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                       >> 0x0000000dU)
                                                                       : 
                                                                      (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                       >> 0x0000000dU)) 
                                                                     << 1U)) 
                                                                 | (1U 
                                                                    & ((0x00001000U 
                                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                        ? 
                                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                        >> 0x0000000cU)
                                                                        : 
                                                                       (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                        >> 0x0000000cU)))) 
                                                                << 4U)) 
                                                            | ((((2U 
                                                                  & (((0x00000800U 
                                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                       ? 
                                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                       >> 0x0000000bU)
                                                                       : 
                                                                      (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                       >> 0x0000000bU)) 
                                                                     << 1U)) 
                                                                 | (1U 
                                                                    & ((0x00000400U 
                                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                        ? 
                                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                        >> 0x0000000aU)
                                                                        : 
                                                                       (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                        >> 0x0000000aU)))) 
                                                                << 2U) 
                                                               | ((2U 
                                                                   & (((0x00000200U 
                                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                        ? 
                                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                        >> 9U)
                                                                        : 
                                                                       (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                        >> 9U)) 
                                                                      << 1U)) 
                                                                  | (1U 
                                                                     & ((0x00000100U 
                                                                         & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                         ? 
                                                                        (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                         >> 8U)
                                                                         : 
                                                                        (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                         [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                         >> 8U)))))) 
                                                           << 8U) 
                                                          | (((((2U 
                                                                 & (((0x00000080U 
                                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                      ? 
                                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                      >> 7U)
                                                                      : 
                                                                     (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                      >> 7U)) 
                                                                    << 1U)) 
                                                                | (1U 
                                                                   & ((0x00000040U 
                                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                       ? 
                                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                       >> 6U)
                                                                       : 
                                                                      (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                       >> 6U)))) 
                                                               << 6U) 
                                                              | (((2U 
                                                                   & (((0x00000020U 
                                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                        ? 
                                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                        >> 5U)
                                                                        : 
                                                                       (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                        >> 5U)) 
                                                                      << 1U)) 
                                                                  | (1U 
                                                                     & ((0x00000010U 
                                                                         & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                         ? 
                                                                        (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                         >> 4U)
                                                                         : 
                                                                        (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                         [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                         >> 4U)))) 
                                                                 << 4U)) 
                                                             | ((((2U 
                                                                   & (((8U 
                                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                        ? 
                                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                        >> 3U)
                                                                        : 
                                                                       (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                        >> 3U)) 
                                                                      << 1U)) 
                                                                  | (1U 
                                                                     & ((4U 
                                                                         & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                         ? 
                                                                        (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                         >> 2U)
                                                                         : 
                                                                        (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                         [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                         >> 2U)))) 
                                                                 << 2U) 
                                                                | ((2U 
                                                                    & (((2U 
                                                                         & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                         ? 
                                                                        (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                         >> 1U)
                                                                         : 
                                                                        (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                         [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                         >> 1U)) 
                                                                       << 1U)) 
                                                                   | (1U 
                                                                      & ((1U 
                                                                          & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                          ? vlSelfRef.L1DCache__DOT__wr_data_w0[7U]
                                                                          : vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                         [vlSelfRef.L1DCache__DOT__data_rd_addr][7U]))))))))) 
                                      << 0x00000020U) 
                                     | (QData)((IData)(
                                                       ((((((((2U 
                                                               & (((vlSelfRef.L1DCache__DOT__ram_be_w0[6U] 
                                                                    >> 0x0000001fU)
                                                                    ? 
                                                                   (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                    >> 0x0000001fU)
                                                                    : 
                                                                   (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                    [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                    >> 0x0000001fU)) 
                                                                  << 1U)) 
                                                              | (1U 
                                                                 & ((0x40000000U 
                                                                     & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                     ? 
                                                                    (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                     >> 0x0000001eU)
                                                                     : 
                                                                    (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                     >> 0x0000001eU)))) 
                                                             << 6U) 
                                                            | (((2U 
                                                                 & (((0x20000000U 
                                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                      ? 
                                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                      >> 0x0000001dU)
                                                                      : 
                                                                     (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                      >> 0x0000001dU)) 
                                                                    << 1U)) 
                                                                | (1U 
                                                                   & ((0x10000000U 
                                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                       ? 
                                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                       >> 0x0000001cU)
                                                                       : 
                                                                      (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                       >> 0x0000001cU)))) 
                                                               << 4U)) 
                                                           | ((((2U 
                                                                 & (((0x08000000U 
                                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                      ? 
                                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                      >> 0x0000001bU)
                                                                      : 
                                                                     (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                      >> 0x0000001bU)) 
                                                                    << 1U)) 
                                                                | (1U 
                                                                   & ((0x04000000U 
                                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                       ? 
                                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                       >> 0x0000001aU)
                                                                       : 
                                                                      (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                       >> 0x0000001aU)))) 
                                                               << 2U) 
                                                              | ((2U 
                                                                  & (((0x02000000U 
                                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                       ? 
                                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                       >> 0x00000019U)
                                                                       : 
                                                                      (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                       >> 0x00000019U)) 
                                                                     << 1U)) 
                                                                 | (1U 
                                                                    & ((0x01000000U 
                                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                        ? 
                                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                        >> 0x00000018U)
                                                                        : 
                                                                       (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                        >> 0x00000018U)))))) 
                                                          << 0x00000018U) 
                                                         | ((((((2U 
                                                                 & (((0x00800000U 
                                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                      ? 
                                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                      >> 0x00000017U)
                                                                      : 
                                                                     (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                      >> 0x00000017U)) 
                                                                    << 1U)) 
                                                                | (1U 
                                                                   & ((0x00400000U 
                                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                       ? 
                                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                       >> 0x00000016U)
                                                                       : 
                                                                      (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                       >> 0x00000016U)))) 
                                                               << 6U) 
                                                              | (((2U 
                                                                   & (((0x00200000U 
                                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                        ? 
                                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                        >> 0x00000015U)
                                                                        : 
                                                                       (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                        >> 0x00000015U)) 
                                                                      << 1U)) 
                                                                  | (1U 
                                                                     & ((0x00100000U 
                                                                         & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                         ? 
                                                                        (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                         >> 0x00000014U)
                                                                         : 
                                                                        (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                         [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                         >> 0x00000014U)))) 
                                                                 << 4U)) 
                                                             | ((((2U 
                                                                   & (((0x00080000U 
                                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                        ? 
                                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                        >> 0x00000013U)
                                                                        : 
                                                                       (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                        >> 0x00000013U)) 
                                                                      << 1U)) 
                                                                  | (1U 
                                                                     & ((0x00040000U 
                                                                         & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                         ? 
                                                                        (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                         >> 0x00000012U)
                                                                         : 
                                                                        (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                         [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                         >> 0x00000012U)))) 
                                                                 << 2U) 
                                                                | ((2U 
                                                                    & (((0x00020000U 
                                                                         & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                         ? 
                                                                        (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                         >> 0x00000011U)
                                                                         : 
                                                                        (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                         [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                         >> 0x00000011U)) 
                                                                       << 1U)) 
                                                                   | (1U 
                                                                      & ((0x00010000U 
                                                                          & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                          ? 
                                                                         (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                          >> 0x00000010U)
                                                                          : 
                                                                         (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                          [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                          >> 0x00000010U)))))) 
                                                            << 0x00000010U)) 
                                                        | (((((((2U 
                                                                 & (((0x00008000U 
                                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                      ? 
                                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                      >> 0x0000000fU)
                                                                      : 
                                                                     (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                      >> 0x0000000fU)) 
                                                                    << 1U)) 
                                                                | (1U 
                                                                   & ((0x00004000U 
                                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                       ? 
                                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                       >> 0x0000000eU)
                                                                       : 
                                                                      (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                       >> 0x0000000eU)))) 
                                                               << 6U) 
                                                              | (((2U 
                                                                   & (((0x00002000U 
                                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                        ? 
                                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                        >> 0x0000000dU)
                                                                        : 
                                                                       (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                        >> 0x0000000dU)) 
                                                                      << 1U)) 
                                                                  | (1U 
                                                                     & ((0x00001000U 
                                                                         & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                         ? 
                                                                        (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                         >> 0x0000000cU)
                                                                         : 
                                                                        (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                         [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                         >> 0x0000000cU)))) 
                                                                 << 4U)) 
                                                             | ((((2U 
                                                                   & (((0x00000800U 
                                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                        ? 
                                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                        >> 0x0000000bU)
                                                                        : 
                                                                       (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                        >> 0x0000000bU)) 
                                                                      << 1U)) 
                                                                  | (1U 
                                                                     & ((0x00000400U 
                                                                         & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                         ? 
                                                                        (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                         >> 0x0000000aU)
                                                                         : 
                                                                        (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                         [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                         >> 0x0000000aU)))) 
                                                                 << 2U) 
                                                                | ((2U 
                                                                    & (((0x00000200U 
                                                                         & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                         ? 
                                                                        (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                         >> 9U)
                                                                         : 
                                                                        (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                         [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                         >> 9U)) 
                                                                       << 1U)) 
                                                                   | (1U 
                                                                      & ((0x00000100U 
                                                                          & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                          ? 
                                                                         (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                          >> 8U)
                                                                          : 
                                                                         (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                          [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                          >> 8U)))))) 
                                                            << 8U) 
                                                           | (((((2U 
                                                                  & (((0x00000080U 
                                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                       ? 
                                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                       >> 7U)
                                                                       : 
                                                                      (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                       >> 7U)) 
                                                                     << 1U)) 
                                                                 | (1U 
                                                                    & ((0x00000040U 
                                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                        ? 
                                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                        >> 6U)
                                                                        : 
                                                                       (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                        >> 6U)))) 
                                                                << 6U) 
                                                               | (((2U 
                                                                    & (((0x00000020U 
                                                                         & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                         ? 
                                                                        (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                         >> 5U)
                                                                         : 
                                                                        (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                         [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                         >> 5U)) 
                                                                       << 1U)) 
                                                                   | (1U 
                                                                      & ((0x00000010U 
                                                                          & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                          ? 
                                                                         (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                          >> 4U)
                                                                          : 
                                                                         (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                          [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                          >> 4U)))) 
                                                                  << 4U)) 
                                                              | ((((2U 
                                                                    & (((8U 
                                                                         & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                         ? 
                                                                        (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                         >> 3U)
                                                                         : 
                                                                        (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                         [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                         >> 3U)) 
                                                                       << 1U)) 
                                                                   | (1U 
                                                                      & ((4U 
                                                                          & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                          ? 
                                                                         (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                          >> 2U)
                                                                          : 
                                                                         (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                          [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                          >> 2U)))) 
                                                                  << 2U) 
                                                                 | ((2U 
                                                                     & (((2U 
                                                                          & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                          ? 
                                                                         (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                          >> 1U)
                                                                          : 
                                                                         (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                          [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                          >> 1U)) 
                                                                        << 1U)) 
                                                                    | (1U 
                                                                       & ((1U 
                                                                           & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                           ? vlSelfRef.L1DCache__DOT__wr_data_w0[6U]
                                                                           : vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                          [vlSelfRef.L1DCache__DOT__data_rd_addr][6U])))))))))));
            __Vtemp_1[2U] = (IData)(((((QData)((IData)(
                                                       ((((((((2U 
                                                               & (((vlSelfRef.L1DCache__DOT__ram_be_w0[7U] 
                                                                    >> 0x0000001fU)
                                                                    ? 
                                                                   (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                    >> 0x0000001fU)
                                                                    : 
                                                                   (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                    [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                    >> 0x0000001fU)) 
                                                                  << 1U)) 
                                                              | (1U 
                                                                 & ((0x40000000U 
                                                                     & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                     ? 
                                                                    (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                     >> 0x0000001eU)
                                                                     : 
                                                                    (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                     >> 0x0000001eU)))) 
                                                             << 6U) 
                                                            | (((2U 
                                                                 & (((0x20000000U 
                                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                      ? 
                                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                      >> 0x0000001dU)
                                                                      : 
                                                                     (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                      >> 0x0000001dU)) 
                                                                    << 1U)) 
                                                                | (1U 
                                                                   & ((0x10000000U 
                                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                       ? 
                                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                       >> 0x0000001cU)
                                                                       : 
                                                                      (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                       >> 0x0000001cU)))) 
                                                               << 4U)) 
                                                           | ((((2U 
                                                                 & (((0x08000000U 
                                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                      ? 
                                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                      >> 0x0000001bU)
                                                                      : 
                                                                     (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                      >> 0x0000001bU)) 
                                                                    << 1U)) 
                                                                | (1U 
                                                                   & ((0x04000000U 
                                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                       ? 
                                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                       >> 0x0000001aU)
                                                                       : 
                                                                      (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                       >> 0x0000001aU)))) 
                                                               << 2U) 
                                                              | ((2U 
                                                                  & (((0x02000000U 
                                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                       ? 
                                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                       >> 0x00000019U)
                                                                       : 
                                                                      (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                       >> 0x00000019U)) 
                                                                     << 1U)) 
                                                                 | (1U 
                                                                    & ((0x01000000U 
                                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                        ? 
                                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                        >> 0x00000018U)
                                                                        : 
                                                                       (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                        >> 0x00000018U)))))) 
                                                          << 0x00000018U) 
                                                         | ((((((2U 
                                                                 & (((0x00800000U 
                                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                      ? 
                                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                      >> 0x00000017U)
                                                                      : 
                                                                     (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                      >> 0x00000017U)) 
                                                                    << 1U)) 
                                                                | (1U 
                                                                   & ((0x00400000U 
                                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                       ? 
                                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                       >> 0x00000016U)
                                                                       : 
                                                                      (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                       >> 0x00000016U)))) 
                                                               << 6U) 
                                                              | (((2U 
                                                                   & (((0x00200000U 
                                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                        ? 
                                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                        >> 0x00000015U)
                                                                        : 
                                                                       (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                        >> 0x00000015U)) 
                                                                      << 1U)) 
                                                                  | (1U 
                                                                     & ((0x00100000U 
                                                                         & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                         ? 
                                                                        (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                         >> 0x00000014U)
                                                                         : 
                                                                        (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                         [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                         >> 0x00000014U)))) 
                                                                 << 4U)) 
                                                             | ((((2U 
                                                                   & (((0x00080000U 
                                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                        ? 
                                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                        >> 0x00000013U)
                                                                        : 
                                                                       (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                        >> 0x00000013U)) 
                                                                      << 1U)) 
                                                                  | (1U 
                                                                     & ((0x00040000U 
                                                                         & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                         ? 
                                                                        (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                         >> 0x00000012U)
                                                                         : 
                                                                        (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                         [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                         >> 0x00000012U)))) 
                                                                 << 2U) 
                                                                | ((2U 
                                                                    & (((0x00020000U 
                                                                         & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                         ? 
                                                                        (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                         >> 0x00000011U)
                                                                         : 
                                                                        (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                         [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                         >> 0x00000011U)) 
                                                                       << 1U)) 
                                                                   | (1U 
                                                                      & ((0x00010000U 
                                                                          & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                          ? 
                                                                         (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                          >> 0x00000010U)
                                                                          : 
                                                                         (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                          [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                          >> 0x00000010U)))))) 
                                                            << 0x00000010U)) 
                                                        | (((((((2U 
                                                                 & (((0x00008000U 
                                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                      ? 
                                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                      >> 0x0000000fU)
                                                                      : 
                                                                     (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                      >> 0x0000000fU)) 
                                                                    << 1U)) 
                                                                | (1U 
                                                                   & ((0x00004000U 
                                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                       ? 
                                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                       >> 0x0000000eU)
                                                                       : 
                                                                      (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                       >> 0x0000000eU)))) 
                                                               << 6U) 
                                                              | (((2U 
                                                                   & (((0x00002000U 
                                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                        ? 
                                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                        >> 0x0000000dU)
                                                                        : 
                                                                       (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                        >> 0x0000000dU)) 
                                                                      << 1U)) 
                                                                  | (1U 
                                                                     & ((0x00001000U 
                                                                         & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                         ? 
                                                                        (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                         >> 0x0000000cU)
                                                                         : 
                                                                        (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                         [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                         >> 0x0000000cU)))) 
                                                                 << 4U)) 
                                                             | ((((2U 
                                                                   & (((0x00000800U 
                                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                        ? 
                                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                        >> 0x0000000bU)
                                                                        : 
                                                                       (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                        >> 0x0000000bU)) 
                                                                      << 1U)) 
                                                                  | (1U 
                                                                     & ((0x00000400U 
                                                                         & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                         ? 
                                                                        (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                         >> 0x0000000aU)
                                                                         : 
                                                                        (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                         [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                         >> 0x0000000aU)))) 
                                                                 << 2U) 
                                                                | ((2U 
                                                                    & (((0x00000200U 
                                                                         & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                         ? 
                                                                        (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                         >> 9U)
                                                                         : 
                                                                        (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                         [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                         >> 9U)) 
                                                                       << 1U)) 
                                                                   | (1U 
                                                                      & ((0x00000100U 
                                                                          & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                          ? 
                                                                         (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                          >> 8U)
                                                                          : 
                                                                         (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                          [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                          >> 8U)))))) 
                                                            << 8U) 
                                                           | (((((2U 
                                                                  & (((0x00000080U 
                                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                       ? 
                                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                       >> 7U)
                                                                       : 
                                                                      (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                       >> 7U)) 
                                                                     << 1U)) 
                                                                 | (1U 
                                                                    & ((0x00000040U 
                                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                        ? 
                                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                        >> 6U)
                                                                        : 
                                                                       (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                        >> 6U)))) 
                                                                << 6U) 
                                                               | (((2U 
                                                                    & (((0x00000020U 
                                                                         & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                         ? 
                                                                        (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                         >> 5U)
                                                                         : 
                                                                        (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                         [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                         >> 5U)) 
                                                                       << 1U)) 
                                                                   | (1U 
                                                                      & ((0x00000010U 
                                                                          & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                          ? 
                                                                         (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                          >> 4U)
                                                                          : 
                                                                         (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                          [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                          >> 4U)))) 
                                                                  << 4U)) 
                                                              | ((((2U 
                                                                    & (((8U 
                                                                         & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                         ? 
                                                                        (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                         >> 3U)
                                                                         : 
                                                                        (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                         [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                         >> 3U)) 
                                                                       << 1U)) 
                                                                   | (1U 
                                                                      & ((4U 
                                                                          & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                          ? 
                                                                         (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                          >> 2U)
                                                                          : 
                                                                         (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                          [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                          >> 2U)))) 
                                                                  << 2U) 
                                                                 | ((2U 
                                                                     & (((2U 
                                                                          & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                          ? 
                                                                         (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                          >> 1U)
                                                                          : 
                                                                         (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                          [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                          >> 1U)) 
                                                                        << 1U)) 
                                                                    | (1U 
                                                                       & ((1U 
                                                                           & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                           ? vlSelfRef.L1DCache__DOT__wr_data_w0[7U]
                                                                           : vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                          [vlSelfRef.L1DCache__DOT__data_rd_addr][7U]))))))))) 
                                       << 0x00000020U) 
                                      | (QData)((IData)(
                                                        ((((((((2U 
                                                                & (((vlSelfRef.L1DCache__DOT__ram_be_w0[6U] 
                                                                     >> 0x0000001fU)
                                                                     ? 
                                                                    (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                     >> 0x0000001fU)
                                                                     : 
                                                                    (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                     >> 0x0000001fU)) 
                                                                   << 1U)) 
                                                               | (1U 
                                                                  & ((0x40000000U 
                                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                      ? 
                                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                      >> 0x0000001eU)
                                                                      : 
                                                                     (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                      >> 0x0000001eU)))) 
                                                              << 6U) 
                                                             | (((2U 
                                                                  & (((0x20000000U 
                                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                       ? 
                                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                       >> 0x0000001dU)
                                                                       : 
                                                                      (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                       >> 0x0000001dU)) 
                                                                     << 1U)) 
                                                                 | (1U 
                                                                    & ((0x10000000U 
                                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                        ? 
                                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                        >> 0x0000001cU)
                                                                        : 
                                                                       (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                        >> 0x0000001cU)))) 
                                                                << 4U)) 
                                                            | ((((2U 
                                                                  & (((0x08000000U 
                                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                       ? 
                                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                       >> 0x0000001bU)
                                                                       : 
                                                                      (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                       >> 0x0000001bU)) 
                                                                     << 1U)) 
                                                                 | (1U 
                                                                    & ((0x04000000U 
                                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                        ? 
                                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                        >> 0x0000001aU)
                                                                        : 
                                                                       (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                        >> 0x0000001aU)))) 
                                                                << 2U) 
                                                               | ((2U 
                                                                   & (((0x02000000U 
                                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                        ? 
                                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                        >> 0x00000019U)
                                                                        : 
                                                                       (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                        >> 0x00000019U)) 
                                                                      << 1U)) 
                                                                  | (1U 
                                                                     & ((0x01000000U 
                                                                         & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                         ? 
                                                                        (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                         >> 0x00000018U)
                                                                         : 
                                                                        (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                         [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                         >> 0x00000018U)))))) 
                                                           << 0x00000018U) 
                                                          | ((((((2U 
                                                                  & (((0x00800000U 
                                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                       ? 
                                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                       >> 0x00000017U)
                                                                       : 
                                                                      (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                       >> 0x00000017U)) 
                                                                     << 1U)) 
                                                                 | (1U 
                                                                    & ((0x00400000U 
                                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                        ? 
                                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                        >> 0x00000016U)
                                                                        : 
                                                                       (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                        >> 0x00000016U)))) 
                                                                << 6U) 
                                                               | (((2U 
                                                                    & (((0x00200000U 
                                                                         & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                         ? 
                                                                        (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                         >> 0x00000015U)
                                                                         : 
                                                                        (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                         [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                         >> 0x00000015U)) 
                                                                       << 1U)) 
                                                                   | (1U 
                                                                      & ((0x00100000U 
                                                                          & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                          ? 
                                                                         (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                          >> 0x00000014U)
                                                                          : 
                                                                         (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                          [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                          >> 0x00000014U)))) 
                                                                  << 4U)) 
                                                              | ((((2U 
                                                                    & (((0x00080000U 
                                                                         & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                         ? 
                                                                        (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                         >> 0x00000013U)
                                                                         : 
                                                                        (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                         [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                         >> 0x00000013U)) 
                                                                       << 1U)) 
                                                                   | (1U 
                                                                      & ((0x00040000U 
                                                                          & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                          ? 
                                                                         (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                          >> 0x00000012U)
                                                                          : 
                                                                         (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                          [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                          >> 0x00000012U)))) 
                                                                  << 2U) 
                                                                 | ((2U 
                                                                     & (((0x00020000U 
                                                                          & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                          ? 
                                                                         (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                          >> 0x00000011U)
                                                                          : 
                                                                         (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                          [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                          >> 0x00000011U)) 
                                                                        << 1U)) 
                                                                    | (1U 
                                                                       & ((0x00010000U 
                                                                           & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                           ? 
                                                                          (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                           >> 0x00000010U)
                                                                           : 
                                                                          (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                           [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                           >> 0x00000010U)))))) 
                                                             << 0x00000010U)) 
                                                         | (((((((2U 
                                                                  & (((0x00008000U 
                                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                       ? 
                                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                       >> 0x0000000fU)
                                                                       : 
                                                                      (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                       >> 0x0000000fU)) 
                                                                     << 1U)) 
                                                                 | (1U 
                                                                    & ((0x00004000U 
                                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                        ? 
                                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                        >> 0x0000000eU)
                                                                        : 
                                                                       (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                        >> 0x0000000eU)))) 
                                                                << 6U) 
                                                               | (((2U 
                                                                    & (((0x00002000U 
                                                                         & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                         ? 
                                                                        (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                         >> 0x0000000dU)
                                                                         : 
                                                                        (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                         [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                         >> 0x0000000dU)) 
                                                                       << 1U)) 
                                                                   | (1U 
                                                                      & ((0x00001000U 
                                                                          & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                          ? 
                                                                         (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                          >> 0x0000000cU)
                                                                          : 
                                                                         (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                          [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                          >> 0x0000000cU)))) 
                                                                  << 4U)) 
                                                              | ((((2U 
                                                                    & (((0x00000800U 
                                                                         & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                         ? 
                                                                        (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                         >> 0x0000000bU)
                                                                         : 
                                                                        (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                         [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                         >> 0x0000000bU)) 
                                                                       << 1U)) 
                                                                   | (1U 
                                                                      & ((0x00000400U 
                                                                          & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                          ? 
                                                                         (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                          >> 0x0000000aU)
                                                                          : 
                                                                         (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                          [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                          >> 0x0000000aU)))) 
                                                                  << 2U) 
                                                                 | ((2U 
                                                                     & (((0x00000200U 
                                                                          & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                          ? 
                                                                         (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                          >> 9U)
                                                                          : 
                                                                         (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                          [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                          >> 9U)) 
                                                                        << 1U)) 
                                                                    | (1U 
                                                                       & ((0x00000100U 
                                                                           & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                           ? 
                                                                          (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                           >> 8U)
                                                                           : 
                                                                          (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                           [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                           >> 8U)))))) 
                                                             << 8U) 
                                                            | (((((2U 
                                                                   & (((0x00000080U 
                                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                        ? 
                                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                        >> 7U)
                                                                        : 
                                                                       (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                        >> 7U)) 
                                                                      << 1U)) 
                                                                  | (1U 
                                                                     & ((0x00000040U 
                                                                         & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                         ? 
                                                                        (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                         >> 6U)
                                                                         : 
                                                                        (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                         [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                         >> 6U)))) 
                                                                 << 6U) 
                                                                | (((2U 
                                                                     & (((0x00000020U 
                                                                          & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                          ? 
                                                                         (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                          >> 5U)
                                                                          : 
                                                                         (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                          [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                          >> 5U)) 
                                                                        << 1U)) 
                                                                    | (1U 
                                                                       & ((0x00000010U 
                                                                           & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                           ? 
                                                                          (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                           >> 4U)
                                                                           : 
                                                                          (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                           [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                           >> 4U)))) 
                                                                   << 4U)) 
                                                               | ((((2U 
                                                                     & (((8U 
                                                                          & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                          ? 
                                                                         (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                          >> 3U)
                                                                          : 
                                                                         (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                          [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                          >> 3U)) 
                                                                        << 1U)) 
                                                                    | (1U 
                                                                       & ((4U 
                                                                           & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                           ? 
                                                                          (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                           >> 2U)
                                                                           : 
                                                                          (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                           [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                           >> 2U)))) 
                                                                   << 2U) 
                                                                  | ((2U 
                                                                      & (((2U 
                                                                           & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                           ? 
                                                                          (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                           >> 1U)
                                                                           : 
                                                                          (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                           [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                           >> 1U)) 
                                                                         << 1U)) 
                                                                     | (1U 
                                                                        & ((1U 
                                                                            & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                            ? vlSelfRef.L1DCache__DOT__wr_data_w0[6U]
                                                                            : vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                           [vlSelfRef.L1DCache__DOT__data_rd_addr][6U])))))))))) 
                                     >> 0x00000020U));
            __Vtemp_2[0U] = ((((((((2U & (((vlSelfRef.L1DCache__DOT__ram_be_w0[4U] 
                                            >> 0x0000001fU)
                                            ? (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                               >> 0x0000001fU)
                                            : (vlSelfRef.L1DCache__DOT__data_ram_w0
                                               [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                               >> 0x0000001fU)) 
                                          << 1U)) | 
                                   (1U & ((0x40000000U 
                                           & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                           ? (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                              >> 0x0000001eU)
                                           : (vlSelfRef.L1DCache__DOT__data_ram_w0
                                              [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                              >> 0x0000001eU)))) 
                                  << 6U) | (((2U & 
                                              (((0x20000000U 
                                                 & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                                 ? 
                                                (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                                 >> 0x0000001dU)
                                                 : 
                                                (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                 [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                                 >> 0x0000001dU)) 
                                               << 1U)) 
                                             | (1U 
                                                & ((0x10000000U 
                                                    & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                                    ? 
                                                   (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                                    >> 0x0000001cU)
                                                    : 
                                                   (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                    [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                                    >> 0x0000001cU)))) 
                                            << 4U)) 
                                | ((((2U & (((0x08000000U 
                                              & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                              ? (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                                 >> 0x0000001bU)
                                              : (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                 [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                                 >> 0x0000001bU)) 
                                            << 1U)) 
                                     | (1U & ((0x04000000U 
                                               & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                               ? (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                                  >> 0x0000001aU)
                                               : (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                  [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                                  >> 0x0000001aU)))) 
                                    << 2U) | ((2U & 
                                               (((0x02000000U 
                                                  & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                                  ? 
                                                 (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                                  >> 0x00000019U)
                                                  : 
                                                 (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                  [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                                  >> 0x00000019U)) 
                                                << 1U)) 
                                              | (1U 
                                                 & ((0x01000000U 
                                                     & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                                     ? 
                                                    (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                                     >> 0x00000018U)
                                                     : 
                                                    (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                                     >> 0x00000018U)))))) 
                               << 0x00000018U) | ((
                                                   ((((2U 
                                                       & (((0x00800000U 
                                                            & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                                            ? 
                                                           (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                                            >> 0x00000017U)
                                                            : 
                                                           (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                            [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                                            >> 0x00000017U)) 
                                                          << 1U)) 
                                                      | (1U 
                                                         & ((0x00400000U 
                                                             & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                                             ? 
                                                            (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                                             >> 0x00000016U)
                                                             : 
                                                            (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                             [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                                             >> 0x00000016U)))) 
                                                     << 6U) 
                                                    | (((2U 
                                                         & (((0x00200000U 
                                                              & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                                              ? 
                                                             (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                                              >> 0x00000015U)
                                                              : 
                                                             (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                              [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                                              >> 0x00000015U)) 
                                                            << 1U)) 
                                                        | (1U 
                                                           & ((0x00100000U 
                                                               & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                                               ? 
                                                              (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                                               >> 0x00000014U)
                                                               : 
                                                              (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                               [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                                               >> 0x00000014U)))) 
                                                       << 4U)) 
                                                   | ((((2U 
                                                         & (((0x00080000U 
                                                              & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                                              ? 
                                                             (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                                              >> 0x00000013U)
                                                              : 
                                                             (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                              [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                                              >> 0x00000013U)) 
                                                            << 1U)) 
                                                        | (1U 
                                                           & ((0x00040000U 
                                                               & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                                               ? 
                                                              (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                                               >> 0x00000012U)
                                                               : 
                                                              (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                               [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                                               >> 0x00000012U)))) 
                                                       << 2U) 
                                                      | ((2U 
                                                          & (((0x00020000U 
                                                               & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                                               ? 
                                                              (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                                               >> 0x00000011U)
                                                               : 
                                                              (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                               [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                                               >> 0x00000011U)) 
                                                             << 1U)) 
                                                         | (1U 
                                                            & ((0x00010000U 
                                                                & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                                                ? 
                                                               (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                                                >> 0x00000010U)
                                                                : 
                                                               (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                                                >> 0x00000010U)))))) 
                                                  << 0x00000010U)) 
                             | (((((((2U & (((0x00008000U 
                                              & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                              ? (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                                 >> 0x0000000fU)
                                              : (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                 [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                                 >> 0x0000000fU)) 
                                            << 1U)) 
                                     | (1U & ((0x00004000U 
                                               & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                               ? (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                                  >> 0x0000000eU)
                                               : (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                  [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                                  >> 0x0000000eU)))) 
                                    << 6U) | (((2U 
                                                & (((0x00002000U 
                                                     & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                                     ? 
                                                    (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                                     >> 0x0000000dU)
                                                     : 
                                                    (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                                     >> 0x0000000dU)) 
                                                   << 1U)) 
                                               | (1U 
                                                  & ((0x00001000U 
                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                                      ? 
                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                                      >> 0x0000000cU)
                                                      : 
                                                     (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                                      >> 0x0000000cU)))) 
                                              << 4U)) 
                                  | ((((2U & (((0x00000800U 
                                                & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                                ? (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                                   >> 0x0000000bU)
                                                : (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                   [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                                   >> 0x0000000bU)) 
                                              << 1U)) 
                                       | (1U & ((0x00000400U 
                                                 & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                                 ? 
                                                (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                                 >> 0x0000000aU)
                                                 : 
                                                (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                 [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                                 >> 0x0000000aU)))) 
                                      << 2U) | ((2U 
                                                 & (((0x00000200U 
                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                                      ? 
                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                                      >> 9U)
                                                      : 
                                                     (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                                      >> 9U)) 
                                                    << 1U)) 
                                                | (1U 
                                                   & ((0x00000100U 
                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                                       ? 
                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                                       >> 8U)
                                                       : 
                                                      (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                                       >> 8U)))))) 
                                 << 8U) | (((((2U & 
                                               (((0x00000080U 
                                                  & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                                  ? 
                                                 (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                                  >> 7U)
                                                  : 
                                                 (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                  [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                                  >> 7U)) 
                                                << 1U)) 
                                              | (1U 
                                                 & ((0x00000040U 
                                                     & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                                     ? 
                                                    (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                                     >> 6U)
                                                     : 
                                                    (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                                     >> 6U)))) 
                                             << 6U) 
                                            | (((2U 
                                                 & (((0x00000020U 
                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                                      ? 
                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                                      >> 5U)
                                                      : 
                                                     (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                                      >> 5U)) 
                                                    << 1U)) 
                                                | (1U 
                                                   & ((0x00000010U 
                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                                       ? 
                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                                       >> 4U)
                                                       : 
                                                      (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                                       >> 4U)))) 
                                               << 4U)) 
                                           | ((((2U 
                                                 & (((8U 
                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                                      ? 
                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                                      >> 3U)
                                                      : 
                                                     (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                                      >> 3U)) 
                                                    << 1U)) 
                                                | (1U 
                                                   & ((4U 
                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                                       ? 
                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                                       >> 2U)
                                                       : 
                                                      (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                                       >> 2U)))) 
                                               << 2U) 
                                              | ((2U 
                                                  & (((2U 
                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                                       ? 
                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                                       >> 1U)
                                                       : 
                                                      (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                                       >> 1U)) 
                                                     << 1U)) 
                                                 | (1U 
                                                    & ((1U 
                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                                        ? vlSelfRef.L1DCache__DOT__wr_data_w0[4U]
                                                        : vlSelfRef.L1DCache__DOT__data_ram_w0
                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][4U])))))));
            __Vtemp_3[0U] = ((((((((2U & (((vlSelfRef.L1DCache__DOT__ram_be_w0[3U] 
                                            >> 0x0000001fU)
                                            ? (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                               >> 0x0000001fU)
                                            : (vlSelfRef.L1DCache__DOT__data_ram_w0
                                               [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                               >> 0x0000001fU)) 
                                          << 1U)) | 
                                   (1U & ((0x40000000U 
                                           & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                           ? (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                              >> 0x0000001eU)
                                           : (vlSelfRef.L1DCache__DOT__data_ram_w0
                                              [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                              >> 0x0000001eU)))) 
                                  << 6U) | (((2U & 
                                              (((0x20000000U 
                                                 & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                                 ? 
                                                (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                                 >> 0x0000001dU)
                                                 : 
                                                (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                 [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                                 >> 0x0000001dU)) 
                                               << 1U)) 
                                             | (1U 
                                                & ((0x10000000U 
                                                    & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                                    ? 
                                                   (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                                    >> 0x0000001cU)
                                                    : 
                                                   (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                    [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                                    >> 0x0000001cU)))) 
                                            << 4U)) 
                                | ((((2U & (((0x08000000U 
                                              & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                              ? (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                                 >> 0x0000001bU)
                                              : (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                 [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                                 >> 0x0000001bU)) 
                                            << 1U)) 
                                     | (1U & ((0x04000000U 
                                               & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                               ? (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                                  >> 0x0000001aU)
                                               : (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                  [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                                  >> 0x0000001aU)))) 
                                    << 2U) | ((2U & 
                                               (((0x02000000U 
                                                  & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                                  ? 
                                                 (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                                  >> 0x00000019U)
                                                  : 
                                                 (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                  [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                                  >> 0x00000019U)) 
                                                << 1U)) 
                                              | (1U 
                                                 & ((0x01000000U 
                                                     & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                                     ? 
                                                    (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                                     >> 0x00000018U)
                                                     : 
                                                    (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                                     >> 0x00000018U)))))) 
                               << 0x00000018U) | ((
                                                   ((((2U 
                                                       & (((0x00800000U 
                                                            & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                                            ? 
                                                           (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                                            >> 0x00000017U)
                                                            : 
                                                           (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                            [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                                            >> 0x00000017U)) 
                                                          << 1U)) 
                                                      | (1U 
                                                         & ((0x00400000U 
                                                             & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                                             ? 
                                                            (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                                             >> 0x00000016U)
                                                             : 
                                                            (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                             [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                                             >> 0x00000016U)))) 
                                                     << 6U) 
                                                    | (((2U 
                                                         & (((0x00200000U 
                                                              & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                                              ? 
                                                             (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                                              >> 0x00000015U)
                                                              : 
                                                             (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                              [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                                              >> 0x00000015U)) 
                                                            << 1U)) 
                                                        | (1U 
                                                           & ((0x00100000U 
                                                               & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                                               ? 
                                                              (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                                               >> 0x00000014U)
                                                               : 
                                                              (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                               [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                                               >> 0x00000014U)))) 
                                                       << 4U)) 
                                                   | ((((2U 
                                                         & (((0x00080000U 
                                                              & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                                              ? 
                                                             (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                                              >> 0x00000013U)
                                                              : 
                                                             (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                              [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                                              >> 0x00000013U)) 
                                                            << 1U)) 
                                                        | (1U 
                                                           & ((0x00040000U 
                                                               & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                                               ? 
                                                              (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                                               >> 0x00000012U)
                                                               : 
                                                              (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                               [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                                               >> 0x00000012U)))) 
                                                       << 2U) 
                                                      | ((2U 
                                                          & (((0x00020000U 
                                                               & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                                               ? 
                                                              (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                                               >> 0x00000011U)
                                                               : 
                                                              (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                               [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                                               >> 0x00000011U)) 
                                                             << 1U)) 
                                                         | (1U 
                                                            & ((0x00010000U 
                                                                & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                                                ? 
                                                               (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                                                >> 0x00000010U)
                                                                : 
                                                               (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                                                >> 0x00000010U)))))) 
                                                  << 0x00000010U)) 
                             | (((((((2U & (((0x00008000U 
                                              & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                              ? (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                                 >> 0x0000000fU)
                                              : (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                 [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                                 >> 0x0000000fU)) 
                                            << 1U)) 
                                     | (1U & ((0x00004000U 
                                               & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                               ? (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                                  >> 0x0000000eU)
                                               : (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                  [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                                  >> 0x0000000eU)))) 
                                    << 6U) | (((2U 
                                                & (((0x00002000U 
                                                     & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                                     ? 
                                                    (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                                     >> 0x0000000dU)
                                                     : 
                                                    (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                                     >> 0x0000000dU)) 
                                                   << 1U)) 
                                               | (1U 
                                                  & ((0x00001000U 
                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                                      ? 
                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                                      >> 0x0000000cU)
                                                      : 
                                                     (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                                      >> 0x0000000cU)))) 
                                              << 4U)) 
                                  | ((((2U & (((0x00000800U 
                                                & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                                ? (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                                   >> 0x0000000bU)
                                                : (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                   [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                                   >> 0x0000000bU)) 
                                              << 1U)) 
                                       | (1U & ((0x00000400U 
                                                 & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                                 ? 
                                                (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                                 >> 0x0000000aU)
                                                 : 
                                                (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                 [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                                 >> 0x0000000aU)))) 
                                      << 2U) | ((2U 
                                                 & (((0x00000200U 
                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                                      ? 
                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                                      >> 9U)
                                                      : 
                                                     (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                                      >> 9U)) 
                                                    << 1U)) 
                                                | (1U 
                                                   & ((0x00000100U 
                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                                       ? 
                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                                       >> 8U)
                                                       : 
                                                      (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                                       >> 8U)))))) 
                                 << 8U) | (((((2U & 
                                               (((0x00000080U 
                                                  & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                                  ? 
                                                 (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                                  >> 7U)
                                                  : 
                                                 (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                  [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                                  >> 7U)) 
                                                << 1U)) 
                                              | (1U 
                                                 & ((0x00000040U 
                                                     & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                                     ? 
                                                    (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                                     >> 6U)
                                                     : 
                                                    (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                                     >> 6U)))) 
                                             << 6U) 
                                            | (((2U 
                                                 & (((0x00000020U 
                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                                      ? 
                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                                      >> 5U)
                                                      : 
                                                     (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                                      >> 5U)) 
                                                    << 1U)) 
                                                | (1U 
                                                   & ((0x00000010U 
                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                                       ? 
                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                                       >> 4U)
                                                       : 
                                                      (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                                       >> 4U)))) 
                                               << 4U)) 
                                           | ((((2U 
                                                 & (((8U 
                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                                      ? 
                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                                      >> 3U)
                                                      : 
                                                     (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                                      >> 3U)) 
                                                    << 1U)) 
                                                | (1U 
                                                   & ((4U 
                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                                       ? 
                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                                       >> 2U)
                                                       : 
                                                      (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                                       >> 2U)))) 
                                               << 2U) 
                                              | ((2U 
                                                  & (((2U 
                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                                       ? 
                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                                       >> 1U)
                                                       : 
                                                      (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                                       >> 1U)) 
                                                     << 1U)) 
                                                 | (1U 
                                                    & ((1U 
                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                                        ? vlSelfRef.L1DCache__DOT__wr_data_w0[3U]
                                                        : vlSelfRef.L1DCache__DOT__data_ram_w0
                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][3U])))))));
            __Vtemp_4[0U] = ((((((((2U & (((vlSelfRef.L1DCache__DOT__ram_be_w0[2U] 
                                            >> 0x0000001fU)
                                            ? (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                               >> 0x0000001fU)
                                            : (vlSelfRef.L1DCache__DOT__data_ram_w0
                                               [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                               >> 0x0000001fU)) 
                                          << 1U)) | 
                                   (1U & ((0x40000000U 
                                           & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                           ? (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                              >> 0x0000001eU)
                                           : (vlSelfRef.L1DCache__DOT__data_ram_w0
                                              [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                              >> 0x0000001eU)))) 
                                  << 6U) | (((2U & 
                                              (((0x20000000U 
                                                 & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                                 ? 
                                                (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                                 >> 0x0000001dU)
                                                 : 
                                                (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                 [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                                 >> 0x0000001dU)) 
                                               << 1U)) 
                                             | (1U 
                                                & ((0x10000000U 
                                                    & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                                    ? 
                                                   (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                                    >> 0x0000001cU)
                                                    : 
                                                   (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                    [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                                    >> 0x0000001cU)))) 
                                            << 4U)) 
                                | ((((2U & (((0x08000000U 
                                              & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                              ? (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                                 >> 0x0000001bU)
                                              : (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                 [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                                 >> 0x0000001bU)) 
                                            << 1U)) 
                                     | (1U & ((0x04000000U 
                                               & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                               ? (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                                  >> 0x0000001aU)
                                               : (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                  [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                                  >> 0x0000001aU)))) 
                                    << 2U) | ((2U & 
                                               (((0x02000000U 
                                                  & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                                  ? 
                                                 (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                                  >> 0x00000019U)
                                                  : 
                                                 (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                  [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                                  >> 0x00000019U)) 
                                                << 1U)) 
                                              | (1U 
                                                 & ((0x01000000U 
                                                     & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                                     ? 
                                                    (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                                     >> 0x00000018U)
                                                     : 
                                                    (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                                     >> 0x00000018U)))))) 
                               << 0x00000018U) | ((
                                                   ((((2U 
                                                       & (((0x00800000U 
                                                            & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                                            ? 
                                                           (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                                            >> 0x00000017U)
                                                            : 
                                                           (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                            [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                                            >> 0x00000017U)) 
                                                          << 1U)) 
                                                      | (1U 
                                                         & ((0x00400000U 
                                                             & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                                             ? 
                                                            (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                                             >> 0x00000016U)
                                                             : 
                                                            (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                             [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                                             >> 0x00000016U)))) 
                                                     << 6U) 
                                                    | (((2U 
                                                         & (((0x00200000U 
                                                              & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                                              ? 
                                                             (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                                              >> 0x00000015U)
                                                              : 
                                                             (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                              [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                                              >> 0x00000015U)) 
                                                            << 1U)) 
                                                        | (1U 
                                                           & ((0x00100000U 
                                                               & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                                               ? 
                                                              (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                                               >> 0x00000014U)
                                                               : 
                                                              (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                               [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                                               >> 0x00000014U)))) 
                                                       << 4U)) 
                                                   | ((((2U 
                                                         & (((0x00080000U 
                                                              & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                                              ? 
                                                             (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                                              >> 0x00000013U)
                                                              : 
                                                             (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                              [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                                              >> 0x00000013U)) 
                                                            << 1U)) 
                                                        | (1U 
                                                           & ((0x00040000U 
                                                               & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                                               ? 
                                                              (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                                               >> 0x00000012U)
                                                               : 
                                                              (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                               [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                                               >> 0x00000012U)))) 
                                                       << 2U) 
                                                      | ((2U 
                                                          & (((0x00020000U 
                                                               & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                                               ? 
                                                              (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                                               >> 0x00000011U)
                                                               : 
                                                              (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                               [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                                               >> 0x00000011U)) 
                                                             << 1U)) 
                                                         | (1U 
                                                            & ((0x00010000U 
                                                                & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                                                ? 
                                                               (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                                                >> 0x00000010U)
                                                                : 
                                                               (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                                                >> 0x00000010U)))))) 
                                                  << 0x00000010U)) 
                             | (((((((2U & (((0x00008000U 
                                              & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                              ? (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                                 >> 0x0000000fU)
                                              : (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                 [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                                 >> 0x0000000fU)) 
                                            << 1U)) 
                                     | (1U & ((0x00004000U 
                                               & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                               ? (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                                  >> 0x0000000eU)
                                               : (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                  [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                                  >> 0x0000000eU)))) 
                                    << 6U) | (((2U 
                                                & (((0x00002000U 
                                                     & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                                     ? 
                                                    (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                                     >> 0x0000000dU)
                                                     : 
                                                    (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                                     >> 0x0000000dU)) 
                                                   << 1U)) 
                                               | (1U 
                                                  & ((0x00001000U 
                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                                      ? 
                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                                      >> 0x0000000cU)
                                                      : 
                                                     (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                                      >> 0x0000000cU)))) 
                                              << 4U)) 
                                  | ((((2U & (((0x00000800U 
                                                & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                                ? (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                                   >> 0x0000000bU)
                                                : (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                   [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                                   >> 0x0000000bU)) 
                                              << 1U)) 
                                       | (1U & ((0x00000400U 
                                                 & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                                 ? 
                                                (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                                 >> 0x0000000aU)
                                                 : 
                                                (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                 [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                                 >> 0x0000000aU)))) 
                                      << 2U) | ((2U 
                                                 & (((0x00000200U 
                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                                      ? 
                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                                      >> 9U)
                                                      : 
                                                     (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                                      >> 9U)) 
                                                    << 1U)) 
                                                | (1U 
                                                   & ((0x00000100U 
                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                                       ? 
                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                                       >> 8U)
                                                       : 
                                                      (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                                       >> 8U)))))) 
                                 << 8U) | (((((2U & 
                                               (((0x00000080U 
                                                  & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                                  ? 
                                                 (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                                  >> 7U)
                                                  : 
                                                 (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                  [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                                  >> 7U)) 
                                                << 1U)) 
                                              | (1U 
                                                 & ((0x00000040U 
                                                     & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                                     ? 
                                                    (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                                     >> 6U)
                                                     : 
                                                    (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                                     >> 6U)))) 
                                             << 6U) 
                                            | (((2U 
                                                 & (((0x00000020U 
                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                                      ? 
                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                                      >> 5U)
                                                      : 
                                                     (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                                      >> 5U)) 
                                                    << 1U)) 
                                                | (1U 
                                                   & ((0x00000010U 
                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                                       ? 
                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                                       >> 4U)
                                                       : 
                                                      (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                                       >> 4U)))) 
                                               << 4U)) 
                                           | ((((2U 
                                                 & (((8U 
                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                                      ? 
                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                                      >> 3U)
                                                      : 
                                                     (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                                      >> 3U)) 
                                                    << 1U)) 
                                                | (1U 
                                                   & ((4U 
                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                                       ? 
                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                                       >> 2U)
                                                       : 
                                                      (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                                       >> 2U)))) 
                                               << 2U) 
                                              | ((2U 
                                                  & (((2U 
                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                                       ? 
                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                                       >> 1U)
                                                       : 
                                                      (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                                       >> 1U)) 
                                                     << 1U)) 
                                                 | (1U 
                                                    & ((1U 
                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                                        ? vlSelfRef.L1DCache__DOT__wr_data_w0[2U]
                                                        : vlSelfRef.L1DCache__DOT__data_ram_w0
                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][2U])))))));
            __Vtemp_5[0U] = ((((((((2U & (((vlSelfRef.L1DCache__DOT__ram_be_w0[1U] 
                                            >> 0x0000001fU)
                                            ? (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                               >> 0x0000001fU)
                                            : (vlSelfRef.L1DCache__DOT__data_ram_w0
                                               [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                               >> 0x0000001fU)) 
                                          << 1U)) | 
                                   (1U & ((0x40000000U 
                                           & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                           ? (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                              >> 0x0000001eU)
                                           : (vlSelfRef.L1DCache__DOT__data_ram_w0
                                              [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                              >> 0x0000001eU)))) 
                                  << 6U) | (((2U & 
                                              (((0x20000000U 
                                                 & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                                 ? 
                                                (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                 >> 0x0000001dU)
                                                 : 
                                                (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                 [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                 >> 0x0000001dU)) 
                                               << 1U)) 
                                             | (1U 
                                                & ((0x10000000U 
                                                    & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                                    ? 
                                                   (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                    >> 0x0000001cU)
                                                    : 
                                                   (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                    [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                    >> 0x0000001cU)))) 
                                            << 4U)) 
                                | ((((2U & (((0x08000000U 
                                              & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                              ? (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                 >> 0x0000001bU)
                                              : (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                 [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                 >> 0x0000001bU)) 
                                            << 1U)) 
                                     | (1U & ((0x04000000U 
                                               & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                               ? (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                  >> 0x0000001aU)
                                               : (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                  [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                  >> 0x0000001aU)))) 
                                    << 2U) | ((2U & 
                                               (((0x02000000U 
                                                  & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                                  ? 
                                                 (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                  >> 0x00000019U)
                                                  : 
                                                 (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                  [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                  >> 0x00000019U)) 
                                                << 1U)) 
                                              | (1U 
                                                 & ((0x01000000U 
                                                     & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                                     ? 
                                                    (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                     >> 0x00000018U)
                                                     : 
                                                    (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                     >> 0x00000018U)))))) 
                               << 0x00000018U) | ((
                                                   ((((2U 
                                                       & (((0x00800000U 
                                                            & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                                            ? 
                                                           (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                            >> 0x00000017U)
                                                            : 
                                                           (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                            [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                            >> 0x00000017U)) 
                                                          << 1U)) 
                                                      | (1U 
                                                         & ((0x00400000U 
                                                             & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                                             ? 
                                                            (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                             >> 0x00000016U)
                                                             : 
                                                            (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                             [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                             >> 0x00000016U)))) 
                                                     << 6U) 
                                                    | (((2U 
                                                         & (((0x00200000U 
                                                              & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                                              ? 
                                                             (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                              >> 0x00000015U)
                                                              : 
                                                             (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                              [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                              >> 0x00000015U)) 
                                                            << 1U)) 
                                                        | (1U 
                                                           & ((0x00100000U 
                                                               & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                                               ? 
                                                              (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                               >> 0x00000014U)
                                                               : 
                                                              (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                               [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                               >> 0x00000014U)))) 
                                                       << 4U)) 
                                                   | ((((2U 
                                                         & (((0x00080000U 
                                                              & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                                              ? 
                                                             (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                              >> 0x00000013U)
                                                              : 
                                                             (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                              [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                              >> 0x00000013U)) 
                                                            << 1U)) 
                                                        | (1U 
                                                           & ((0x00040000U 
                                                               & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                                               ? 
                                                              (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                               >> 0x00000012U)
                                                               : 
                                                              (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                               [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                               >> 0x00000012U)))) 
                                                       << 2U) 
                                                      | ((2U 
                                                          & (((0x00020000U 
                                                               & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                                               ? 
                                                              (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                               >> 0x00000011U)
                                                               : 
                                                              (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                               [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                               >> 0x00000011U)) 
                                                             << 1U)) 
                                                         | (1U 
                                                            & ((0x00010000U 
                                                                & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                                                ? 
                                                               (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                                >> 0x00000010U)
                                                                : 
                                                               (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                                [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                                >> 0x00000010U)))))) 
                                                  << 0x00000010U)) 
                             | (((((((2U & (((0x00008000U 
                                              & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                              ? (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                 >> 0x0000000fU)
                                              : (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                 [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                 >> 0x0000000fU)) 
                                            << 1U)) 
                                     | (1U & ((0x00004000U 
                                               & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                               ? (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                  >> 0x0000000eU)
                                               : (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                  [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                  >> 0x0000000eU)))) 
                                    << 6U) | (((2U 
                                                & (((0x00002000U 
                                                     & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                                     ? 
                                                    (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                     >> 0x0000000dU)
                                                     : 
                                                    (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                     >> 0x0000000dU)) 
                                                   << 1U)) 
                                               | (1U 
                                                  & ((0x00001000U 
                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                                      ? 
                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                      >> 0x0000000cU)
                                                      : 
                                                     (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                      >> 0x0000000cU)))) 
                                              << 4U)) 
                                  | ((((2U & (((0x00000800U 
                                                & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                                ? (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                   >> 0x0000000bU)
                                                : (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                   [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                   >> 0x0000000bU)) 
                                              << 1U)) 
                                       | (1U & ((0x00000400U 
                                                 & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                                 ? 
                                                (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                 >> 0x0000000aU)
                                                 : 
                                                (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                 [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                 >> 0x0000000aU)))) 
                                      << 2U) | ((2U 
                                                 & (((0x00000200U 
                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                                      ? 
                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                      >> 9U)
                                                      : 
                                                     (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                      >> 9U)) 
                                                    << 1U)) 
                                                | (1U 
                                                   & ((0x00000100U 
                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                                       ? 
                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                       >> 8U)
                                                       : 
                                                      (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                       >> 8U)))))) 
                                 << 8U) | (((((2U & 
                                               (((0x00000080U 
                                                  & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                                  ? 
                                                 (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                  >> 7U)
                                                  : 
                                                 (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                  [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                  >> 7U)) 
                                                << 1U)) 
                                              | (1U 
                                                 & ((0x00000040U 
                                                     & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                                     ? 
                                                    (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                     >> 6U)
                                                     : 
                                                    (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                     >> 6U)))) 
                                             << 6U) 
                                            | (((2U 
                                                 & (((0x00000020U 
                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                                      ? 
                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                      >> 5U)
                                                      : 
                                                     (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                      >> 5U)) 
                                                    << 1U)) 
                                                | (1U 
                                                   & ((0x00000010U 
                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                                       ? 
                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                       >> 4U)
                                                       : 
                                                      (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                       >> 4U)))) 
                                               << 4U)) 
                                           | ((((2U 
                                                 & (((8U 
                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                                      ? 
                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                      >> 3U)
                                                      : 
                                                     (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                      >> 3U)) 
                                                    << 1U)) 
                                                | (1U 
                                                   & ((4U 
                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                                       ? 
                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                       >> 2U)
                                                       : 
                                                      (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                       >> 2U)))) 
                                               << 2U) 
                                              | ((2U 
                                                  & (((2U 
                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                                       ? 
                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                       >> 1U)
                                                       : 
                                                      (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                       >> 1U)) 
                                                     << 1U)) 
                                                 | (1U 
                                                    & ((1U 
                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                                        ? vlSelfRef.L1DCache__DOT__wr_data_w0[1U]
                                                        : vlSelfRef.L1DCache__DOT__data_ram_w0
                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][1U])))))));
            __VdlyVal__L1DCache__DOT__data_ram_w0__v0[0U] 
                = ((((((((2U & (((vlSelfRef.L1DCache__DOT__ram_be_w0[0U] 
                                  >> 0x0000001fU) ? 
                                 (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                  >> 0x0000001fU) : 
                                 (vlSelfRef.L1DCache__DOT__data_ram_w0
                                  [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                  >> 0x0000001fU)) 
                                << 1U)) | (1U & ((0x40000000U 
                                                  & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                                  ? 
                                                 (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                                  >> 0x0000001eU)
                                                  : 
                                                 (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                  [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                                  >> 0x0000001eU)))) 
                        << 6U) | (((2U & (((0x20000000U 
                                            & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                            ? (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                               >> 0x0000001dU)
                                            : (vlSelfRef.L1DCache__DOT__data_ram_w0
                                               [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                               >> 0x0000001dU)) 
                                          << 1U)) | 
                                   (1U & ((0x10000000U 
                                           & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                           ? (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                              >> 0x0000001cU)
                                           : (vlSelfRef.L1DCache__DOT__data_ram_w0
                                              [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                              >> 0x0000001cU)))) 
                                  << 4U)) | ((((2U 
                                                & (((0x08000000U 
                                                     & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                                     ? 
                                                    (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                                     >> 0x0000001bU)
                                                     : 
                                                    (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                                     >> 0x0000001bU)) 
                                                   << 1U)) 
                                               | (1U 
                                                  & ((0x04000000U 
                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                                      ? 
                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                                      >> 0x0000001aU)
                                                      : 
                                                     (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                                      >> 0x0000001aU)))) 
                                              << 2U) 
                                             | ((2U 
                                                 & (((0x02000000U 
                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                                      ? 
                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                                      >> 0x00000019U)
                                                      : 
                                                     (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                                      >> 0x00000019U)) 
                                                    << 1U)) 
                                                | (1U 
                                                   & ((0x01000000U 
                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                                       ? 
                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                                       >> 0x00000018U)
                                                       : 
                                                      (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                                       >> 0x00000018U)))))) 
                     << 0x00000018U) | ((((((2U & (
                                                   ((0x00800000U 
                                                     & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                                     ? 
                                                    (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                                     >> 0x00000017U)
                                                     : 
                                                    (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                                     >> 0x00000017U)) 
                                                   << 1U)) 
                                            | (1U & 
                                               ((0x00400000U 
                                                 & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                                 ? 
                                                (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                                 >> 0x00000016U)
                                                 : 
                                                (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                 [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                                 >> 0x00000016U)))) 
                                           << 6U) | 
                                          (((2U & (
                                                   ((0x00200000U 
                                                     & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                                     ? 
                                                    (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                                     >> 0x00000015U)
                                                     : 
                                                    (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                                     >> 0x00000015U)) 
                                                   << 1U)) 
                                            | (1U & 
                                               ((0x00100000U 
                                                 & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                                 ? 
                                                (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                                 >> 0x00000014U)
                                                 : 
                                                (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                 [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                                 >> 0x00000014U)))) 
                                           << 4U)) 
                                         | ((((2U & 
                                               (((0x00080000U 
                                                  & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                                  ? 
                                                 (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                                  >> 0x00000013U)
                                                  : 
                                                 (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                  [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                                  >> 0x00000013U)) 
                                                << 1U)) 
                                              | (1U 
                                                 & ((0x00040000U 
                                                     & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                                     ? 
                                                    (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                                     >> 0x00000012U)
                                                     : 
                                                    (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                                     >> 0x00000012U)))) 
                                             << 2U) 
                                            | ((2U 
                                                & (((0x00020000U 
                                                     & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                                     ? 
                                                    (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                                     >> 0x00000011U)
                                                     : 
                                                    (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                                     >> 0x00000011U)) 
                                                   << 1U)) 
                                               | (1U 
                                                  & ((0x00010000U 
                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                                      ? 
                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                                      >> 0x00000010U)
                                                      : 
                                                     (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                                      >> 0x00000010U)))))) 
                                        << 0x00000010U)) 
                   | (((((((2U & (((0x00008000U & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                    ? (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                       >> 0x0000000fU)
                                    : (vlSelfRef.L1DCache__DOT__data_ram_w0
                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                       >> 0x0000000fU)) 
                                  << 1U)) | (1U & (
                                                   (0x00004000U 
                                                    & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                                    ? 
                                                   (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                                    >> 0x0000000eU)
                                                    : 
                                                   (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                    [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                                    >> 0x0000000eU)))) 
                          << 6U) | (((2U & (((0x00002000U 
                                              & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                              ? (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                                 >> 0x0000000dU)
                                              : (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                 [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                                 >> 0x0000000dU)) 
                                            << 1U)) 
                                     | (1U & ((0x00001000U 
                                               & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                               ? (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                                  >> 0x0000000cU)
                                               : (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                  [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                                  >> 0x0000000cU)))) 
                                    << 4U)) | ((((2U 
                                                  & (((0x00000800U 
                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                                       ? 
                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                                       >> 0x0000000bU)
                                                       : 
                                                      (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                                       >> 0x0000000bU)) 
                                                     << 1U)) 
                                                 | (1U 
                                                    & ((0x00000400U 
                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                                        ? 
                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                                        >> 0x0000000aU)
                                                        : 
                                                       (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                                        >> 0x0000000aU)))) 
                                                << 2U) 
                                               | ((2U 
                                                   & (((0x00000200U 
                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                                        ? 
                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                                        >> 9U)
                                                        : 
                                                       (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                                        >> 9U)) 
                                                      << 1U)) 
                                                  | (1U 
                                                     & ((0x00000100U 
                                                         & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                                         ? 
                                                        (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                                         >> 8U)
                                                         : 
                                                        (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                         [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                                         >> 8U)))))) 
                       << 8U) | (((((2U & (((0x00000080U 
                                             & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                             ? (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                                >> 7U)
                                             : (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                                >> 7U)) 
                                           << 1U)) 
                                    | (1U & ((0x00000040U 
                                              & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                              ? (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                                 >> 6U)
                                              : (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                 [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                                 >> 6U)))) 
                                   << 6U) | (((2U & 
                                               (((0x00000020U 
                                                  & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                                  ? 
                                                 (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                                  >> 5U)
                                                  : 
                                                 (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                  [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                                  >> 5U)) 
                                                << 1U)) 
                                              | (1U 
                                                 & ((0x00000010U 
                                                     & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                                     ? 
                                                    (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                                     >> 4U)
                                                     : 
                                                    (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                                     >> 4U)))) 
                                             << 4U)) 
                                 | ((((2U & (((8U & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                               ? (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                                  >> 3U)
                                               : (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                  [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                                  >> 3U)) 
                                             << 1U)) 
                                      | (1U & ((4U 
                                                & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                                ? (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                                   >> 2U)
                                                : (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                   [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                                   >> 2U)))) 
                                     << 2U) | ((2U 
                                                & (((2U 
                                                     & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                                     ? 
                                                    (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                                     >> 1U)
                                                     : 
                                                    (vlSelfRef.L1DCache__DOT__data_ram_w0
                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                                     >> 1U)) 
                                                   << 1U)) 
                                               | (1U 
                                                  & ((1U 
                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                                      ? vlSelfRef.L1DCache__DOT__wr_data_w0[0U]
                                                      : vlSelfRef.L1DCache__DOT__data_ram_w0
                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][0U])))))));
            __VdlyVal__L1DCache__DOT__data_ram_w0__v0[1U] 
                = __Vtemp_5[0U];
            __VdlyVal__L1DCache__DOT__data_ram_w0__v0[2U] 
                = __Vtemp_4[0U];
            __VdlyVal__L1DCache__DOT__data_ram_w0__v0[3U] 
                = __Vtemp_3[0U];
            __VdlyVal__L1DCache__DOT__data_ram_w0__v0[4U] 
                = __Vtemp_2[0U];
            __VdlyVal__L1DCache__DOT__data_ram_w0__v0[5U] 
                = __Vtemp_1[0U];
            __VdlyVal__L1DCache__DOT__data_ram_w0__v0[6U] 
                = __Vtemp_1[1U];
            __VdlyVal__L1DCache__DOT__data_ram_w0__v0[7U] 
                = __Vtemp_1[2U];
        }
        __VdlyDim0__L1DCache__DOT__data_ram_w0__v0 
            = vlSelfRef.L1DCache__DOT__data_wr_addr_w0;
        __VdlySet__L1DCache__DOT__data_ram_w0__v0 = 1U;
    }
    if ((((IData)(vlSelfRef.L1DCache__DOT__write_hit) 
          & (IData)(vlSelfRef.L1DCache__DOT__way1_hit)) 
         | ((IData)(vlSelfRef.L1DCache__DOT__pend_victim_q_reg) 
            & (IData)(vlSelfRef.L1DCache__DOT__refill_done)))) {
        if (vlSelfRef.L1DCache__DOT__refill_done) {
            __VdlyVal__L1DCache__DOT__data_ram_w1__v0[0U] 
                = vlSelfRef.refill_data[0U];
            __VdlyVal__L1DCache__DOT__data_ram_w1__v0[1U] 
                = vlSelfRef.refill_data[1U];
            __VdlyVal__L1DCache__DOT__data_ram_w1__v0[2U] 
                = vlSelfRef.refill_data[2U];
            __VdlyVal__L1DCache__DOT__data_ram_w1__v0[3U] 
                = vlSelfRef.refill_data[3U];
            __VdlyVal__L1DCache__DOT__data_ram_w1__v0[4U] 
                = vlSelfRef.refill_data[4U];
            __VdlyVal__L1DCache__DOT__data_ram_w1__v0[5U] 
                = vlSelfRef.refill_data[5U];
            __VdlyVal__L1DCache__DOT__data_ram_w1__v0[6U] 
                = vlSelfRef.refill_data[6U];
            __VdlyVal__L1DCache__DOT__data_ram_w1__v0[7U] 
                = vlSelfRef.refill_data[7U];
        } else {
            __Vtemp_6[0U] = ((((((((2U & (((vlSelfRef.L1DCache__DOT__ram_be_w0[5U] 
                                            >> 0x0000001fU)
                                            ? (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                               >> 0x0000001fU)
                                            : (vlSelfRef.L1DCache__DOT__data_ram_w1
                                               [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                               >> 0x0000001fU)) 
                                          << 1U)) | 
                                   (1U & ((0x40000000U 
                                           & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                           ? (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                              >> 0x0000001eU)
                                           : (vlSelfRef.L1DCache__DOT__data_ram_w1
                                              [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                              >> 0x0000001eU)))) 
                                  << 6U) | (((2U & 
                                              (((0x20000000U 
                                                 & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                                 ? 
                                                (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                                 >> 0x0000001dU)
                                                 : 
                                                (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                 [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                                 >> 0x0000001dU)) 
                                               << 1U)) 
                                             | (1U 
                                                & ((0x10000000U 
                                                    & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                                    ? 
                                                   (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                                    >> 0x0000001cU)
                                                    : 
                                                   (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                    [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                                    >> 0x0000001cU)))) 
                                            << 4U)) 
                                | ((((2U & (((0x08000000U 
                                              & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                              ? (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                                 >> 0x0000001bU)
                                              : (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                 [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                                 >> 0x0000001bU)) 
                                            << 1U)) 
                                     | (1U & ((0x04000000U 
                                               & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                               ? (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                                  >> 0x0000001aU)
                                               : (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                  [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                                  >> 0x0000001aU)))) 
                                    << 2U) | ((2U & 
                                               (((0x02000000U 
                                                  & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                                  ? 
                                                 (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                                  >> 0x00000019U)
                                                  : 
                                                 (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                  [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                                  >> 0x00000019U)) 
                                                << 1U)) 
                                              | (1U 
                                                 & ((0x01000000U 
                                                     & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                                     ? 
                                                    (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                                     >> 0x00000018U)
                                                     : 
                                                    (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                                     >> 0x00000018U)))))) 
                               << 0x00000018U) | ((
                                                   ((((2U 
                                                       & (((0x00800000U 
                                                            & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                                            ? 
                                                           (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                                            >> 0x00000017U)
                                                            : 
                                                           (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                            [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                                            >> 0x00000017U)) 
                                                          << 1U)) 
                                                      | (1U 
                                                         & ((0x00400000U 
                                                             & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                                             ? 
                                                            (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                                             >> 0x00000016U)
                                                             : 
                                                            (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                             [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                                             >> 0x00000016U)))) 
                                                     << 6U) 
                                                    | (((2U 
                                                         & (((0x00200000U 
                                                              & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                                              ? 
                                                             (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                                              >> 0x00000015U)
                                                              : 
                                                             (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                              [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                                              >> 0x00000015U)) 
                                                            << 1U)) 
                                                        | (1U 
                                                           & ((0x00100000U 
                                                               & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                                               ? 
                                                              (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                                               >> 0x00000014U)
                                                               : 
                                                              (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                               [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                                               >> 0x00000014U)))) 
                                                       << 4U)) 
                                                   | ((((2U 
                                                         & (((0x00080000U 
                                                              & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                                              ? 
                                                             (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                                              >> 0x00000013U)
                                                              : 
                                                             (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                              [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                                              >> 0x00000013U)) 
                                                            << 1U)) 
                                                        | (1U 
                                                           & ((0x00040000U 
                                                               & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                                               ? 
                                                              (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                                               >> 0x00000012U)
                                                               : 
                                                              (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                               [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                                               >> 0x00000012U)))) 
                                                       << 2U) 
                                                      | ((2U 
                                                          & (((0x00020000U 
                                                               & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                                               ? 
                                                              (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                                               >> 0x00000011U)
                                                               : 
                                                              (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                               [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                                               >> 0x00000011U)) 
                                                             << 1U)) 
                                                         | (1U 
                                                            & ((0x00010000U 
                                                                & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                                                ? 
                                                               (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                                                >> 0x00000010U)
                                                                : 
                                                               (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                                                >> 0x00000010U)))))) 
                                                  << 0x00000010U)) 
                             | (((((((2U & (((0x00008000U 
                                              & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                              ? (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                                 >> 0x0000000fU)
                                              : (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                 [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                                 >> 0x0000000fU)) 
                                            << 1U)) 
                                     | (1U & ((0x00004000U 
                                               & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                               ? (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                                  >> 0x0000000eU)
                                               : (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                  [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                                  >> 0x0000000eU)))) 
                                    << 6U) | (((2U 
                                                & (((0x00002000U 
                                                     & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                                     ? 
                                                    (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                                     >> 0x0000000dU)
                                                     : 
                                                    (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                                     >> 0x0000000dU)) 
                                                   << 1U)) 
                                               | (1U 
                                                  & ((0x00001000U 
                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                                      ? 
                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                                      >> 0x0000000cU)
                                                      : 
                                                     (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                                      >> 0x0000000cU)))) 
                                              << 4U)) 
                                  | ((((2U & (((0x00000800U 
                                                & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                                ? (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                                   >> 0x0000000bU)
                                                : (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                   [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                                   >> 0x0000000bU)) 
                                              << 1U)) 
                                       | (1U & ((0x00000400U 
                                                 & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                                 ? 
                                                (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                                 >> 0x0000000aU)
                                                 : 
                                                (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                 [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                                 >> 0x0000000aU)))) 
                                      << 2U) | ((2U 
                                                 & (((0x00000200U 
                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                                      ? 
                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                                      >> 9U)
                                                      : 
                                                     (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                                      >> 9U)) 
                                                    << 1U)) 
                                                | (1U 
                                                   & ((0x00000100U 
                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                                       ? 
                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                                       >> 8U)
                                                       : 
                                                      (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                                       >> 8U)))))) 
                                 << 8U) | (((((2U & 
                                               (((0x00000080U 
                                                  & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                                  ? 
                                                 (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                                  >> 7U)
                                                  : 
                                                 (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                  [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                                  >> 7U)) 
                                                << 1U)) 
                                              | (1U 
                                                 & ((0x00000040U 
                                                     & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                                     ? 
                                                    (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                                     >> 6U)
                                                     : 
                                                    (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                                     >> 6U)))) 
                                             << 6U) 
                                            | (((2U 
                                                 & (((0x00000020U 
                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                                      ? 
                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                                      >> 5U)
                                                      : 
                                                     (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                                      >> 5U)) 
                                                    << 1U)) 
                                                | (1U 
                                                   & ((0x00000010U 
                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                                       ? 
                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                                       >> 4U)
                                                       : 
                                                      (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                                       >> 4U)))) 
                                               << 4U)) 
                                           | ((((2U 
                                                 & (((8U 
                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                                      ? 
                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                                      >> 3U)
                                                      : 
                                                     (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                                      >> 3U)) 
                                                    << 1U)) 
                                                | (1U 
                                                   & ((4U 
                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                                       ? 
                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                                       >> 2U)
                                                       : 
                                                      (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                                       >> 2U)))) 
                                               << 2U) 
                                              | ((2U 
                                                  & (((2U 
                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                                       ? 
                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[5U] 
                                                       >> 1U)
                                                       : 
                                                      (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][5U] 
                                                       >> 1U)) 
                                                     << 1U)) 
                                                 | (1U 
                                                    & ((1U 
                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[5U])
                                                        ? vlSelfRef.L1DCache__DOT__wr_data_w0[5U]
                                                        : vlSelfRef.L1DCache__DOT__data_ram_w1
                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][5U])))))));
            __Vtemp_6[1U] = (IData)((((QData)((IData)(
                                                      ((((((((2U 
                                                              & (((vlSelfRef.L1DCache__DOT__ram_be_w0[7U] 
                                                                   >> 0x0000001fU)
                                                                   ? 
                                                                  (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                   >> 0x0000001fU)
                                                                   : 
                                                                  (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                   [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                   >> 0x0000001fU)) 
                                                                 << 1U)) 
                                                             | (1U 
                                                                & ((0x40000000U 
                                                                    & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                    ? 
                                                                   (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                    >> 0x0000001eU)
                                                                    : 
                                                                   (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                    [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                    >> 0x0000001eU)))) 
                                                            << 6U) 
                                                           | (((2U 
                                                                & (((0x20000000U 
                                                                     & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                     ? 
                                                                    (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                     >> 0x0000001dU)
                                                                     : 
                                                                    (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                     >> 0x0000001dU)) 
                                                                   << 1U)) 
                                                               | (1U 
                                                                  & ((0x10000000U 
                                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                      ? 
                                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                      >> 0x0000001cU)
                                                                      : 
                                                                     (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                      >> 0x0000001cU)))) 
                                                              << 4U)) 
                                                          | ((((2U 
                                                                & (((0x08000000U 
                                                                     & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                     ? 
                                                                    (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                     >> 0x0000001bU)
                                                                     : 
                                                                    (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                     >> 0x0000001bU)) 
                                                                   << 1U)) 
                                                               | (1U 
                                                                  & ((0x04000000U 
                                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                      ? 
                                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                      >> 0x0000001aU)
                                                                      : 
                                                                     (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                      >> 0x0000001aU)))) 
                                                              << 2U) 
                                                             | ((2U 
                                                                 & (((0x02000000U 
                                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                      ? 
                                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                      >> 0x00000019U)
                                                                      : 
                                                                     (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                      >> 0x00000019U)) 
                                                                    << 1U)) 
                                                                | (1U 
                                                                   & ((0x01000000U 
                                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                       ? 
                                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                       >> 0x00000018U)
                                                                       : 
                                                                      (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                       >> 0x00000018U)))))) 
                                                         << 0x00000018U) 
                                                        | ((((((2U 
                                                                & (((0x00800000U 
                                                                     & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                     ? 
                                                                    (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                     >> 0x00000017U)
                                                                     : 
                                                                    (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                     >> 0x00000017U)) 
                                                                   << 1U)) 
                                                               | (1U 
                                                                  & ((0x00400000U 
                                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                      ? 
                                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                      >> 0x00000016U)
                                                                      : 
                                                                     (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                      >> 0x00000016U)))) 
                                                              << 6U) 
                                                             | (((2U 
                                                                  & (((0x00200000U 
                                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                       ? 
                                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                       >> 0x00000015U)
                                                                       : 
                                                                      (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                       >> 0x00000015U)) 
                                                                     << 1U)) 
                                                                 | (1U 
                                                                    & ((0x00100000U 
                                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                        ? 
                                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                        >> 0x00000014U)
                                                                        : 
                                                                       (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                        >> 0x00000014U)))) 
                                                                << 4U)) 
                                                            | ((((2U 
                                                                  & (((0x00080000U 
                                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                       ? 
                                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                       >> 0x00000013U)
                                                                       : 
                                                                      (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                       >> 0x00000013U)) 
                                                                     << 1U)) 
                                                                 | (1U 
                                                                    & ((0x00040000U 
                                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                        ? 
                                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                        >> 0x00000012U)
                                                                        : 
                                                                       (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                        >> 0x00000012U)))) 
                                                                << 2U) 
                                                               | ((2U 
                                                                   & (((0x00020000U 
                                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                        ? 
                                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                        >> 0x00000011U)
                                                                        : 
                                                                       (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                        >> 0x00000011U)) 
                                                                      << 1U)) 
                                                                  | (1U 
                                                                     & ((0x00010000U 
                                                                         & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                         ? 
                                                                        (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                         >> 0x00000010U)
                                                                         : 
                                                                        (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                         [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                         >> 0x00000010U)))))) 
                                                           << 0x00000010U)) 
                                                       | (((((((2U 
                                                                & (((0x00008000U 
                                                                     & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                     ? 
                                                                    (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                     >> 0x0000000fU)
                                                                     : 
                                                                    (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                     >> 0x0000000fU)) 
                                                                   << 1U)) 
                                                               | (1U 
                                                                  & ((0x00004000U 
                                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                      ? 
                                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                      >> 0x0000000eU)
                                                                      : 
                                                                     (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                      >> 0x0000000eU)))) 
                                                              << 6U) 
                                                             | (((2U 
                                                                  & (((0x00002000U 
                                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                       ? 
                                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                       >> 0x0000000dU)
                                                                       : 
                                                                      (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                       >> 0x0000000dU)) 
                                                                     << 1U)) 
                                                                 | (1U 
                                                                    & ((0x00001000U 
                                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                        ? 
                                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                        >> 0x0000000cU)
                                                                        : 
                                                                       (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                        >> 0x0000000cU)))) 
                                                                << 4U)) 
                                                            | ((((2U 
                                                                  & (((0x00000800U 
                                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                       ? 
                                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                       >> 0x0000000bU)
                                                                       : 
                                                                      (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                       >> 0x0000000bU)) 
                                                                     << 1U)) 
                                                                 | (1U 
                                                                    & ((0x00000400U 
                                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                        ? 
                                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                        >> 0x0000000aU)
                                                                        : 
                                                                       (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                        >> 0x0000000aU)))) 
                                                                << 2U) 
                                                               | ((2U 
                                                                   & (((0x00000200U 
                                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                        ? 
                                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                        >> 9U)
                                                                        : 
                                                                       (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                        >> 9U)) 
                                                                      << 1U)) 
                                                                  | (1U 
                                                                     & ((0x00000100U 
                                                                         & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                         ? 
                                                                        (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                         >> 8U)
                                                                         : 
                                                                        (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                         [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                         >> 8U)))))) 
                                                           << 8U) 
                                                          | (((((2U 
                                                                 & (((0x00000080U 
                                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                      ? 
                                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                      >> 7U)
                                                                      : 
                                                                     (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                      >> 7U)) 
                                                                    << 1U)) 
                                                                | (1U 
                                                                   & ((0x00000040U 
                                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                       ? 
                                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                       >> 6U)
                                                                       : 
                                                                      (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                       >> 6U)))) 
                                                               << 6U) 
                                                              | (((2U 
                                                                   & (((0x00000020U 
                                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                        ? 
                                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                        >> 5U)
                                                                        : 
                                                                       (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                        >> 5U)) 
                                                                      << 1U)) 
                                                                  | (1U 
                                                                     & ((0x00000010U 
                                                                         & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                         ? 
                                                                        (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                         >> 4U)
                                                                         : 
                                                                        (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                         [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                         >> 4U)))) 
                                                                 << 4U)) 
                                                             | ((((2U 
                                                                   & (((8U 
                                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                        ? 
                                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                        >> 3U)
                                                                        : 
                                                                       (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                        >> 3U)) 
                                                                      << 1U)) 
                                                                  | (1U 
                                                                     & ((4U 
                                                                         & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                         ? 
                                                                        (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                         >> 2U)
                                                                         : 
                                                                        (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                         [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                         >> 2U)))) 
                                                                 << 2U) 
                                                                | ((2U 
                                                                    & (((2U 
                                                                         & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                         ? 
                                                                        (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                         >> 1U)
                                                                         : 
                                                                        (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                         [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                         >> 1U)) 
                                                                       << 1U)) 
                                                                   | (1U 
                                                                      & ((1U 
                                                                          & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                          ? vlSelfRef.L1DCache__DOT__wr_data_w0[7U]
                                                                          : vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                         [vlSelfRef.L1DCache__DOT__data_rd_addr][7U]))))))))) 
                                      << 0x00000020U) 
                                     | (QData)((IData)(
                                                       ((((((((2U 
                                                               & (((vlSelfRef.L1DCache__DOT__ram_be_w0[6U] 
                                                                    >> 0x0000001fU)
                                                                    ? 
                                                                   (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                    >> 0x0000001fU)
                                                                    : 
                                                                   (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                    [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                    >> 0x0000001fU)) 
                                                                  << 1U)) 
                                                              | (1U 
                                                                 & ((0x40000000U 
                                                                     & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                     ? 
                                                                    (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                     >> 0x0000001eU)
                                                                     : 
                                                                    (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                     >> 0x0000001eU)))) 
                                                             << 6U) 
                                                            | (((2U 
                                                                 & (((0x20000000U 
                                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                      ? 
                                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                      >> 0x0000001dU)
                                                                      : 
                                                                     (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                      >> 0x0000001dU)) 
                                                                    << 1U)) 
                                                                | (1U 
                                                                   & ((0x10000000U 
                                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                       ? 
                                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                       >> 0x0000001cU)
                                                                       : 
                                                                      (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                       >> 0x0000001cU)))) 
                                                               << 4U)) 
                                                           | ((((2U 
                                                                 & (((0x08000000U 
                                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                      ? 
                                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                      >> 0x0000001bU)
                                                                      : 
                                                                     (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                      >> 0x0000001bU)) 
                                                                    << 1U)) 
                                                                | (1U 
                                                                   & ((0x04000000U 
                                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                       ? 
                                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                       >> 0x0000001aU)
                                                                       : 
                                                                      (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                       >> 0x0000001aU)))) 
                                                               << 2U) 
                                                              | ((2U 
                                                                  & (((0x02000000U 
                                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                       ? 
                                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                       >> 0x00000019U)
                                                                       : 
                                                                      (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                       >> 0x00000019U)) 
                                                                     << 1U)) 
                                                                 | (1U 
                                                                    & ((0x01000000U 
                                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                        ? 
                                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                        >> 0x00000018U)
                                                                        : 
                                                                       (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                        >> 0x00000018U)))))) 
                                                          << 0x00000018U) 
                                                         | ((((((2U 
                                                                 & (((0x00800000U 
                                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                      ? 
                                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                      >> 0x00000017U)
                                                                      : 
                                                                     (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                      >> 0x00000017U)) 
                                                                    << 1U)) 
                                                                | (1U 
                                                                   & ((0x00400000U 
                                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                       ? 
                                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                       >> 0x00000016U)
                                                                       : 
                                                                      (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                       >> 0x00000016U)))) 
                                                               << 6U) 
                                                              | (((2U 
                                                                   & (((0x00200000U 
                                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                        ? 
                                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                        >> 0x00000015U)
                                                                        : 
                                                                       (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                        >> 0x00000015U)) 
                                                                      << 1U)) 
                                                                  | (1U 
                                                                     & ((0x00100000U 
                                                                         & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                         ? 
                                                                        (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                         >> 0x00000014U)
                                                                         : 
                                                                        (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                         [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                         >> 0x00000014U)))) 
                                                                 << 4U)) 
                                                             | ((((2U 
                                                                   & (((0x00080000U 
                                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                        ? 
                                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                        >> 0x00000013U)
                                                                        : 
                                                                       (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                        >> 0x00000013U)) 
                                                                      << 1U)) 
                                                                  | (1U 
                                                                     & ((0x00040000U 
                                                                         & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                         ? 
                                                                        (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                         >> 0x00000012U)
                                                                         : 
                                                                        (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                         [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                         >> 0x00000012U)))) 
                                                                 << 2U) 
                                                                | ((2U 
                                                                    & (((0x00020000U 
                                                                         & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                         ? 
                                                                        (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                         >> 0x00000011U)
                                                                         : 
                                                                        (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                         [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                         >> 0x00000011U)) 
                                                                       << 1U)) 
                                                                   | (1U 
                                                                      & ((0x00010000U 
                                                                          & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                          ? 
                                                                         (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                          >> 0x00000010U)
                                                                          : 
                                                                         (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                          [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                          >> 0x00000010U)))))) 
                                                            << 0x00000010U)) 
                                                        | (((((((2U 
                                                                 & (((0x00008000U 
                                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                      ? 
                                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                      >> 0x0000000fU)
                                                                      : 
                                                                     (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                      >> 0x0000000fU)) 
                                                                    << 1U)) 
                                                                | (1U 
                                                                   & ((0x00004000U 
                                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                       ? 
                                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                       >> 0x0000000eU)
                                                                       : 
                                                                      (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                       >> 0x0000000eU)))) 
                                                               << 6U) 
                                                              | (((2U 
                                                                   & (((0x00002000U 
                                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                        ? 
                                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                        >> 0x0000000dU)
                                                                        : 
                                                                       (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                        >> 0x0000000dU)) 
                                                                      << 1U)) 
                                                                  | (1U 
                                                                     & ((0x00001000U 
                                                                         & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                         ? 
                                                                        (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                         >> 0x0000000cU)
                                                                         : 
                                                                        (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                         [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                         >> 0x0000000cU)))) 
                                                                 << 4U)) 
                                                             | ((((2U 
                                                                   & (((0x00000800U 
                                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                        ? 
                                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                        >> 0x0000000bU)
                                                                        : 
                                                                       (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                        >> 0x0000000bU)) 
                                                                      << 1U)) 
                                                                  | (1U 
                                                                     & ((0x00000400U 
                                                                         & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                         ? 
                                                                        (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                         >> 0x0000000aU)
                                                                         : 
                                                                        (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                         [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                         >> 0x0000000aU)))) 
                                                                 << 2U) 
                                                                | ((2U 
                                                                    & (((0x00000200U 
                                                                         & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                         ? 
                                                                        (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                         >> 9U)
                                                                         : 
                                                                        (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                         [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                         >> 9U)) 
                                                                       << 1U)) 
                                                                   | (1U 
                                                                      & ((0x00000100U 
                                                                          & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                          ? 
                                                                         (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                          >> 8U)
                                                                          : 
                                                                         (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                          [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                          >> 8U)))))) 
                                                            << 8U) 
                                                           | (((((2U 
                                                                  & (((0x00000080U 
                                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                       ? 
                                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                       >> 7U)
                                                                       : 
                                                                      (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                       >> 7U)) 
                                                                     << 1U)) 
                                                                 | (1U 
                                                                    & ((0x00000040U 
                                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                        ? 
                                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                        >> 6U)
                                                                        : 
                                                                       (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                        >> 6U)))) 
                                                                << 6U) 
                                                               | (((2U 
                                                                    & (((0x00000020U 
                                                                         & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                         ? 
                                                                        (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                         >> 5U)
                                                                         : 
                                                                        (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                         [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                         >> 5U)) 
                                                                       << 1U)) 
                                                                   | (1U 
                                                                      & ((0x00000010U 
                                                                          & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                          ? 
                                                                         (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                          >> 4U)
                                                                          : 
                                                                         (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                          [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                          >> 4U)))) 
                                                                  << 4U)) 
                                                              | ((((2U 
                                                                    & (((8U 
                                                                         & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                         ? 
                                                                        (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                         >> 3U)
                                                                         : 
                                                                        (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                         [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                         >> 3U)) 
                                                                       << 1U)) 
                                                                   | (1U 
                                                                      & ((4U 
                                                                          & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                          ? 
                                                                         (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                          >> 2U)
                                                                          : 
                                                                         (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                          [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                          >> 2U)))) 
                                                                  << 2U) 
                                                                 | ((2U 
                                                                     & (((2U 
                                                                          & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                          ? 
                                                                         (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                          >> 1U)
                                                                          : 
                                                                         (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                          [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                          >> 1U)) 
                                                                        << 1U)) 
                                                                    | (1U 
                                                                       & ((1U 
                                                                           & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                           ? vlSelfRef.L1DCache__DOT__wr_data_w0[6U]
                                                                           : vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                          [vlSelfRef.L1DCache__DOT__data_rd_addr][6U])))))))))));
            __Vtemp_6[2U] = (IData)(((((QData)((IData)(
                                                       ((((((((2U 
                                                               & (((vlSelfRef.L1DCache__DOT__ram_be_w0[7U] 
                                                                    >> 0x0000001fU)
                                                                    ? 
                                                                   (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                    >> 0x0000001fU)
                                                                    : 
                                                                   (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                    [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                    >> 0x0000001fU)) 
                                                                  << 1U)) 
                                                              | (1U 
                                                                 & ((0x40000000U 
                                                                     & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                     ? 
                                                                    (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                     >> 0x0000001eU)
                                                                     : 
                                                                    (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                     >> 0x0000001eU)))) 
                                                             << 6U) 
                                                            | (((2U 
                                                                 & (((0x20000000U 
                                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                      ? 
                                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                      >> 0x0000001dU)
                                                                      : 
                                                                     (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                      >> 0x0000001dU)) 
                                                                    << 1U)) 
                                                                | (1U 
                                                                   & ((0x10000000U 
                                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                       ? 
                                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                       >> 0x0000001cU)
                                                                       : 
                                                                      (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                       >> 0x0000001cU)))) 
                                                               << 4U)) 
                                                           | ((((2U 
                                                                 & (((0x08000000U 
                                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                      ? 
                                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                      >> 0x0000001bU)
                                                                      : 
                                                                     (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                      >> 0x0000001bU)) 
                                                                    << 1U)) 
                                                                | (1U 
                                                                   & ((0x04000000U 
                                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                       ? 
                                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                       >> 0x0000001aU)
                                                                       : 
                                                                      (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                       >> 0x0000001aU)))) 
                                                               << 2U) 
                                                              | ((2U 
                                                                  & (((0x02000000U 
                                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                       ? 
                                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                       >> 0x00000019U)
                                                                       : 
                                                                      (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                       >> 0x00000019U)) 
                                                                     << 1U)) 
                                                                 | (1U 
                                                                    & ((0x01000000U 
                                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                        ? 
                                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                        >> 0x00000018U)
                                                                        : 
                                                                       (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                        >> 0x00000018U)))))) 
                                                          << 0x00000018U) 
                                                         | ((((((2U 
                                                                 & (((0x00800000U 
                                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                      ? 
                                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                      >> 0x00000017U)
                                                                      : 
                                                                     (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                      >> 0x00000017U)) 
                                                                    << 1U)) 
                                                                | (1U 
                                                                   & ((0x00400000U 
                                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                       ? 
                                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                       >> 0x00000016U)
                                                                       : 
                                                                      (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                       >> 0x00000016U)))) 
                                                               << 6U) 
                                                              | (((2U 
                                                                   & (((0x00200000U 
                                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                        ? 
                                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                        >> 0x00000015U)
                                                                        : 
                                                                       (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                        >> 0x00000015U)) 
                                                                      << 1U)) 
                                                                  | (1U 
                                                                     & ((0x00100000U 
                                                                         & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                         ? 
                                                                        (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                         >> 0x00000014U)
                                                                         : 
                                                                        (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                         [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                         >> 0x00000014U)))) 
                                                                 << 4U)) 
                                                             | ((((2U 
                                                                   & (((0x00080000U 
                                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                        ? 
                                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                        >> 0x00000013U)
                                                                        : 
                                                                       (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                        >> 0x00000013U)) 
                                                                      << 1U)) 
                                                                  | (1U 
                                                                     & ((0x00040000U 
                                                                         & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                         ? 
                                                                        (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                         >> 0x00000012U)
                                                                         : 
                                                                        (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                         [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                         >> 0x00000012U)))) 
                                                                 << 2U) 
                                                                | ((2U 
                                                                    & (((0x00020000U 
                                                                         & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                         ? 
                                                                        (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                         >> 0x00000011U)
                                                                         : 
                                                                        (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                         [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                         >> 0x00000011U)) 
                                                                       << 1U)) 
                                                                   | (1U 
                                                                      & ((0x00010000U 
                                                                          & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                          ? 
                                                                         (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                          >> 0x00000010U)
                                                                          : 
                                                                         (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                          [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                          >> 0x00000010U)))))) 
                                                            << 0x00000010U)) 
                                                        | (((((((2U 
                                                                 & (((0x00008000U 
                                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                      ? 
                                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                      >> 0x0000000fU)
                                                                      : 
                                                                     (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                      >> 0x0000000fU)) 
                                                                    << 1U)) 
                                                                | (1U 
                                                                   & ((0x00004000U 
                                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                       ? 
                                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                       >> 0x0000000eU)
                                                                       : 
                                                                      (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                       >> 0x0000000eU)))) 
                                                               << 6U) 
                                                              | (((2U 
                                                                   & (((0x00002000U 
                                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                        ? 
                                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                        >> 0x0000000dU)
                                                                        : 
                                                                       (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                        >> 0x0000000dU)) 
                                                                      << 1U)) 
                                                                  | (1U 
                                                                     & ((0x00001000U 
                                                                         & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                         ? 
                                                                        (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                         >> 0x0000000cU)
                                                                         : 
                                                                        (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                         [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                         >> 0x0000000cU)))) 
                                                                 << 4U)) 
                                                             | ((((2U 
                                                                   & (((0x00000800U 
                                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                        ? 
                                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                        >> 0x0000000bU)
                                                                        : 
                                                                       (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                        >> 0x0000000bU)) 
                                                                      << 1U)) 
                                                                  | (1U 
                                                                     & ((0x00000400U 
                                                                         & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                         ? 
                                                                        (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                         >> 0x0000000aU)
                                                                         : 
                                                                        (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                         [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                         >> 0x0000000aU)))) 
                                                                 << 2U) 
                                                                | ((2U 
                                                                    & (((0x00000200U 
                                                                         & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                         ? 
                                                                        (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                         >> 9U)
                                                                         : 
                                                                        (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                         [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                         >> 9U)) 
                                                                       << 1U)) 
                                                                   | (1U 
                                                                      & ((0x00000100U 
                                                                          & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                          ? 
                                                                         (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                          >> 8U)
                                                                          : 
                                                                         (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                          [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                          >> 8U)))))) 
                                                            << 8U) 
                                                           | (((((2U 
                                                                  & (((0x00000080U 
                                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                       ? 
                                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                       >> 7U)
                                                                       : 
                                                                      (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                       >> 7U)) 
                                                                     << 1U)) 
                                                                 | (1U 
                                                                    & ((0x00000040U 
                                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                        ? 
                                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                        >> 6U)
                                                                        : 
                                                                       (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                        >> 6U)))) 
                                                                << 6U) 
                                                               | (((2U 
                                                                    & (((0x00000020U 
                                                                         & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                         ? 
                                                                        (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                         >> 5U)
                                                                         : 
                                                                        (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                         [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                         >> 5U)) 
                                                                       << 1U)) 
                                                                   | (1U 
                                                                      & ((0x00000010U 
                                                                          & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                          ? 
                                                                         (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                          >> 4U)
                                                                          : 
                                                                         (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                          [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                          >> 4U)))) 
                                                                  << 4U)) 
                                                              | ((((2U 
                                                                    & (((8U 
                                                                         & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                         ? 
                                                                        (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                         >> 3U)
                                                                         : 
                                                                        (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                         [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                         >> 3U)) 
                                                                       << 1U)) 
                                                                   | (1U 
                                                                      & ((4U 
                                                                          & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                          ? 
                                                                         (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                          >> 2U)
                                                                          : 
                                                                         (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                          [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                          >> 2U)))) 
                                                                  << 2U) 
                                                                 | ((2U 
                                                                     & (((2U 
                                                                          & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                          ? 
                                                                         (vlSelfRef.L1DCache__DOT__wr_data_w0[7U] 
                                                                          >> 1U)
                                                                          : 
                                                                         (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                          [vlSelfRef.L1DCache__DOT__data_rd_addr][7U] 
                                                                          >> 1U)) 
                                                                        << 1U)) 
                                                                    | (1U 
                                                                       & ((1U 
                                                                           & vlSelfRef.L1DCache__DOT__ram_be_w0[7U])
                                                                           ? vlSelfRef.L1DCache__DOT__wr_data_w0[7U]
                                                                           : vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                          [vlSelfRef.L1DCache__DOT__data_rd_addr][7U]))))))))) 
                                       << 0x00000020U) 
                                      | (QData)((IData)(
                                                        ((((((((2U 
                                                                & (((vlSelfRef.L1DCache__DOT__ram_be_w0[6U] 
                                                                     >> 0x0000001fU)
                                                                     ? 
                                                                    (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                     >> 0x0000001fU)
                                                                     : 
                                                                    (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                     >> 0x0000001fU)) 
                                                                   << 1U)) 
                                                               | (1U 
                                                                  & ((0x40000000U 
                                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                      ? 
                                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                      >> 0x0000001eU)
                                                                      : 
                                                                     (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                      >> 0x0000001eU)))) 
                                                              << 6U) 
                                                             | (((2U 
                                                                  & (((0x20000000U 
                                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                       ? 
                                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                       >> 0x0000001dU)
                                                                       : 
                                                                      (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                       >> 0x0000001dU)) 
                                                                     << 1U)) 
                                                                 | (1U 
                                                                    & ((0x10000000U 
                                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                        ? 
                                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                        >> 0x0000001cU)
                                                                        : 
                                                                       (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                        >> 0x0000001cU)))) 
                                                                << 4U)) 
                                                            | ((((2U 
                                                                  & (((0x08000000U 
                                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                       ? 
                                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                       >> 0x0000001bU)
                                                                       : 
                                                                      (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                       >> 0x0000001bU)) 
                                                                     << 1U)) 
                                                                 | (1U 
                                                                    & ((0x04000000U 
                                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                        ? 
                                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                        >> 0x0000001aU)
                                                                        : 
                                                                       (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                        >> 0x0000001aU)))) 
                                                                << 2U) 
                                                               | ((2U 
                                                                   & (((0x02000000U 
                                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                        ? 
                                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                        >> 0x00000019U)
                                                                        : 
                                                                       (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                        >> 0x00000019U)) 
                                                                      << 1U)) 
                                                                  | (1U 
                                                                     & ((0x01000000U 
                                                                         & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                         ? 
                                                                        (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                         >> 0x00000018U)
                                                                         : 
                                                                        (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                         [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                         >> 0x00000018U)))))) 
                                                           << 0x00000018U) 
                                                          | ((((((2U 
                                                                  & (((0x00800000U 
                                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                       ? 
                                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                       >> 0x00000017U)
                                                                       : 
                                                                      (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                       >> 0x00000017U)) 
                                                                     << 1U)) 
                                                                 | (1U 
                                                                    & ((0x00400000U 
                                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                        ? 
                                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                        >> 0x00000016U)
                                                                        : 
                                                                       (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                        >> 0x00000016U)))) 
                                                                << 6U) 
                                                               | (((2U 
                                                                    & (((0x00200000U 
                                                                         & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                         ? 
                                                                        (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                         >> 0x00000015U)
                                                                         : 
                                                                        (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                         [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                         >> 0x00000015U)) 
                                                                       << 1U)) 
                                                                   | (1U 
                                                                      & ((0x00100000U 
                                                                          & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                          ? 
                                                                         (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                          >> 0x00000014U)
                                                                          : 
                                                                         (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                          [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                          >> 0x00000014U)))) 
                                                                  << 4U)) 
                                                              | ((((2U 
                                                                    & (((0x00080000U 
                                                                         & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                         ? 
                                                                        (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                         >> 0x00000013U)
                                                                         : 
                                                                        (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                         [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                         >> 0x00000013U)) 
                                                                       << 1U)) 
                                                                   | (1U 
                                                                      & ((0x00040000U 
                                                                          & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                          ? 
                                                                         (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                          >> 0x00000012U)
                                                                          : 
                                                                         (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                          [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                          >> 0x00000012U)))) 
                                                                  << 2U) 
                                                                 | ((2U 
                                                                     & (((0x00020000U 
                                                                          & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                          ? 
                                                                         (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                          >> 0x00000011U)
                                                                          : 
                                                                         (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                          [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                          >> 0x00000011U)) 
                                                                        << 1U)) 
                                                                    | (1U 
                                                                       & ((0x00010000U 
                                                                           & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                           ? 
                                                                          (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                           >> 0x00000010U)
                                                                           : 
                                                                          (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                           [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                           >> 0x00000010U)))))) 
                                                             << 0x00000010U)) 
                                                         | (((((((2U 
                                                                  & (((0x00008000U 
                                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                       ? 
                                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                       >> 0x0000000fU)
                                                                       : 
                                                                      (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                       >> 0x0000000fU)) 
                                                                     << 1U)) 
                                                                 | (1U 
                                                                    & ((0x00004000U 
                                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                        ? 
                                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                        >> 0x0000000eU)
                                                                        : 
                                                                       (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                        >> 0x0000000eU)))) 
                                                                << 6U) 
                                                               | (((2U 
                                                                    & (((0x00002000U 
                                                                         & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                         ? 
                                                                        (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                         >> 0x0000000dU)
                                                                         : 
                                                                        (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                         [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                         >> 0x0000000dU)) 
                                                                       << 1U)) 
                                                                   | (1U 
                                                                      & ((0x00001000U 
                                                                          & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                          ? 
                                                                         (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                          >> 0x0000000cU)
                                                                          : 
                                                                         (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                          [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                          >> 0x0000000cU)))) 
                                                                  << 4U)) 
                                                              | ((((2U 
                                                                    & (((0x00000800U 
                                                                         & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                         ? 
                                                                        (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                         >> 0x0000000bU)
                                                                         : 
                                                                        (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                         [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                         >> 0x0000000bU)) 
                                                                       << 1U)) 
                                                                   | (1U 
                                                                      & ((0x00000400U 
                                                                          & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                          ? 
                                                                         (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                          >> 0x0000000aU)
                                                                          : 
                                                                         (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                          [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                          >> 0x0000000aU)))) 
                                                                  << 2U) 
                                                                 | ((2U 
                                                                     & (((0x00000200U 
                                                                          & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                          ? 
                                                                         (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                          >> 9U)
                                                                          : 
                                                                         (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                          [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                          >> 9U)) 
                                                                        << 1U)) 
                                                                    | (1U 
                                                                       & ((0x00000100U 
                                                                           & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                           ? 
                                                                          (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                           >> 8U)
                                                                           : 
                                                                          (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                           [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                           >> 8U)))))) 
                                                             << 8U) 
                                                            | (((((2U 
                                                                   & (((0x00000080U 
                                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                        ? 
                                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                        >> 7U)
                                                                        : 
                                                                       (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                        >> 7U)) 
                                                                      << 1U)) 
                                                                  | (1U 
                                                                     & ((0x00000040U 
                                                                         & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                         ? 
                                                                        (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                         >> 6U)
                                                                         : 
                                                                        (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                         [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                         >> 6U)))) 
                                                                 << 6U) 
                                                                | (((2U 
                                                                     & (((0x00000020U 
                                                                          & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                          ? 
                                                                         (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                          >> 5U)
                                                                          : 
                                                                         (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                          [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                          >> 5U)) 
                                                                        << 1U)) 
                                                                    | (1U 
                                                                       & ((0x00000010U 
                                                                           & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                           ? 
                                                                          (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                           >> 4U)
                                                                           : 
                                                                          (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                           [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                           >> 4U)))) 
                                                                   << 4U)) 
                                                               | ((((2U 
                                                                     & (((8U 
                                                                          & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                          ? 
                                                                         (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                          >> 3U)
                                                                          : 
                                                                         (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                          [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                          >> 3U)) 
                                                                        << 1U)) 
                                                                    | (1U 
                                                                       & ((4U 
                                                                           & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                           ? 
                                                                          (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                           >> 2U)
                                                                           : 
                                                                          (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                           [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                           >> 2U)))) 
                                                                   << 2U) 
                                                                  | ((2U 
                                                                      & (((2U 
                                                                           & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                           ? 
                                                                          (vlSelfRef.L1DCache__DOT__wr_data_w0[6U] 
                                                                           >> 1U)
                                                                           : 
                                                                          (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                           [vlSelfRef.L1DCache__DOT__data_rd_addr][6U] 
                                                                           >> 1U)) 
                                                                         << 1U)) 
                                                                     | (1U 
                                                                        & ((1U 
                                                                            & vlSelfRef.L1DCache__DOT__ram_be_w0[6U])
                                                                            ? vlSelfRef.L1DCache__DOT__wr_data_w0[6U]
                                                                            : vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                           [vlSelfRef.L1DCache__DOT__data_rd_addr][6U])))))))))) 
                                     >> 0x00000020U));
            __Vtemp_7[0U] = ((((((((2U & (((vlSelfRef.L1DCache__DOT__ram_be_w0[4U] 
                                            >> 0x0000001fU)
                                            ? (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                               >> 0x0000001fU)
                                            : (vlSelfRef.L1DCache__DOT__data_ram_w1
                                               [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                               >> 0x0000001fU)) 
                                          << 1U)) | 
                                   (1U & ((0x40000000U 
                                           & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                           ? (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                              >> 0x0000001eU)
                                           : (vlSelfRef.L1DCache__DOT__data_ram_w1
                                              [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                              >> 0x0000001eU)))) 
                                  << 6U) | (((2U & 
                                              (((0x20000000U 
                                                 & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                                 ? 
                                                (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                                 >> 0x0000001dU)
                                                 : 
                                                (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                 [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                                 >> 0x0000001dU)) 
                                               << 1U)) 
                                             | (1U 
                                                & ((0x10000000U 
                                                    & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                                    ? 
                                                   (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                                    >> 0x0000001cU)
                                                    : 
                                                   (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                    [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                                    >> 0x0000001cU)))) 
                                            << 4U)) 
                                | ((((2U & (((0x08000000U 
                                              & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                              ? (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                                 >> 0x0000001bU)
                                              : (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                 [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                                 >> 0x0000001bU)) 
                                            << 1U)) 
                                     | (1U & ((0x04000000U 
                                               & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                               ? (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                                  >> 0x0000001aU)
                                               : (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                  [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                                  >> 0x0000001aU)))) 
                                    << 2U) | ((2U & 
                                               (((0x02000000U 
                                                  & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                                  ? 
                                                 (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                                  >> 0x00000019U)
                                                  : 
                                                 (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                  [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                                  >> 0x00000019U)) 
                                                << 1U)) 
                                              | (1U 
                                                 & ((0x01000000U 
                                                     & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                                     ? 
                                                    (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                                     >> 0x00000018U)
                                                     : 
                                                    (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                                     >> 0x00000018U)))))) 
                               << 0x00000018U) | ((
                                                   ((((2U 
                                                       & (((0x00800000U 
                                                            & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                                            ? 
                                                           (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                                            >> 0x00000017U)
                                                            : 
                                                           (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                            [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                                            >> 0x00000017U)) 
                                                          << 1U)) 
                                                      | (1U 
                                                         & ((0x00400000U 
                                                             & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                                             ? 
                                                            (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                                             >> 0x00000016U)
                                                             : 
                                                            (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                             [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                                             >> 0x00000016U)))) 
                                                     << 6U) 
                                                    | (((2U 
                                                         & (((0x00200000U 
                                                              & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                                              ? 
                                                             (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                                              >> 0x00000015U)
                                                              : 
                                                             (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                              [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                                              >> 0x00000015U)) 
                                                            << 1U)) 
                                                        | (1U 
                                                           & ((0x00100000U 
                                                               & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                                               ? 
                                                              (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                                               >> 0x00000014U)
                                                               : 
                                                              (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                               [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                                               >> 0x00000014U)))) 
                                                       << 4U)) 
                                                   | ((((2U 
                                                         & (((0x00080000U 
                                                              & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                                              ? 
                                                             (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                                              >> 0x00000013U)
                                                              : 
                                                             (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                              [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                                              >> 0x00000013U)) 
                                                            << 1U)) 
                                                        | (1U 
                                                           & ((0x00040000U 
                                                               & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                                               ? 
                                                              (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                                               >> 0x00000012U)
                                                               : 
                                                              (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                               [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                                               >> 0x00000012U)))) 
                                                       << 2U) 
                                                      | ((2U 
                                                          & (((0x00020000U 
                                                               & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                                               ? 
                                                              (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                                               >> 0x00000011U)
                                                               : 
                                                              (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                               [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                                               >> 0x00000011U)) 
                                                             << 1U)) 
                                                         | (1U 
                                                            & ((0x00010000U 
                                                                & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                                                ? 
                                                               (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                                                >> 0x00000010U)
                                                                : 
                                                               (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                                                >> 0x00000010U)))))) 
                                                  << 0x00000010U)) 
                             | (((((((2U & (((0x00008000U 
                                              & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                              ? (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                                 >> 0x0000000fU)
                                              : (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                 [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                                 >> 0x0000000fU)) 
                                            << 1U)) 
                                     | (1U & ((0x00004000U 
                                               & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                               ? (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                                  >> 0x0000000eU)
                                               : (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                  [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                                  >> 0x0000000eU)))) 
                                    << 6U) | (((2U 
                                                & (((0x00002000U 
                                                     & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                                     ? 
                                                    (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                                     >> 0x0000000dU)
                                                     : 
                                                    (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                                     >> 0x0000000dU)) 
                                                   << 1U)) 
                                               | (1U 
                                                  & ((0x00001000U 
                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                                      ? 
                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                                      >> 0x0000000cU)
                                                      : 
                                                     (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                                      >> 0x0000000cU)))) 
                                              << 4U)) 
                                  | ((((2U & (((0x00000800U 
                                                & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                                ? (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                                   >> 0x0000000bU)
                                                : (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                   [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                                   >> 0x0000000bU)) 
                                              << 1U)) 
                                       | (1U & ((0x00000400U 
                                                 & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                                 ? 
                                                (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                                 >> 0x0000000aU)
                                                 : 
                                                (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                 [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                                 >> 0x0000000aU)))) 
                                      << 2U) | ((2U 
                                                 & (((0x00000200U 
                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                                      ? 
                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                                      >> 9U)
                                                      : 
                                                     (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                                      >> 9U)) 
                                                    << 1U)) 
                                                | (1U 
                                                   & ((0x00000100U 
                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                                       ? 
                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                                       >> 8U)
                                                       : 
                                                      (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                                       >> 8U)))))) 
                                 << 8U) | (((((2U & 
                                               (((0x00000080U 
                                                  & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                                  ? 
                                                 (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                                  >> 7U)
                                                  : 
                                                 (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                  [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                                  >> 7U)) 
                                                << 1U)) 
                                              | (1U 
                                                 & ((0x00000040U 
                                                     & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                                     ? 
                                                    (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                                     >> 6U)
                                                     : 
                                                    (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                                     >> 6U)))) 
                                             << 6U) 
                                            | (((2U 
                                                 & (((0x00000020U 
                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                                      ? 
                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                                      >> 5U)
                                                      : 
                                                     (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                                      >> 5U)) 
                                                    << 1U)) 
                                                | (1U 
                                                   & ((0x00000010U 
                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                                       ? 
                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                                       >> 4U)
                                                       : 
                                                      (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                                       >> 4U)))) 
                                               << 4U)) 
                                           | ((((2U 
                                                 & (((8U 
                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                                      ? 
                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                                      >> 3U)
                                                      : 
                                                     (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                                      >> 3U)) 
                                                    << 1U)) 
                                                | (1U 
                                                   & ((4U 
                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                                       ? 
                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                                       >> 2U)
                                                       : 
                                                      (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                                       >> 2U)))) 
                                               << 2U) 
                                              | ((2U 
                                                  & (((2U 
                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                                       ? 
                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[4U] 
                                                       >> 1U)
                                                       : 
                                                      (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][4U] 
                                                       >> 1U)) 
                                                     << 1U)) 
                                                 | (1U 
                                                    & ((1U 
                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[4U])
                                                        ? vlSelfRef.L1DCache__DOT__wr_data_w0[4U]
                                                        : vlSelfRef.L1DCache__DOT__data_ram_w1
                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][4U])))))));
            __Vtemp_8[0U] = ((((((((2U & (((vlSelfRef.L1DCache__DOT__ram_be_w0[3U] 
                                            >> 0x0000001fU)
                                            ? (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                               >> 0x0000001fU)
                                            : (vlSelfRef.L1DCache__DOT__data_ram_w1
                                               [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                               >> 0x0000001fU)) 
                                          << 1U)) | 
                                   (1U & ((0x40000000U 
                                           & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                           ? (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                              >> 0x0000001eU)
                                           : (vlSelfRef.L1DCache__DOT__data_ram_w1
                                              [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                              >> 0x0000001eU)))) 
                                  << 6U) | (((2U & 
                                              (((0x20000000U 
                                                 & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                                 ? 
                                                (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                                 >> 0x0000001dU)
                                                 : 
                                                (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                 [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                                 >> 0x0000001dU)) 
                                               << 1U)) 
                                             | (1U 
                                                & ((0x10000000U 
                                                    & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                                    ? 
                                                   (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                                    >> 0x0000001cU)
                                                    : 
                                                   (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                    [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                                    >> 0x0000001cU)))) 
                                            << 4U)) 
                                | ((((2U & (((0x08000000U 
                                              & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                              ? (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                                 >> 0x0000001bU)
                                              : (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                 [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                                 >> 0x0000001bU)) 
                                            << 1U)) 
                                     | (1U & ((0x04000000U 
                                               & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                               ? (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                                  >> 0x0000001aU)
                                               : (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                  [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                                  >> 0x0000001aU)))) 
                                    << 2U) | ((2U & 
                                               (((0x02000000U 
                                                  & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                                  ? 
                                                 (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                                  >> 0x00000019U)
                                                  : 
                                                 (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                  [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                                  >> 0x00000019U)) 
                                                << 1U)) 
                                              | (1U 
                                                 & ((0x01000000U 
                                                     & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                                     ? 
                                                    (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                                     >> 0x00000018U)
                                                     : 
                                                    (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                                     >> 0x00000018U)))))) 
                               << 0x00000018U) | ((
                                                   ((((2U 
                                                       & (((0x00800000U 
                                                            & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                                            ? 
                                                           (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                                            >> 0x00000017U)
                                                            : 
                                                           (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                            [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                                            >> 0x00000017U)) 
                                                          << 1U)) 
                                                      | (1U 
                                                         & ((0x00400000U 
                                                             & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                                             ? 
                                                            (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                                             >> 0x00000016U)
                                                             : 
                                                            (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                             [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                                             >> 0x00000016U)))) 
                                                     << 6U) 
                                                    | (((2U 
                                                         & (((0x00200000U 
                                                              & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                                              ? 
                                                             (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                                              >> 0x00000015U)
                                                              : 
                                                             (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                              [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                                              >> 0x00000015U)) 
                                                            << 1U)) 
                                                        | (1U 
                                                           & ((0x00100000U 
                                                               & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                                               ? 
                                                              (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                                               >> 0x00000014U)
                                                               : 
                                                              (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                               [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                                               >> 0x00000014U)))) 
                                                       << 4U)) 
                                                   | ((((2U 
                                                         & (((0x00080000U 
                                                              & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                                              ? 
                                                             (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                                              >> 0x00000013U)
                                                              : 
                                                             (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                              [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                                              >> 0x00000013U)) 
                                                            << 1U)) 
                                                        | (1U 
                                                           & ((0x00040000U 
                                                               & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                                               ? 
                                                              (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                                               >> 0x00000012U)
                                                               : 
                                                              (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                               [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                                               >> 0x00000012U)))) 
                                                       << 2U) 
                                                      | ((2U 
                                                          & (((0x00020000U 
                                                               & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                                               ? 
                                                              (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                                               >> 0x00000011U)
                                                               : 
                                                              (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                               [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                                               >> 0x00000011U)) 
                                                             << 1U)) 
                                                         | (1U 
                                                            & ((0x00010000U 
                                                                & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                                                ? 
                                                               (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                                                >> 0x00000010U)
                                                                : 
                                                               (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                                                >> 0x00000010U)))))) 
                                                  << 0x00000010U)) 
                             | (((((((2U & (((0x00008000U 
                                              & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                              ? (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                                 >> 0x0000000fU)
                                              : (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                 [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                                 >> 0x0000000fU)) 
                                            << 1U)) 
                                     | (1U & ((0x00004000U 
                                               & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                               ? (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                                  >> 0x0000000eU)
                                               : (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                  [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                                  >> 0x0000000eU)))) 
                                    << 6U) | (((2U 
                                                & (((0x00002000U 
                                                     & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                                     ? 
                                                    (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                                     >> 0x0000000dU)
                                                     : 
                                                    (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                                     >> 0x0000000dU)) 
                                                   << 1U)) 
                                               | (1U 
                                                  & ((0x00001000U 
                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                                      ? 
                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                                      >> 0x0000000cU)
                                                      : 
                                                     (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                                      >> 0x0000000cU)))) 
                                              << 4U)) 
                                  | ((((2U & (((0x00000800U 
                                                & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                                ? (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                                   >> 0x0000000bU)
                                                : (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                   [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                                   >> 0x0000000bU)) 
                                              << 1U)) 
                                       | (1U & ((0x00000400U 
                                                 & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                                 ? 
                                                (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                                 >> 0x0000000aU)
                                                 : 
                                                (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                 [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                                 >> 0x0000000aU)))) 
                                      << 2U) | ((2U 
                                                 & (((0x00000200U 
                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                                      ? 
                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                                      >> 9U)
                                                      : 
                                                     (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                                      >> 9U)) 
                                                    << 1U)) 
                                                | (1U 
                                                   & ((0x00000100U 
                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                                       ? 
                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                                       >> 8U)
                                                       : 
                                                      (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                                       >> 8U)))))) 
                                 << 8U) | (((((2U & 
                                               (((0x00000080U 
                                                  & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                                  ? 
                                                 (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                                  >> 7U)
                                                  : 
                                                 (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                  [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                                  >> 7U)) 
                                                << 1U)) 
                                              | (1U 
                                                 & ((0x00000040U 
                                                     & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                                     ? 
                                                    (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                                     >> 6U)
                                                     : 
                                                    (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                                     >> 6U)))) 
                                             << 6U) 
                                            | (((2U 
                                                 & (((0x00000020U 
                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                                      ? 
                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                                      >> 5U)
                                                      : 
                                                     (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                                      >> 5U)) 
                                                    << 1U)) 
                                                | (1U 
                                                   & ((0x00000010U 
                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                                       ? 
                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                                       >> 4U)
                                                       : 
                                                      (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                                       >> 4U)))) 
                                               << 4U)) 
                                           | ((((2U 
                                                 & (((8U 
                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                                      ? 
                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                                      >> 3U)
                                                      : 
                                                     (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                                      >> 3U)) 
                                                    << 1U)) 
                                                | (1U 
                                                   & ((4U 
                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                                       ? 
                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                                       >> 2U)
                                                       : 
                                                      (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                                       >> 2U)))) 
                                               << 2U) 
                                              | ((2U 
                                                  & (((2U 
                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                                       ? 
                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[3U] 
                                                       >> 1U)
                                                       : 
                                                      (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][3U] 
                                                       >> 1U)) 
                                                     << 1U)) 
                                                 | (1U 
                                                    & ((1U 
                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[3U])
                                                        ? vlSelfRef.L1DCache__DOT__wr_data_w0[3U]
                                                        : vlSelfRef.L1DCache__DOT__data_ram_w1
                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][3U])))))));
            __Vtemp_9[0U] = ((((((((2U & (((vlSelfRef.L1DCache__DOT__ram_be_w0[2U] 
                                            >> 0x0000001fU)
                                            ? (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                               >> 0x0000001fU)
                                            : (vlSelfRef.L1DCache__DOT__data_ram_w1
                                               [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                               >> 0x0000001fU)) 
                                          << 1U)) | 
                                   (1U & ((0x40000000U 
                                           & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                           ? (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                              >> 0x0000001eU)
                                           : (vlSelfRef.L1DCache__DOT__data_ram_w1
                                              [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                              >> 0x0000001eU)))) 
                                  << 6U) | (((2U & 
                                              (((0x20000000U 
                                                 & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                                 ? 
                                                (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                                 >> 0x0000001dU)
                                                 : 
                                                (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                 [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                                 >> 0x0000001dU)) 
                                               << 1U)) 
                                             | (1U 
                                                & ((0x10000000U 
                                                    & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                                    ? 
                                                   (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                                    >> 0x0000001cU)
                                                    : 
                                                   (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                    [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                                    >> 0x0000001cU)))) 
                                            << 4U)) 
                                | ((((2U & (((0x08000000U 
                                              & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                              ? (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                                 >> 0x0000001bU)
                                              : (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                 [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                                 >> 0x0000001bU)) 
                                            << 1U)) 
                                     | (1U & ((0x04000000U 
                                               & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                               ? (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                                  >> 0x0000001aU)
                                               : (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                  [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                                  >> 0x0000001aU)))) 
                                    << 2U) | ((2U & 
                                               (((0x02000000U 
                                                  & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                                  ? 
                                                 (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                                  >> 0x00000019U)
                                                  : 
                                                 (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                  [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                                  >> 0x00000019U)) 
                                                << 1U)) 
                                              | (1U 
                                                 & ((0x01000000U 
                                                     & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                                     ? 
                                                    (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                                     >> 0x00000018U)
                                                     : 
                                                    (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                                     >> 0x00000018U)))))) 
                               << 0x00000018U) | ((
                                                   ((((2U 
                                                       & (((0x00800000U 
                                                            & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                                            ? 
                                                           (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                                            >> 0x00000017U)
                                                            : 
                                                           (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                            [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                                            >> 0x00000017U)) 
                                                          << 1U)) 
                                                      | (1U 
                                                         & ((0x00400000U 
                                                             & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                                             ? 
                                                            (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                                             >> 0x00000016U)
                                                             : 
                                                            (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                             [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                                             >> 0x00000016U)))) 
                                                     << 6U) 
                                                    | (((2U 
                                                         & (((0x00200000U 
                                                              & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                                              ? 
                                                             (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                                              >> 0x00000015U)
                                                              : 
                                                             (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                              [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                                              >> 0x00000015U)) 
                                                            << 1U)) 
                                                        | (1U 
                                                           & ((0x00100000U 
                                                               & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                                               ? 
                                                              (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                                               >> 0x00000014U)
                                                               : 
                                                              (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                               [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                                               >> 0x00000014U)))) 
                                                       << 4U)) 
                                                   | ((((2U 
                                                         & (((0x00080000U 
                                                              & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                                              ? 
                                                             (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                                              >> 0x00000013U)
                                                              : 
                                                             (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                              [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                                              >> 0x00000013U)) 
                                                            << 1U)) 
                                                        | (1U 
                                                           & ((0x00040000U 
                                                               & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                                               ? 
                                                              (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                                               >> 0x00000012U)
                                                               : 
                                                              (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                               [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                                               >> 0x00000012U)))) 
                                                       << 2U) 
                                                      | ((2U 
                                                          & (((0x00020000U 
                                                               & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                                               ? 
                                                              (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                                               >> 0x00000011U)
                                                               : 
                                                              (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                               [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                                               >> 0x00000011U)) 
                                                             << 1U)) 
                                                         | (1U 
                                                            & ((0x00010000U 
                                                                & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                                                ? 
                                                               (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                                                >> 0x00000010U)
                                                                : 
                                                               (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                                                >> 0x00000010U)))))) 
                                                  << 0x00000010U)) 
                             | (((((((2U & (((0x00008000U 
                                              & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                              ? (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                                 >> 0x0000000fU)
                                              : (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                 [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                                 >> 0x0000000fU)) 
                                            << 1U)) 
                                     | (1U & ((0x00004000U 
                                               & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                               ? (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                                  >> 0x0000000eU)
                                               : (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                  [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                                  >> 0x0000000eU)))) 
                                    << 6U) | (((2U 
                                                & (((0x00002000U 
                                                     & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                                     ? 
                                                    (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                                     >> 0x0000000dU)
                                                     : 
                                                    (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                                     >> 0x0000000dU)) 
                                                   << 1U)) 
                                               | (1U 
                                                  & ((0x00001000U 
                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                                      ? 
                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                                      >> 0x0000000cU)
                                                      : 
                                                     (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                                      >> 0x0000000cU)))) 
                                              << 4U)) 
                                  | ((((2U & (((0x00000800U 
                                                & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                                ? (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                                   >> 0x0000000bU)
                                                : (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                   [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                                   >> 0x0000000bU)) 
                                              << 1U)) 
                                       | (1U & ((0x00000400U 
                                                 & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                                 ? 
                                                (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                                 >> 0x0000000aU)
                                                 : 
                                                (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                 [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                                 >> 0x0000000aU)))) 
                                      << 2U) | ((2U 
                                                 & (((0x00000200U 
                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                                      ? 
                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                                      >> 9U)
                                                      : 
                                                     (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                                      >> 9U)) 
                                                    << 1U)) 
                                                | (1U 
                                                   & ((0x00000100U 
                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                                       ? 
                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                                       >> 8U)
                                                       : 
                                                      (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                                       >> 8U)))))) 
                                 << 8U) | (((((2U & 
                                               (((0x00000080U 
                                                  & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                                  ? 
                                                 (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                                  >> 7U)
                                                  : 
                                                 (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                  [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                                  >> 7U)) 
                                                << 1U)) 
                                              | (1U 
                                                 & ((0x00000040U 
                                                     & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                                     ? 
                                                    (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                                     >> 6U)
                                                     : 
                                                    (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                                     >> 6U)))) 
                                             << 6U) 
                                            | (((2U 
                                                 & (((0x00000020U 
                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                                      ? 
                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                                      >> 5U)
                                                      : 
                                                     (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                                      >> 5U)) 
                                                    << 1U)) 
                                                | (1U 
                                                   & ((0x00000010U 
                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                                       ? 
                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                                       >> 4U)
                                                       : 
                                                      (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                                       >> 4U)))) 
                                               << 4U)) 
                                           | ((((2U 
                                                 & (((8U 
                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                                      ? 
                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                                      >> 3U)
                                                      : 
                                                     (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                                      >> 3U)) 
                                                    << 1U)) 
                                                | (1U 
                                                   & ((4U 
                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                                       ? 
                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                                       >> 2U)
                                                       : 
                                                      (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                                       >> 2U)))) 
                                               << 2U) 
                                              | ((2U 
                                                  & (((2U 
                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                                       ? 
                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[2U] 
                                                       >> 1U)
                                                       : 
                                                      (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][2U] 
                                                       >> 1U)) 
                                                     << 1U)) 
                                                 | (1U 
                                                    & ((1U 
                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[2U])
                                                        ? vlSelfRef.L1DCache__DOT__wr_data_w0[2U]
                                                        : vlSelfRef.L1DCache__DOT__data_ram_w1
                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][2U])))))));
            __Vtemp_10[0U] = ((((((((2U & (((vlSelfRef.L1DCache__DOT__ram_be_w0[1U] 
                                             >> 0x0000001fU)
                                             ? (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                >> 0x0000001fU)
                                             : (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                >> 0x0000001fU)) 
                                           << 1U)) 
                                    | (1U & ((0x40000000U 
                                              & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                              ? (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                 >> 0x0000001eU)
                                              : (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                 [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                 >> 0x0000001eU)))) 
                                   << 6U) | (((2U & 
                                               (((0x20000000U 
                                                  & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                                  ? 
                                                 (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                  >> 0x0000001dU)
                                                  : 
                                                 (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                  [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                  >> 0x0000001dU)) 
                                                << 1U)) 
                                              | (1U 
                                                 & ((0x10000000U 
                                                     & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                                     ? 
                                                    (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                     >> 0x0000001cU)
                                                     : 
                                                    (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                     >> 0x0000001cU)))) 
                                             << 4U)) 
                                 | ((((2U & (((0x08000000U 
                                               & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                               ? (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                  >> 0x0000001bU)
                                               : (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                  [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                  >> 0x0000001bU)) 
                                             << 1U)) 
                                      | (1U & ((0x04000000U 
                                                & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                                ? (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                   >> 0x0000001aU)
                                                : (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                   [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                   >> 0x0000001aU)))) 
                                     << 2U) | ((2U 
                                                & (((0x02000000U 
                                                     & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                                     ? 
                                                    (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                     >> 0x00000019U)
                                                     : 
                                                    (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                     >> 0x00000019U)) 
                                                   << 1U)) 
                                               | (1U 
                                                  & ((0x01000000U 
                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                                      ? 
                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                      >> 0x00000018U)
                                                      : 
                                                     (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                      >> 0x00000018U)))))) 
                                << 0x00000018U) | (
                                                   (((((2U 
                                                        & (((0x00800000U 
                                                             & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                                             ? 
                                                            (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                             >> 0x00000017U)
                                                             : 
                                                            (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                             [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                             >> 0x00000017U)) 
                                                           << 1U)) 
                                                       | (1U 
                                                          & ((0x00400000U 
                                                              & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                                              ? 
                                                             (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                              >> 0x00000016U)
                                                              : 
                                                             (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                              [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                              >> 0x00000016U)))) 
                                                      << 6U) 
                                                     | (((2U 
                                                          & (((0x00200000U 
                                                               & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                                               ? 
                                                              (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                               >> 0x00000015U)
                                                               : 
                                                              (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                               [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                               >> 0x00000015U)) 
                                                             << 1U)) 
                                                         | (1U 
                                                            & ((0x00100000U 
                                                                & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                                                ? 
                                                               (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                                >> 0x00000014U)
                                                                : 
                                                               (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                                >> 0x00000014U)))) 
                                                        << 4U)) 
                                                    | ((((2U 
                                                          & (((0x00080000U 
                                                               & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                                               ? 
                                                              (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                               >> 0x00000013U)
                                                               : 
                                                              (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                               [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                               >> 0x00000013U)) 
                                                             << 1U)) 
                                                         | (1U 
                                                            & ((0x00040000U 
                                                                & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                                                ? 
                                                               (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                                >> 0x00000012U)
                                                                : 
                                                               (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                                >> 0x00000012U)))) 
                                                        << 2U) 
                                                       | ((2U 
                                                           & (((0x00020000U 
                                                                & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                                                ? 
                                                               (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                                >> 0x00000011U)
                                                                : 
                                                               (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                                >> 0x00000011U)) 
                                                              << 1U)) 
                                                          | (1U 
                                                             & ((0x00010000U 
                                                                 & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                                                 ? 
                                                                (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                                 >> 0x00000010U)
                                                                 : 
                                                                (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                                 [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                                 >> 0x00000010U)))))) 
                                                   << 0x00000010U)) 
                              | (((((((2U & (((0x00008000U 
                                               & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                               ? (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                  >> 0x0000000fU)
                                               : (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                  [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                  >> 0x0000000fU)) 
                                             << 1U)) 
                                      | (1U & ((0x00004000U 
                                                & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                                ? (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                   >> 0x0000000eU)
                                                : (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                   [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                   >> 0x0000000eU)))) 
                                     << 6U) | (((2U 
                                                 & (((0x00002000U 
                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                                      ? 
                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                      >> 0x0000000dU)
                                                      : 
                                                     (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                      >> 0x0000000dU)) 
                                                    << 1U)) 
                                                | (1U 
                                                   & ((0x00001000U 
                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                                       ? 
                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                       >> 0x0000000cU)
                                                       : 
                                                      (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                       >> 0x0000000cU)))) 
                                               << 4U)) 
                                   | ((((2U & (((0x00000800U 
                                                 & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                                 ? 
                                                (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                 >> 0x0000000bU)
                                                 : 
                                                (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                 [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                 >> 0x0000000bU)) 
                                               << 1U)) 
                                        | (1U & ((0x00000400U 
                                                  & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                                  ? 
                                                 (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                  >> 0x0000000aU)
                                                  : 
                                                 (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                  [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                  >> 0x0000000aU)))) 
                                       << 2U) | ((2U 
                                                  & (((0x00000200U 
                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                                       ? 
                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                       >> 9U)
                                                       : 
                                                      (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                       >> 9U)) 
                                                     << 1U)) 
                                                 | (1U 
                                                    & ((0x00000100U 
                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                                        ? 
                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                        >> 8U)
                                                        : 
                                                       (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                        >> 8U)))))) 
                                  << 8U) | (((((2U 
                                                & (((0x00000080U 
                                                     & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                                     ? 
                                                    (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                     >> 7U)
                                                     : 
                                                    (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                     >> 7U)) 
                                                   << 1U)) 
                                               | (1U 
                                                  & ((0x00000040U 
                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                                      ? 
                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                      >> 6U)
                                                      : 
                                                     (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                      >> 6U)))) 
                                              << 6U) 
                                             | (((2U 
                                                  & (((0x00000020U 
                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                                       ? 
                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                       >> 5U)
                                                       : 
                                                      (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                       >> 5U)) 
                                                     << 1U)) 
                                                 | (1U 
                                                    & ((0x00000010U 
                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                                        ? 
                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                        >> 4U)
                                                        : 
                                                       (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                        >> 4U)))) 
                                                << 4U)) 
                                            | ((((2U 
                                                  & (((8U 
                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                                       ? 
                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                       >> 3U)
                                                       : 
                                                      (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                       >> 3U)) 
                                                     << 1U)) 
                                                 | (1U 
                                                    & ((4U 
                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                                        ? 
                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                        >> 2U)
                                                        : 
                                                       (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                        >> 2U)))) 
                                                << 2U) 
                                               | ((2U 
                                                   & (((2U 
                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                                        ? 
                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[1U] 
                                                        >> 1U)
                                                        : 
                                                       (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][1U] 
                                                        >> 1U)) 
                                                      << 1U)) 
                                                  | (1U 
                                                     & ((1U 
                                                         & vlSelfRef.L1DCache__DOT__ram_be_w0[1U])
                                                         ? vlSelfRef.L1DCache__DOT__wr_data_w0[1U]
                                                         : vlSelfRef.L1DCache__DOT__data_ram_w1
                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][1U])))))));
            __VdlyVal__L1DCache__DOT__data_ram_w1__v0[0U] 
                = ((((((((2U & (((vlSelfRef.L1DCache__DOT__ram_be_w0[0U] 
                                  >> 0x0000001fU) ? 
                                 (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                  >> 0x0000001fU) : 
                                 (vlSelfRef.L1DCache__DOT__data_ram_w1
                                  [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                  >> 0x0000001fU)) 
                                << 1U)) | (1U & ((0x40000000U 
                                                  & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                                  ? 
                                                 (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                                  >> 0x0000001eU)
                                                  : 
                                                 (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                  [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                                  >> 0x0000001eU)))) 
                        << 6U) | (((2U & (((0x20000000U 
                                            & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                            ? (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                               >> 0x0000001dU)
                                            : (vlSelfRef.L1DCache__DOT__data_ram_w1
                                               [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                               >> 0x0000001dU)) 
                                          << 1U)) | 
                                   (1U & ((0x10000000U 
                                           & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                           ? (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                              >> 0x0000001cU)
                                           : (vlSelfRef.L1DCache__DOT__data_ram_w1
                                              [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                              >> 0x0000001cU)))) 
                                  << 4U)) | ((((2U 
                                                & (((0x08000000U 
                                                     & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                                     ? 
                                                    (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                                     >> 0x0000001bU)
                                                     : 
                                                    (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                                     >> 0x0000001bU)) 
                                                   << 1U)) 
                                               | (1U 
                                                  & ((0x04000000U 
                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                                      ? 
                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                                      >> 0x0000001aU)
                                                      : 
                                                     (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                                      >> 0x0000001aU)))) 
                                              << 2U) 
                                             | ((2U 
                                                 & (((0x02000000U 
                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                                      ? 
                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                                      >> 0x00000019U)
                                                      : 
                                                     (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                                      >> 0x00000019U)) 
                                                    << 1U)) 
                                                | (1U 
                                                   & ((0x01000000U 
                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                                       ? 
                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                                       >> 0x00000018U)
                                                       : 
                                                      (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                                       >> 0x00000018U)))))) 
                     << 0x00000018U) | ((((((2U & (
                                                   ((0x00800000U 
                                                     & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                                     ? 
                                                    (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                                     >> 0x00000017U)
                                                     : 
                                                    (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                                     >> 0x00000017U)) 
                                                   << 1U)) 
                                            | (1U & 
                                               ((0x00400000U 
                                                 & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                                 ? 
                                                (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                                 >> 0x00000016U)
                                                 : 
                                                (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                 [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                                 >> 0x00000016U)))) 
                                           << 6U) | 
                                          (((2U & (
                                                   ((0x00200000U 
                                                     & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                                     ? 
                                                    (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                                     >> 0x00000015U)
                                                     : 
                                                    (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                                     >> 0x00000015U)) 
                                                   << 1U)) 
                                            | (1U & 
                                               ((0x00100000U 
                                                 & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                                 ? 
                                                (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                                 >> 0x00000014U)
                                                 : 
                                                (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                 [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                                 >> 0x00000014U)))) 
                                           << 4U)) 
                                         | ((((2U & 
                                               (((0x00080000U 
                                                  & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                                  ? 
                                                 (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                                  >> 0x00000013U)
                                                  : 
                                                 (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                  [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                                  >> 0x00000013U)) 
                                                << 1U)) 
                                              | (1U 
                                                 & ((0x00040000U 
                                                     & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                                     ? 
                                                    (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                                     >> 0x00000012U)
                                                     : 
                                                    (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                                     >> 0x00000012U)))) 
                                             << 2U) 
                                            | ((2U 
                                                & (((0x00020000U 
                                                     & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                                     ? 
                                                    (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                                     >> 0x00000011U)
                                                     : 
                                                    (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                                     >> 0x00000011U)) 
                                                   << 1U)) 
                                               | (1U 
                                                  & ((0x00010000U 
                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                                      ? 
                                                     (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                                      >> 0x00000010U)
                                                      : 
                                                     (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                      [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                                      >> 0x00000010U)))))) 
                                        << 0x00000010U)) 
                   | (((((((2U & (((0x00008000U & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                    ? (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                       >> 0x0000000fU)
                                    : (vlSelfRef.L1DCache__DOT__data_ram_w1
                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                       >> 0x0000000fU)) 
                                  << 1U)) | (1U & (
                                                   (0x00004000U 
                                                    & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                                    ? 
                                                   (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                                    >> 0x0000000eU)
                                                    : 
                                                   (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                    [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                                    >> 0x0000000eU)))) 
                          << 6U) | (((2U & (((0x00002000U 
                                              & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                              ? (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                                 >> 0x0000000dU)
                                              : (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                 [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                                 >> 0x0000000dU)) 
                                            << 1U)) 
                                     | (1U & ((0x00001000U 
                                               & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                               ? (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                                  >> 0x0000000cU)
                                               : (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                  [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                                  >> 0x0000000cU)))) 
                                    << 4U)) | ((((2U 
                                                  & (((0x00000800U 
                                                       & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                                       ? 
                                                      (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                                       >> 0x0000000bU)
                                                       : 
                                                      (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                       [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                                       >> 0x0000000bU)) 
                                                     << 1U)) 
                                                 | (1U 
                                                    & ((0x00000400U 
                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                                        ? 
                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                                        >> 0x0000000aU)
                                                        : 
                                                       (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                                        >> 0x0000000aU)))) 
                                                << 2U) 
                                               | ((2U 
                                                   & (((0x00000200U 
                                                        & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                                        ? 
                                                       (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                                        >> 9U)
                                                        : 
                                                       (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                        [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                                        >> 9U)) 
                                                      << 1U)) 
                                                  | (1U 
                                                     & ((0x00000100U 
                                                         & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                                         ? 
                                                        (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                                         >> 8U)
                                                         : 
                                                        (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                         [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                                         >> 8U)))))) 
                       << 8U) | (((((2U & (((0x00000080U 
                                             & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                             ? (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                                >> 7U)
                                             : (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                                >> 7U)) 
                                           << 1U)) 
                                    | (1U & ((0x00000040U 
                                              & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                              ? (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                                 >> 6U)
                                              : (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                 [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                                 >> 6U)))) 
                                   << 6U) | (((2U & 
                                               (((0x00000020U 
                                                  & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                                  ? 
                                                 (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                                  >> 5U)
                                                  : 
                                                 (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                  [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                                  >> 5U)) 
                                                << 1U)) 
                                              | (1U 
                                                 & ((0x00000010U 
                                                     & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                                     ? 
                                                    (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                                     >> 4U)
                                                     : 
                                                    (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                                     >> 4U)))) 
                                             << 4U)) 
                                 | ((((2U & (((8U & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                               ? (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                                  >> 3U)
                                               : (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                  [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                                  >> 3U)) 
                                             << 1U)) 
                                      | (1U & ((4U 
                                                & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                                ? (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                                   >> 2U)
                                                : (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                   [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                                   >> 2U)))) 
                                     << 2U) | ((2U 
                                                & (((2U 
                                                     & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                                     ? 
                                                    (vlSelfRef.L1DCache__DOT__wr_data_w0[0U] 
                                                     >> 1U)
                                                     : 
                                                    (vlSelfRef.L1DCache__DOT__data_ram_w1
                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][0U] 
                                                     >> 1U)) 
                                                   << 1U)) 
                                               | (1U 
                                                  & ((1U 
                                                      & vlSelfRef.L1DCache__DOT__ram_be_w0[0U])
                                                      ? vlSelfRef.L1DCache__DOT__wr_data_w0[0U]
                                                      : vlSelfRef.L1DCache__DOT__data_ram_w1
                                                     [vlSelfRef.L1DCache__DOT__data_rd_addr][0U])))))));
            __VdlyVal__L1DCache__DOT__data_ram_w1__v0[1U] 
                = __Vtemp_10[0U];
            __VdlyVal__L1DCache__DOT__data_ram_w1__v0[2U] 
                = __Vtemp_9[0U];
            __VdlyVal__L1DCache__DOT__data_ram_w1__v0[3U] 
                = __Vtemp_8[0U];
            __VdlyVal__L1DCache__DOT__data_ram_w1__v0[4U] 
                = __Vtemp_7[0U];
            __VdlyVal__L1DCache__DOT__data_ram_w1__v0[5U] 
                = __Vtemp_6[0U];
            __VdlyVal__L1DCache__DOT__data_ram_w1__v0[6U] 
                = __Vtemp_6[1U];
            __VdlyVal__L1DCache__DOT__data_ram_w1__v0[7U] 
                = __Vtemp_6[2U];
        }
        __VdlyDim0__L1DCache__DOT__data_ram_w1__v0 
            = vlSelfRef.L1DCache__DOT__data_wr_addr_w0;
        __VdlySet__L1DCache__DOT__data_ram_w1__v0 = 1U;
    }
    if (__VdlySet__L1DCache__DOT__data_ram_w0__v0) {
        vlSelfRef.L1DCache__DOT__data_ram_w0[__VdlyDim0__L1DCache__DOT__data_ram_w0__v0][0U] 
            = __VdlyVal__L1DCache__DOT__data_ram_w0__v0[0U];
        vlSelfRef.L1DCache__DOT__data_ram_w0[__VdlyDim0__L1DCache__DOT__data_ram_w0__v0][1U] 
            = __VdlyVal__L1DCache__DOT__data_ram_w0__v0[1U];
        vlSelfRef.L1DCache__DOT__data_ram_w0[__VdlyDim0__L1DCache__DOT__data_ram_w0__v0][2U] 
            = __VdlyVal__L1DCache__DOT__data_ram_w0__v0[2U];
        vlSelfRef.L1DCache__DOT__data_ram_w0[__VdlyDim0__L1DCache__DOT__data_ram_w0__v0][3U] 
            = __VdlyVal__L1DCache__DOT__data_ram_w0__v0[3U];
        vlSelfRef.L1DCache__DOT__data_ram_w0[__VdlyDim0__L1DCache__DOT__data_ram_w0__v0][4U] 
            = __VdlyVal__L1DCache__DOT__data_ram_w0__v0[4U];
        vlSelfRef.L1DCache__DOT__data_ram_w0[__VdlyDim0__L1DCache__DOT__data_ram_w0__v0][5U] 
            = __VdlyVal__L1DCache__DOT__data_ram_w0__v0[5U];
        vlSelfRef.L1DCache__DOT__data_ram_w0[__VdlyDim0__L1DCache__DOT__data_ram_w0__v0][6U] 
            = __VdlyVal__L1DCache__DOT__data_ram_w0__v0[6U];
        vlSelfRef.L1DCache__DOT__data_ram_w0[__VdlyDim0__L1DCache__DOT__data_ram_w0__v0][7U] 
            = __VdlyVal__L1DCache__DOT__data_ram_w0__v0[7U];
    }
    if (__VdlySet__L1DCache__DOT__data_ram_w1__v0) {
        vlSelfRef.L1DCache__DOT__data_ram_w1[__VdlyDim0__L1DCache__DOT__data_ram_w1__v0][0U] 
            = __VdlyVal__L1DCache__DOT__data_ram_w1__v0[0U];
        vlSelfRef.L1DCache__DOT__data_ram_w1[__VdlyDim0__L1DCache__DOT__data_ram_w1__v0][1U] 
            = __VdlyVal__L1DCache__DOT__data_ram_w1__v0[1U];
        vlSelfRef.L1DCache__DOT__data_ram_w1[__VdlyDim0__L1DCache__DOT__data_ram_w1__v0][2U] 
            = __VdlyVal__L1DCache__DOT__data_ram_w1__v0[2U];
        vlSelfRef.L1DCache__DOT__data_ram_w1[__VdlyDim0__L1DCache__DOT__data_ram_w1__v0][3U] 
            = __VdlyVal__L1DCache__DOT__data_ram_w1__v0[3U];
        vlSelfRef.L1DCache__DOT__data_ram_w1[__VdlyDim0__L1DCache__DOT__data_ram_w1__v0][4U] 
            = __VdlyVal__L1DCache__DOT__data_ram_w1__v0[4U];
        vlSelfRef.L1DCache__DOT__data_ram_w1[__VdlyDim0__L1DCache__DOT__data_ram_w1__v0][5U] 
            = __VdlyVal__L1DCache__DOT__data_ram_w1__v0[5U];
        vlSelfRef.L1DCache__DOT__data_ram_w1[__VdlyDim0__L1DCache__DOT__data_ram_w1__v0][6U] 
            = __VdlyVal__L1DCache__DOT__data_ram_w1__v0[6U];
        vlSelfRef.L1DCache__DOT__data_ram_w1[__VdlyDim0__L1DCache__DOT__data_ram_w1__v0][7U] 
            = __VdlyVal__L1DCache__DOT__data_ram_w1__v0[7U];
    }
}

void VL1DCache___024root___nba_sequent__TOP__2(VL1DCache___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VL1DCache___024root___nba_sequent__TOP__2\n"); );
    VL1DCache__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Locals
    IData/*24:0*/ L1DCache__DOT__sel_tag_w0;
    L1DCache__DOT__sel_tag_w0 = 0;
    IData/*24:0*/ L1DCache__DOT__sel_tag_w1;
    L1DCache__DOT__sel_tag_w1 = 0;
    IData/*24:0*/ L1DCache__DOT__u_tag_cmp_w1__DOT__diff;
    L1DCache__DOT__u_tag_cmp_w1__DOT__diff = 0;
    SData/*11:0*/ L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0;
    L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0 = 0;
    IData/*24:0*/ L1DCache__DOT__u_tag_cmp_w0__DOT__diff;
    L1DCache__DOT__u_tag_cmp_w0__DOT__diff = 0;
    SData/*11:0*/ L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0;
    L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0 = 0;
    // Body
    vlSelfRef.L1DCache__DOT__pend_victim_q_reg = vlSelfRef.__Vdly__L1DCache__DOT__pend_victim_q_reg;
    vlSelfRef.L1DCache__DOT__refill_done = ((IData)(vlSelfRef.refill_valid) 
                                            & (IData)(vlSelfRef.L1DCache__DOT__is_refill_wait));
    vlSelfRef.L1DCache__DOT__data_rd_addr = (3U & ((IData)(vlSelfRef.wb_valid)
                                                    ? 
                                                   (vlSelfRef.L1DCache__DOT__pend_q_reg 
                                                    >> 5U)
                                                    : 
                                                   (vlSelfRef.req_addr 
                                                    >> 5U)));
    vlSelfRef.L1DCache__DOT__rfs_0 = ((- (IData)((IData)(vlSelfRef.L1DCache__DOT__refill_done))) 
                                      & (((0x0000000cU 
                                           & ((- (IData)(
                                                         (1U 
                                                          & (vlSelfRef.L1DCache__DOT__pend_q_reg 
                                                             >> 6U)))) 
                                              << 2U)) 
                                          | (3U & (- (IData)(
                                                             (1U 
                                                              & (~ 
                                                                 (vlSelfRef.L1DCache__DOT__pend_q_reg 
                                                                  >> 6U))))))) 
                                         & ((((2U & 
                                               (vlSelfRef.L1DCache__DOT__pend_q_reg 
                                                >> 4U)) 
                                              | (1U 
                                                 & (~ 
                                                    (vlSelfRef.L1DCache__DOT__pend_q_reg 
                                                     >> 5U)))) 
                                             << 2U) 
                                            | ((2U 
                                                & (vlSelfRef.L1DCache__DOT__pend_q_reg 
                                                   >> 4U)) 
                                               | (1U 
                                                  & (~ 
                                                     (vlSelfRef.L1DCache__DOT__pend_q_reg 
                                                      >> 5U)))))));
    L1DCache__DOT__sel_tag_w0 = (((~ (- (IData)((1U 
                                                 & ((IData)(vlSelfRef.L1DCache__DOT__data_rd_addr) 
                                                    >> 1U))))) 
                                  & (((~ (- (IData)(
                                                    (1U 
                                                     & (IData)(vlSelfRef.L1DCache__DOT__data_rd_addr))))) 
                                      & vlSelfRef.L1DCache__DOT__tag_q_w0_s0) 
                                     | (vlSelfRef.L1DCache__DOT__tag_q_w0_s1 
                                        & (- (IData)(
                                                     (1U 
                                                      & (IData)(vlSelfRef.L1DCache__DOT__data_rd_addr))))))) 
                                 | ((- (IData)((1U 
                                                & ((IData)(vlSelfRef.L1DCache__DOT__data_rd_addr) 
                                                   >> 1U)))) 
                                    & (((~ (- (IData)(
                                                      (1U 
                                                       & (IData)(vlSelfRef.L1DCache__DOT__data_rd_addr))))) 
                                        & vlSelfRef.L1DCache__DOT__tag_q_w0_s2) 
                                       | (vlSelfRef.L1DCache__DOT__tag_q_w0_s3 
                                          & (- (IData)(
                                                       (1U 
                                                        & (IData)(vlSelfRef.L1DCache__DOT__data_rd_addr))))))));
    L1DCache__DOT__sel_tag_w1 = (((~ (- (IData)((1U 
                                                 & ((IData)(vlSelfRef.L1DCache__DOT__data_rd_addr) 
                                                    >> 1U))))) 
                                  & (((~ (- (IData)(
                                                    (1U 
                                                     & (IData)(vlSelfRef.L1DCache__DOT__data_rd_addr))))) 
                                      & vlSelfRef.L1DCache__DOT__tag_q_w1_s0) 
                                     | (vlSelfRef.L1DCache__DOT__tag_q_w1_s1 
                                        & (- (IData)(
                                                     (1U 
                                                      & (IData)(vlSelfRef.L1DCache__DOT__data_rd_addr))))))) 
                                 | ((((~ (- (IData)(
                                                    (1U 
                                                     & (IData)(vlSelfRef.L1DCache__DOT__data_rd_addr))))) 
                                      & vlSelfRef.L1DCache__DOT__tag_q_w1_s2) 
                                     | (vlSelfRef.L1DCache__DOT__tag_q_w1_s3 
                                        & (- (IData)(
                                                     (1U 
                                                      & (IData)(vlSelfRef.L1DCache__DOT__data_rd_addr)))))) 
                                    & (- (IData)((1U 
                                                  & ((IData)(vlSelfRef.L1DCache__DOT__data_rd_addr) 
                                                     >> 1U))))));
    vlSelfRef.L1DCache__DOT__rfe_0 = ((- (IData)((1U 
                                                  & (~ (IData)(vlSelfRef.L1DCache__DOT__pend_victim_q_reg))))) 
                                      & (IData)(vlSelfRef.L1DCache__DOT__rfs_0));
    vlSelfRef.L1DCache__DOT__rfe_1 = ((- (IData)((IData)(vlSelfRef.L1DCache__DOT__pend_victim_q_reg))) 
                                      & (IData)(vlSelfRef.L1DCache__DOT__rfs_0));
    L1DCache__DOT__u_tag_cmp_w0__DOT__diff = (0x01ffffffU 
                                              & ((vlSelfRef.req_addr 
                                                  >> 7U) 
                                                 ^ L1DCache__DOT__sel_tag_w0));
    vlSelfRef.wb_addr = ((((IData)(vlSelfRef.L1DCache__DOT__pend_victim_q_reg)
                            ? L1DCache__DOT__sel_tag_w1
                            : L1DCache__DOT__sel_tag_w0) 
                          << 7U) | ((IData)(vlSelfRef.L1DCache__DOT__data_rd_addr) 
                                    << 5U));
    L1DCache__DOT__u_tag_cmp_w1__DOT__diff = (0x01ffffffU 
                                              & ((vlSelfRef.req_addr 
                                                  >> 7U) 
                                                 ^ L1DCache__DOT__sel_tag_w1));
    L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0 
        = ((((((4U & (L1DCache__DOT__u_tag_cmp_w0__DOT__diff 
                      >> 0x00000014U)) | ((2U & (L1DCache__DOT__u_tag_cmp_w0__DOT__diff 
                                                 >> 0x00000013U)) 
                                          | (1U & (L1DCache__DOT__u_tag_cmp_w0__DOT__diff 
                                                   >> 0x00000012U)))) 
              << 9U) | (((4U & (L1DCache__DOT__u_tag_cmp_w0__DOT__diff 
                                >> 0x0000000eU)) | 
                         ((2U & (L1DCache__DOT__u_tag_cmp_w0__DOT__diff 
                                 >> 0x0000000dU)) | 
                          (1U & (L1DCache__DOT__u_tag_cmp_w0__DOT__diff 
                                 >> 0x0000000cU)))) 
                        << 6U)) | ((((4U & (L1DCache__DOT__u_tag_cmp_w0__DOT__diff 
                                            >> 8U)) 
                                     | ((2U & (L1DCache__DOT__u_tag_cmp_w0__DOT__diff 
                                               >> 7U)) 
                                        | (1U & (L1DCache__DOT__u_tag_cmp_w0__DOT__diff 
                                                 >> 6U)))) 
                                    << 3U) | ((4U & 
                                               (L1DCache__DOT__u_tag_cmp_w0__DOT__diff 
                                                >> 2U)) 
                                              | ((2U 
                                                  & (L1DCache__DOT__u_tag_cmp_w0__DOT__diff 
                                                     >> 1U)) 
                                                 | (1U 
                                                    & L1DCache__DOT__u_tag_cmp_w0__DOT__diff))))) 
           | (((((4U & (L1DCache__DOT__u_tag_cmp_w0__DOT__diff 
                        >> 0x00000015U)) | ((2U & (L1DCache__DOT__u_tag_cmp_w0__DOT__diff 
                                                   >> 0x00000014U)) 
                                            | (1U & 
                                               (L1DCache__DOT__u_tag_cmp_w0__DOT__diff 
                                                >> 0x00000013U)))) 
                << 9U) | (((4U & (L1DCache__DOT__u_tag_cmp_w0__DOT__diff 
                                  >> 0x0000000fU)) 
                           | ((2U & (L1DCache__DOT__u_tag_cmp_w0__DOT__diff 
                                     >> 0x0000000eU)) 
                              | (1U & (L1DCache__DOT__u_tag_cmp_w0__DOT__diff 
                                       >> 0x0000000dU)))) 
                          << 6U)) | ((((4U & (L1DCache__DOT__u_tag_cmp_w0__DOT__diff 
                                              >> 9U)) 
                                       | ((2U & (L1DCache__DOT__u_tag_cmp_w0__DOT__diff 
                                                 >> 8U)) 
                                          | (1U & (L1DCache__DOT__u_tag_cmp_w0__DOT__diff 
                                                   >> 7U)))) 
                                      << 3U) | ((4U 
                                                 & (L1DCache__DOT__u_tag_cmp_w0__DOT__diff 
                                                    >> 3U)) 
                                                | ((2U 
                                                    & (L1DCache__DOT__u_tag_cmp_w0__DOT__diff 
                                                       >> 2U)) 
                                                   | (1U 
                                                      & (L1DCache__DOT__u_tag_cmp_w0__DOT__diff 
                                                         >> 1U)))))));
    L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0 
        = ((((((4U & (L1DCache__DOT__u_tag_cmp_w1__DOT__diff 
                      >> 0x00000014U)) | ((2U & (L1DCache__DOT__u_tag_cmp_w1__DOT__diff 
                                                 >> 0x00000013U)) 
                                          | (1U & (L1DCache__DOT__u_tag_cmp_w1__DOT__diff 
                                                   >> 0x00000012U)))) 
              << 9U) | (((4U & (L1DCache__DOT__u_tag_cmp_w1__DOT__diff 
                                >> 0x0000000eU)) | 
                         ((2U & (L1DCache__DOT__u_tag_cmp_w1__DOT__diff 
                                 >> 0x0000000dU)) | 
                          (1U & (L1DCache__DOT__u_tag_cmp_w1__DOT__diff 
                                 >> 0x0000000cU)))) 
                        << 6U)) | ((((4U & (L1DCache__DOT__u_tag_cmp_w1__DOT__diff 
                                            >> 8U)) 
                                     | ((2U & (L1DCache__DOT__u_tag_cmp_w1__DOT__diff 
                                               >> 7U)) 
                                        | (1U & (L1DCache__DOT__u_tag_cmp_w1__DOT__diff 
                                                 >> 6U)))) 
                                    << 3U) | ((4U & 
                                               (L1DCache__DOT__u_tag_cmp_w1__DOT__diff 
                                                >> 2U)) 
                                              | ((2U 
                                                  & (L1DCache__DOT__u_tag_cmp_w1__DOT__diff 
                                                     >> 1U)) 
                                                 | (1U 
                                                    & L1DCache__DOT__u_tag_cmp_w1__DOT__diff))))) 
           | (((((4U & (L1DCache__DOT__u_tag_cmp_w1__DOT__diff 
                        >> 0x00000015U)) | ((2U & (L1DCache__DOT__u_tag_cmp_w1__DOT__diff 
                                                   >> 0x00000014U)) 
                                            | (1U & 
                                               (L1DCache__DOT__u_tag_cmp_w1__DOT__diff 
                                                >> 0x00000013U)))) 
                << 9U) | (((4U & (L1DCache__DOT__u_tag_cmp_w1__DOT__diff 
                                  >> 0x0000000fU)) 
                           | ((2U & (L1DCache__DOT__u_tag_cmp_w1__DOT__diff 
                                     >> 0x0000000eU)) 
                              | (1U & (L1DCache__DOT__u_tag_cmp_w1__DOT__diff 
                                       >> 0x0000000dU)))) 
                          << 6U)) | ((((4U & (L1DCache__DOT__u_tag_cmp_w1__DOT__diff 
                                              >> 9U)) 
                                       | ((2U & (L1DCache__DOT__u_tag_cmp_w1__DOT__diff 
                                                 >> 8U)) 
                                          | (1U & (L1DCache__DOT__u_tag_cmp_w1__DOT__diff 
                                                   >> 7U)))) 
                                      << 3U) | ((4U 
                                                 & (L1DCache__DOT__u_tag_cmp_w1__DOT__diff 
                                                    >> 3U)) 
                                                | ((2U 
                                                    & (L1DCache__DOT__u_tag_cmp_w1__DOT__diff 
                                                       >> 2U)) 
                                                   | (1U 
                                                      & (L1DCache__DOT__u_tag_cmp_w1__DOT__diff 
                                                         >> 1U)))))));
    vlSelfRef.L1DCache__DOT__way1_hit = ((~ ((VL1DCache__ConstPool__TABLE_h8d06dde6_0
                                              [((((
                                                   (4U 
                                                    & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                       >> 8U)) 
                                                   | ((2U 
                                                       & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                          >> 7U)) 
                                                      | (1U 
                                                         & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                            >> 6U)))) 
                                                  << 3U) 
                                                 | ((4U 
                                                     & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                        >> 2U)) 
                                                    | ((2U 
                                                        & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                           >> 1U)) 
                                                       | (1U 
                                                          & (IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0))))) 
                                                | ((((4U 
                                                      & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                         >> 9U)) 
                                                     | ((2U 
                                                         & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                            >> 8U)) 
                                                        | (1U 
                                                           & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                              >> 7U)))) 
                                                    << 3U) 
                                                   | ((4U 
                                                       & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                          >> 3U)) 
                                                      | ((2U 
                                                          & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                             >> 2U)) 
                                                         | (1U 
                                                            & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                               >> 1U))))))] 
                                              >> 2U) 
                                             | (VL1DCache__ConstPool__TABLE_h8d06dde6_0
                                                [((
                                                   (((4U 
                                                      & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                         >> 8U)) 
                                                     | ((2U 
                                                         & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                            >> 7U)) 
                                                        | (1U 
                                                           & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                              >> 6U)))) 
                                                    << 3U) 
                                                   | ((4U 
                                                       & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                          >> 2U)) 
                                                      | ((2U 
                                                          & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                             >> 1U)) 
                                                         | (1U 
                                                            & (IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0))))) 
                                                  | ((((4U 
                                                        & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                           >> 9U)) 
                                                       | ((2U 
                                                           & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                              >> 8U)) 
                                                          | (1U 
                                                             & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                                >> 7U)))) 
                                                      << 3U) 
                                                     | ((4U 
                                                         & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                            >> 3U)) 
                                                        | ((2U 
                                                            & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                               >> 2U)) 
                                                           | (1U 
                                                              & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                                 >> 1U))))))] 
                                                | ((L1DCache__DOT__u_tag_cmp_w1__DOT__diff 
                                                    >> 0x00000018U) 
                                                   | (VL1DCache__ConstPool__TABLE_h8d06dde6_0
                                                      [
                                                      (((((4U 
                                                           & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                              >> 8U)) 
                                                          | ((2U 
                                                              & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                                 >> 7U)) 
                                                             | (1U 
                                                                & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                                   >> 6U)))) 
                                                         << 3U) 
                                                        | ((4U 
                                                            & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                               >> 2U)) 
                                                           | ((2U 
                                                               & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                                  >> 1U)) 
                                                              | (1U 
                                                                 & (IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0))))) 
                                                       | ((((4U 
                                                             & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                                >> 9U)) 
                                                            | ((2U 
                                                                & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                                   >> 8U)) 
                                                               | (1U 
                                                                  & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                                     >> 7U)))) 
                                                           << 3U) 
                                                          | ((4U 
                                                              & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                                 >> 3U)) 
                                                             | ((2U 
                                                                 & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                                    >> 2U)) 
                                                                | (1U 
                                                                   & ((IData)(L1DCache__DOT__u_tag_cmp_w1__DOT__or_t_any_diff_l0) 
                                                                      >> 1U))))))] 
                                                      >> 1U))))) 
                                         & (IData)(vlSelfRef.L1DCache__DOT__way1_valid_sel));
    if (vlSelfRef.L1DCache__DOT__refill_done) {
        vlSelfRef.L1DCache__DOT__data_wr_addr_w0 = 
            (3U & (vlSelfRef.L1DCache__DOT__pend_q_reg 
                   >> 5U));
        vlSelfRef.L1DCache__DOT__lru_nv = (0x0000000fU 
                                           & (- (IData)(
                                                        (1U 
                                                         & (~ (IData)(vlSelfRef.L1DCache__DOT__pend_victim_q_reg))))));
    } else {
        vlSelfRef.L1DCache__DOT__data_wr_addr_w0 = 
            (3U & (vlSelfRef.req_addr >> 5U));
        vlSelfRef.L1DCache__DOT__lru_nv = (0x0000000fU 
                                           & (- (IData)(
                                                        (1U 
                                                         & (~ (IData)(vlSelfRef.L1DCache__DOT__way1_hit))))));
    }
    vlSelfRef.L1DCache__DOT__hit = ((IData)(vlSelfRef.L1DCache__DOT__way1_hit) 
                                    | ((~ ((VL1DCache__ConstPool__TABLE_h8d06dde6_0
                                            [(((((4U 
                                                  & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                     >> 8U)) 
                                                 | ((2U 
                                                     & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                        >> 7U)) 
                                                    | (1U 
                                                       & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                          >> 6U)))) 
                                                << 3U) 
                                               | ((4U 
                                                   & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                      >> 2U)) 
                                                  | ((2U 
                                                      & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                         >> 1U)) 
                                                     | (1U 
                                                        & (IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0))))) 
                                              | ((((4U 
                                                    & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                       >> 9U)) 
                                                   | ((2U 
                                                       & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                          >> 8U)) 
                                                      | (1U 
                                                         & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                            >> 7U)))) 
                                                  << 3U) 
                                                 | ((4U 
                                                     & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                        >> 3U)) 
                                                    | ((2U 
                                                        & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                           >> 2U)) 
                                                       | (1U 
                                                          & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                             >> 1U))))))] 
                                            >> 2U) 
                                           | (VL1DCache__ConstPool__TABLE_h8d06dde6_0
                                              [((((
                                                   (4U 
                                                    & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                       >> 8U)) 
                                                   | ((2U 
                                                       & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                          >> 7U)) 
                                                      | (1U 
                                                         & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                            >> 6U)))) 
                                                  << 3U) 
                                                 | ((4U 
                                                     & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                        >> 2U)) 
                                                    | ((2U 
                                                        & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                           >> 1U)) 
                                                       | (1U 
                                                          & (IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0))))) 
                                                | ((((4U 
                                                      & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                         >> 9U)) 
                                                     | ((2U 
                                                         & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                            >> 8U)) 
                                                        | (1U 
                                                           & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                              >> 7U)))) 
                                                    << 3U) 
                                                   | ((4U 
                                                       & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                          >> 3U)) 
                                                      | ((2U 
                                                          & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                             >> 2U)) 
                                                         | (1U 
                                                            & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                               >> 1U))))))] 
                                              | ((L1DCache__DOT__u_tag_cmp_w0__DOT__diff 
                                                  >> 0x00000018U) 
                                                 | (VL1DCache__ConstPool__TABLE_h8d06dde6_0
                                                    [
                                                    (((((4U 
                                                         & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                            >> 8U)) 
                                                        | ((2U 
                                                            & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                               >> 7U)) 
                                                           | (1U 
                                                              & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                                 >> 6U)))) 
                                                       << 3U) 
                                                      | ((4U 
                                                          & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                             >> 2U)) 
                                                         | ((2U 
                                                             & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                                >> 1U)) 
                                                            | (1U 
                                                               & (IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0))))) 
                                                     | ((((4U 
                                                           & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                              >> 9U)) 
                                                          | ((2U 
                                                              & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                                 >> 8U)) 
                                                             | (1U 
                                                                & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                                   >> 7U)))) 
                                                         << 3U) 
                                                        | ((4U 
                                                            & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                               >> 3U)) 
                                                           | ((2U 
                                                               & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                                  >> 2U)) 
                                                              | (1U 
                                                                 & ((IData)(L1DCache__DOT__u_tag_cmp_w0__DOT__or_t_any_diff_l0) 
                                                                    >> 1U))))))] 
                                                    >> 1U))))) 
                                       & (IData)(vlSelfRef.L1DCache__DOT__way0_valid_sel)));
    vlSelfRef.L1DCache__DOT__write_hit = ((7U == (7U 
                                                  & (~ (IData)(vlSelfRef.L1DCache__DOT__fsm_q_reg)))) 
                                          & ((IData)(vlSelfRef.L1DCache__DOT__hit) 
                                             & ((IData)(vlSelfRef.req_valid) 
                                                & (IData)(vlSelfRef.req_we))));
    vlSelfRef.L1DCache__DOT__miss_detect = ((IData)(vlSelfRef.req_valid) 
                                            & ((~ (IData)(vlSelfRef.L1DCache__DOT__hit)) 
                                               & (7U 
                                                  == 
                                                  (7U 
                                                   & (~ (IData)(vlSelfRef.L1DCache__DOT__fsm_q_reg))))));
    vlSelfRef.L1DCache__DOT__whs_0 = ((- (IData)((IData)(vlSelfRef.L1DCache__DOT__write_hit))) 
                                      & (IData)(vlSelfRef.L1DCache__DOT__valid_dec_w0));
    vlSelfRef.stall = (1U & ((~ (7U == (7U & (~ (IData)(vlSelfRef.L1DCache__DOT__fsm_q_reg))))) 
                             | (IData)(vlSelfRef.L1DCache__DOT__miss_detect)));
    vlSelfRef.L1DCache__DOT__miss_detect_clean = ((~ (IData)(vlSelfRef.L1DCache__DOT__victim_needs_wb)) 
                                                  & (IData)(vlSelfRef.L1DCache__DOT__miss_detect));
    vlSelfRef.L1DCache__DOT__lru_en = ((IData)(vlSelfRef.L1DCache__DOT__rfs_0) 
                                       | (IData)(vlSelfRef.L1DCache__DOT__whs_0));
    vlSelfRef.miss_valid = ((IData)(vlSelfRef.L1DCache__DOT__is_refill_wait) 
                            | (IData)(vlSelfRef.L1DCache__DOT__miss_detect_clean));
}
