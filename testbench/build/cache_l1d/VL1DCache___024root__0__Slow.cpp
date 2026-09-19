// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VL1DCache.h for the primary calling header

#include "VL1DCache__pch.h"

VL_ATTR_COLD void VL1DCache___024root___eval_static(VL1DCache___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VL1DCache___024root___eval_static\n"); );
    VL1DCache__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
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
    vlSelfRef.__Vtrigprevexpr___TOP__clock__1 = vlSelfRef.clock;
    vlSelfRef.__Vtrigprevexpr___TOP__reset__1 = vlSelfRef.reset;
}

VL_ATTR_COLD void VL1DCache___024root___eval_initial(VL1DCache___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VL1DCache___024root___eval_initial\n"); );
    VL1DCache__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    {
        // Inlined CFunc: _eval_initial__TOP
        vlSelfRef.fence_i_busy = 0U;
    }
}

#ifdef VL_DEBUG
VL_ATTR_COLD void VL1DCache___024root___dump_triggers__stl(const VlUnpacked<QData/*63:0*/, 1> &triggers, const std::string &tag);
#endif  // VL_DEBUG
VL_ATTR_COLD bool VL1DCache___024root___trigger_anySet__stl(const VlUnpacked<QData/*63:0*/, 1> &in);
VL_ATTR_COLD void VL1DCache___024root___stl_sequent__TOP__0(VL1DCache___024root* vlSelf);

VL_ATTR_COLD bool VL1DCache___024root___eval_stl(VL1DCache___024root* vlSelf, CData/*0:0*/ firstIteration) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VL1DCache___024root___eval_stl\n"); );
    VL1DCache__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Locals
    CData/*0:0*/ __VstlExecute;
    // Body
    vlSelfRef.__VstlTriggered[0U] = ((0xfffffffffffffffeULL 
                                      & vlSelfRef.__VstlTriggered[0U]) 
                                     | (IData)((IData)(firstIteration)));
#ifdef VL_DEBUG
    if (VL_UNLIKELY(vlSymsp->_vm_contextp__->debug())) {
        VL1DCache___024root___dump_triggers__stl(vlSelfRef.__VstlTriggered, "stl"s);
    }
#endif
    __VstlExecute = VL1DCache___024root___trigger_anySet__stl(vlSelfRef.__VstlTriggered);
    if (__VstlExecute) {
        {
            // Inlined CFunc: _eval_body__stl
            if ((1ULL & vlSelfRef.__VstlTriggered[0U])) {
                VL1DCache___024root___stl_sequent__TOP__0(vlSelf);
            }
        }
    }
    return (__VstlExecute);
}

VL_ATTR_COLD void VL1DCache___024root___eval_dump_triggers__stl(VL1DCache___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VL1DCache___024root___eval_dump_triggers__stl\n"); );
    VL1DCache__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
#ifdef VL_DEBUG
    VL1DCache___024root___dump_triggers__stl(vlSelfRef.__VstlTriggered, "stl"s);
#endif
}

#ifdef VL_DEBUG
VL_ATTR_COLD void VL1DCache___024root___dump_triggers__ico(const VlUnpacked<QData/*63:0*/, 2> &triggers, const std::string &tag);
#endif  // VL_DEBUG

VL_ATTR_COLD void VL1DCache___024root___eval_dump_triggers__ico(VL1DCache___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VL1DCache___024root___eval_dump_triggers__ico\n"); );
    VL1DCache__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
#ifdef VL_DEBUG
    VL1DCache___024root___dump_triggers__ico(vlSelfRef.__VicoTriggered, "ico"s);
#endif
}

#ifdef VL_DEBUG
VL_ATTR_COLD void VL1DCache___024root___dump_triggers__act(const VlUnpacked<QData/*63:0*/, 1> &triggers, const std::string &tag);
#endif  // VL_DEBUG

VL_ATTR_COLD void VL1DCache___024root___eval_dump_triggers__act(VL1DCache___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VL1DCache___024root___eval_dump_triggers__act\n"); );
    VL1DCache__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
#ifdef VL_DEBUG
    VL1DCache___024root___dump_triggers__act(vlSelfRef.__VactTriggered, "act"s);
#endif
}

VL_ATTR_COLD void VL1DCache___024root___eval_dump_triggers__nba(VL1DCache___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VL1DCache___024root___eval_dump_triggers__nba\n"); );
    VL1DCache__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
#ifdef VL_DEBUG
    VL1DCache___024root___dump_triggers__act(vlSelfRef.__VnbaTriggered, "nba"s);
#endif
}

VL_ATTR_COLD void VL1DCache___024root___eval_dump_triggers__obs(VL1DCache___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VL1DCache___024root___eval_dump_triggers__obs\n"); );
    VL1DCache__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
}

VL_ATTR_COLD void VL1DCache___024root___eval_dump_triggers__react(VL1DCache___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VL1DCache___024root___eval_dump_triggers__react\n"); );
    VL1DCache__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
}

VL_ATTR_COLD void VL1DCache___024root___eval_final(VL1DCache___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VL1DCache___024root___eval_final\n"); );
    VL1DCache__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
}

#ifdef VL_DEBUG
VL_ATTR_COLD void VL1DCache___024root___dump_triggers__stl(const VlUnpacked<QData/*63:0*/, 1> &triggers, const std::string &tag) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VL1DCache___024root___dump_triggers__stl\n"); );
    // Body
    if ((1U & (~ (IData)(VL1DCache___024root___trigger_anySet__stl(triggers))))) {
        VL_DBG_MSGS("         No '" + tag + "' region triggers active\n");
    }
    if ((1U & (IData)(triggers[0U]))) {
        VL_DBG_MSGS("         '" + tag + "' region trigger index 0 is active: Internal 'stl' trigger - first iteration\n");
    }
}
#endif  // VL_DEBUG

VL_ATTR_COLD bool VL1DCache___024root___trigger_anySet__stl(const VlUnpacked<QData/*63:0*/, 1> &in) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VL1DCache___024root___trigger_anySet__stl\n"); );
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

extern const VlUnpacked<CData/*3:0*/, 256> VL1DCache__ConstPool__TABLE_h9783ab34_0;
extern const VlUnpacked<CData/*2:0*/, 64> VL1DCache__ConstPool__TABLE_h8d06dde6_0;

VL_ATTR_COLD void VL1DCache___024root___stl_sequent__TOP__0(VL1DCache___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VL1DCache___024root___stl_sequent__TOP__0\n"); );
    VL1DCache__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Locals
    CData/*3:0*/ L1DCache__DOT__be;
    L1DCache__DOT__be = 0;
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
    vlSelfRef.__VdfgRegularize_h6e95ff9d_0_0 = ((0x0000ff00U 
                                                 & (((3U 
                                                      == 
                                                      (3U 
                                                       & (~ (IData)(vlSelfRef.req_size))))
                                                      ? (IData)(vlSelfRef.req_wdata)
                                                      : (IData)(
                                                                (vlSelfRef.req_wdata 
                                                                 >> 8U))) 
                                                    << 8U)) 
                                                | (0x000000ffU 
                                                   & (IData)(vlSelfRef.req_wdata)));
    vlSelfRef.L1DCache__DOT__be2_h = ((vlSelfRef.req_addr 
                                       >> 1U) & (1U 
                                                 == (IData)(vlSelfRef.req_size)));
    vlSelfRef.L1DCache__DOT__is_word = (IData)((2U 
                                                == (IData)(vlSelfRef.req_size)));
    vlSelfRef.__VdfgRegularize_h6e95ff9d_0_1 = (1U 
                                                & ((~ 
                                                    (vlSelfRef.req_addr 
                                                     >> 1U)) 
                                                   & (~ 
                                                      ((IData)(vlSelfRef.req_size) 
                                                       >> 1U))));
    vlSelfRef.L1DCache__DOT__is_refill_wait = ((IData)(vlSelfRef.L1DCache__DOT__fsm_q_reg) 
                                               & (3U 
                                                  == 
                                                  (3U 
                                                   & (~ 
                                                      ((IData)(vlSelfRef.L1DCache__DOT__fsm_q_reg) 
                                                       >> 1U)))));
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
    vlSelfRef.wb_valid = (IData)((2U == (IData)(vlSelfRef.L1DCache__DOT__fsm_q_reg)));
    vlSelfRef.L1DCache__DOT__be0_h = ((IData)(vlSelfRef.req_size) 
                                      & (IData)(vlSelfRef.__VdfgRegularize_h6e95ff9d_0_1));
    vlSelfRef.miss_addr = (((IData)(vlSelfRef.L1DCache__DOT__is_refill_wait)
                             ? (vlSelfRef.L1DCache__DOT__pend_q_reg 
                                >> 5U) : (vlSelfRef.req_addr 
                                          >> 5U)) << 5U);
    vlSelfRef.L1DCache__DOT__refill_done = ((IData)(vlSelfRef.refill_valid) 
                                            & (IData)(vlSelfRef.L1DCache__DOT__is_refill_wait));
    vlSelfRef.L1DCache__DOT__victim_lru = (0U != ((IData)(vlSelfRef.L1DCache__DOT__lru_q_reg) 
                                                  & (IData)(vlSelfRef.L1DCache__DOT__valid_dec_w0)));
    vlSelfRef.L1DCache__DOT__way0_valid_sel = (0U != 
                                               ((IData)(vlSelfRef.L1DCache__DOT__valid_q_reg) 
                                                & (IData)(vlSelfRef.L1DCache__DOT__valid_dec_w0)));
    vlSelfRef.L1DCache__DOT__way1_valid_sel = (0U != 
                                               (((IData)(vlSelfRef.L1DCache__DOT__valid_q_reg) 
                                                 >> 4U) 
                                                & (IData)(vlSelfRef.L1DCache__DOT__valid_dec_w0)));
    vlSelfRef.L1DCache__DOT__data_rd_addr = (3U & ((IData)(vlSelfRef.wb_valid)
                                                    ? 
                                                   (vlSelfRef.L1DCache__DOT__pend_q_reg 
                                                    >> 5U)
                                                    : 
                                                   (vlSelfRef.req_addr 
                                                    >> 5U)));
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
        vlSelfRef.L1DCache__DOT__wr_data_w0[0U] = (IData)(vlSelfRef.req_wdata);
        vlSelfRef.L1DCache__DOT__wr_data_w0[1U] = (IData)(
                                                          (vlSelfRef.req_wdata 
                                                           >> 0x00000020U));
        vlSelfRef.L1DCache__DOT__wr_data_w0[2U] = (IData)(vlSelfRef.req_wdata);
        vlSelfRef.L1DCache__DOT__wr_data_w0[3U] = (IData)(
                                                          (vlSelfRef.req_wdata 
                                                           >> 0x00000020U));
        vlSelfRef.L1DCache__DOT__wr_data_w0[4U] = (IData)(vlSelfRef.req_wdata);
        vlSelfRef.L1DCache__DOT__wr_data_w0[5U] = (IData)(
                                                          (vlSelfRef.req_wdata 
                                                           >> 0x00000020U));
        vlSelfRef.L1DCache__DOT__wr_data_w0[6U] = (IData)(vlSelfRef.req_wdata);
        vlSelfRef.L1DCache__DOT__wr_data_w0[7U] = (IData)(
                                                          (vlSelfRef.req_wdata 
                                                           >> 0x00000020U));
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
        vlSelfRef.L1DCache__DOT__wr_data_w0[0U] = (
                                                   (((IData)(vlSelfRef.L1DCache__DOT__is_word)
                                                      ? (IData)(
                                                                (vlSelfRef.req_wdata 
                                                                 >> 0x00000010U))
                                                      : (IData)(vlSelfRef.__VdfgRegularize_h6e95ff9d_0_0)) 
                                                    << 0x00000010U) 
                                                   | (IData)(vlSelfRef.__VdfgRegularize_h6e95ff9d_0_0));
        vlSelfRef.L1DCache__DOT__wr_data_w0[1U] = (
                                                   (((IData)(vlSelfRef.L1DCache__DOT__is_word)
                                                      ? (IData)(
                                                                (vlSelfRef.req_wdata 
                                                                 >> 0x00000010U))
                                                      : (IData)(vlSelfRef.__VdfgRegularize_h6e95ff9d_0_0)) 
                                                    << 0x00000010U) 
                                                   | (IData)(vlSelfRef.__VdfgRegularize_h6e95ff9d_0_0));
        vlSelfRef.L1DCache__DOT__wr_data_w0[2U] = (
                                                   (((IData)(vlSelfRef.L1DCache__DOT__is_word)
                                                      ? (IData)(
                                                                (vlSelfRef.req_wdata 
                                                                 >> 0x00000010U))
                                                      : (IData)(vlSelfRef.__VdfgRegularize_h6e95ff9d_0_0)) 
                                                    << 0x00000010U) 
                                                   | (IData)(vlSelfRef.__VdfgRegularize_h6e95ff9d_0_0));
        vlSelfRef.L1DCache__DOT__wr_data_w0[3U] = (
                                                   (((IData)(vlSelfRef.L1DCache__DOT__is_word)
                                                      ? (IData)(
                                                                (vlSelfRef.req_wdata 
                                                                 >> 0x00000010U))
                                                      : (IData)(vlSelfRef.__VdfgRegularize_h6e95ff9d_0_0)) 
                                                    << 0x00000010U) 
                                                   | (IData)(vlSelfRef.__VdfgRegularize_h6e95ff9d_0_0));
        vlSelfRef.L1DCache__DOT__wr_data_w0[4U] = (
                                                   (((IData)(vlSelfRef.L1DCache__DOT__is_word)
                                                      ? (IData)(
                                                                (vlSelfRef.req_wdata 
                                                                 >> 0x00000010U))
                                                      : (IData)(vlSelfRef.__VdfgRegularize_h6e95ff9d_0_0)) 
                                                    << 0x00000010U) 
                                                   | (IData)(vlSelfRef.__VdfgRegularize_h6e95ff9d_0_0));
        vlSelfRef.L1DCache__DOT__wr_data_w0[5U] = (
                                                   (((IData)(vlSelfRef.L1DCache__DOT__is_word)
                                                      ? (IData)(
                                                                (vlSelfRef.req_wdata 
                                                                 >> 0x00000010U))
                                                      : (IData)(vlSelfRef.__VdfgRegularize_h6e95ff9d_0_0)) 
                                                    << 0x00000010U) 
                                                   | (IData)(vlSelfRef.__VdfgRegularize_h6e95ff9d_0_0));
        vlSelfRef.L1DCache__DOT__wr_data_w0[6U] = (
                                                   (((IData)(vlSelfRef.L1DCache__DOT__is_word)
                                                      ? (IData)(
                                                                (vlSelfRef.req_wdata 
                                                                 >> 0x00000010U))
                                                      : (IData)(vlSelfRef.__VdfgRegularize_h6e95ff9d_0_0)) 
                                                    << 0x00000010U) 
                                                   | (IData)(vlSelfRef.__VdfgRegularize_h6e95ff9d_0_0));
        vlSelfRef.L1DCache__DOT__wr_data_w0[7U] = (
                                                   (((IData)(vlSelfRef.L1DCache__DOT__is_word)
                                                      ? (IData)(
                                                                (vlSelfRef.req_wdata 
                                                                 >> 0x00000010U))
                                                      : (IData)(vlSelfRef.__VdfgRegularize_h6e95ff9d_0_0)) 
                                                    << 0x00000010U) 
                                                   | (IData)(vlSelfRef.__VdfgRegularize_h6e95ff9d_0_0));
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

bool VL1DCache___024root___trigger_anySet__ico(const VlUnpacked<QData/*63:0*/, 2> &in);

#ifdef VL_DEBUG
VL_ATTR_COLD void VL1DCache___024root___dump_triggers__ico(const VlUnpacked<QData/*63:0*/, 2> &triggers, const std::string &tag) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VL1DCache___024root___dump_triggers__ico\n"); );
    // Body
    if ((1U & (~ (IData)(VL1DCache___024root___trigger_anySet__ico(triggers))))) {
        VL_DBG_MSGS("         No '" + tag + "' region triggers active\n");
    }
    if ((1U & (IData)(triggers[0U]))) {
        VL_DBG_MSGS("         '" + tag + "' region trigger index 0 is active: @( req_valid)\n");
    }
    if ((1U & (IData)((triggers[0U] >> 1U)))) {
        VL_DBG_MSGS("         '" + tag + "' region trigger index 1 is active: @( req_we)\n");
    }
    if ((1U & (IData)((triggers[0U] >> 2U)))) {
        VL_DBG_MSGS("         '" + tag + "' region trigger index 2 is active: @( req_addr)\n");
    }
    if ((1U & (IData)((triggers[0U] >> 3U)))) {
        VL_DBG_MSGS("         '" + tag + "' region trigger index 3 is active: @( req_wdata)\n");
    }
    if ((1U & (IData)((triggers[0U] >> 4U)))) {
        VL_DBG_MSGS("         '" + tag + "' region trigger index 4 is active: @( req_size)\n");
    }
    if ((1U & (IData)((triggers[0U] >> 5U)))) {
        VL_DBG_MSGS("         '" + tag + "' region trigger index 5 is active: @( refill_valid)\n");
    }
    if ((1U & (IData)((triggers[0U] >> 6U)))) {
        VL_DBG_MSGS("         '" + tag + "' region trigger index 6 is active: @( refill_data)\n");
    }
    if ((1U & (IData)((triggers[0U] >> 7U)))) {
        VL_DBG_MSGS("         '" + tag + "' region trigger index 7 is active: @( wb_ack)\n");
    }
    if ((1U & (IData)((triggers[0U] >> 8U)))) {
        VL_DBG_MSGS("         '" + tag + "' region trigger index 8 is active: @( fence_i)\n");
    }
    if ((1U & (IData)((triggers[0U] >> 9U)))) {
        VL_DBG_MSGS("         '" + tag + "' region trigger index 9 is active: @( clock)\n");
    }
    if ((1U & (IData)((triggers[0U] >> 0x0000000aU)))) {
        VL_DBG_MSGS("         '" + tag + "' region trigger index 10 is active: @( reset)\n");
    }
    if ((1U & (IData)(triggers[1U]))) {
        VL_DBG_MSGS("         '" + tag + "' region trigger index 64 is active: Internal 'ico' trigger - first iteration\n");
    }
}
#endif  // VL_DEBUG

bool VL1DCache___024root___trigger_anySet__act(const VlUnpacked<QData/*63:0*/, 1> &in);

#ifdef VL_DEBUG
VL_ATTR_COLD void VL1DCache___024root___dump_triggers__act(const VlUnpacked<QData/*63:0*/, 1> &triggers, const std::string &tag) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VL1DCache___024root___dump_triggers__act\n"); );
    // Body
    if ((1U & (~ (IData)(VL1DCache___024root___trigger_anySet__act(triggers))))) {
        VL_DBG_MSGS("         No '" + tag + "' region triggers active\n");
    }
    if ((1U & (IData)(triggers[0U]))) {
        VL_DBG_MSGS("         '" + tag + "' region trigger index 0 is active: @(posedge clock)\n");
    }
    if ((1U & (IData)((triggers[0U] >> 1U)))) {
        VL_DBG_MSGS("         '" + tag + "' region trigger index 1 is active: @(posedge reset)\n");
    }
}
#endif  // VL_DEBUG

VL_ATTR_COLD void VL1DCache___024root___ctor_var_reset(VL1DCache___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VL1DCache___024root___ctor_var_reset\n"); );
    VL1DCache__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    const uint64_t __VscopeHash = VL_MURMUR64_HASH(vlSelf->vlNamep);
    vlSelf->req_valid = VL_SCOPED_RAND_RESET_I(1, __VscopeHash, 12465084953323796564ull);
    vlSelf->req_we = VL_SCOPED_RAND_RESET_I(1, __VscopeHash, 15839722762072607281ull);
    vlSelf->req_addr = VL_SCOPED_RAND_RESET_I(32, __VscopeHash, 8827924800276735786ull);
    vlSelf->req_wdata = VL_SCOPED_RAND_RESET_Q(64, __VscopeHash, 3891584043155575951ull);
    vlSelf->req_size = VL_SCOPED_RAND_RESET_I(2, __VscopeHash, 4602496199685744212ull);
    vlSelf->refill_valid = VL_SCOPED_RAND_RESET_I(1, __VscopeHash, 10322335494162995794ull);
    VL_SCOPED_RAND_RESET_W(256, vlSelf->refill_data, __VscopeHash, 11168697880087203344ull);
    vlSelf->wb_ack = VL_SCOPED_RAND_RESET_I(1, __VscopeHash, 10739700758802936317ull);
    vlSelf->fence_i = VL_SCOPED_RAND_RESET_I(1, __VscopeHash, 12433034871770682783ull);
    vlSelf->resp_valid = VL_SCOPED_RAND_RESET_I(1, __VscopeHash, 4735948940430534270ull);
    vlSelf->resp_data = VL_SCOPED_RAND_RESET_Q(64, __VscopeHash, 15368686384628245554ull);
    vlSelf->miss_valid = VL_SCOPED_RAND_RESET_I(1, __VscopeHash, 8398881475748943990ull);
    vlSelf->miss_addr = VL_SCOPED_RAND_RESET_I(32, __VscopeHash, 14113374476463280350ull);
    vlSelf->wb_valid = VL_SCOPED_RAND_RESET_I(1, __VscopeHash, 3497284126980777111ull);
    vlSelf->wb_addr = VL_SCOPED_RAND_RESET_I(32, __VscopeHash, 9922404897426586993ull);
    VL_SCOPED_RAND_RESET_W(256, vlSelf->wb_data, __VscopeHash, 16778089495013024266ull);
    vlSelf->stall = VL_SCOPED_RAND_RESET_I(1, __VscopeHash, 7179230919112499263ull);
    vlSelf->fence_i_busy = VL_SCOPED_RAND_RESET_I(1, __VscopeHash, 14182098136676769470ull);
    vlSelf->clock = VL_SCOPED_RAND_RESET_I(1, __VscopeHash, 5452235342940299466ull);
    vlSelf->reset = VL_SCOPED_RAND_RESET_I(1, __VscopeHash, 9928399931838511862ull);
    vlSelf->L1DCache__DOT__data_rd_addr = VL_SCOPED_RAND_RESET_I(2, __VscopeHash, 17086299598993025003ull);
    vlSelf->L1DCache__DOT__valid_dec_w0 = VL_SCOPED_RAND_RESET_I(4, __VscopeHash, 13961648157491751300ull);
    vlSelf->L1DCache__DOT__way0_valid_sel = VL_SCOPED_RAND_RESET_I(1, __VscopeHash, 5283004028693855859ull);
    vlSelf->L1DCache__DOT__way1_valid_sel = VL_SCOPED_RAND_RESET_I(1, __VscopeHash, 5383336931674270858ull);
    vlSelf->L1DCache__DOT__victim_needs_wb = VL_SCOPED_RAND_RESET_I(1, __VscopeHash, 10817099926203329622ull);
    vlSelf->L1DCache__DOT__way1_hit = VL_SCOPED_RAND_RESET_I(1, __VscopeHash, 4740203511451810634ull);
    vlSelf->L1DCache__DOT__hit = VL_SCOPED_RAND_RESET_I(1, __VscopeHash, 5854774542615238160ull);
    vlSelf->L1DCache__DOT__miss_detect = VL_SCOPED_RAND_RESET_I(1, __VscopeHash, 6366940309628642018ull);
    vlSelf->L1DCache__DOT__miss_detect_clean = VL_SCOPED_RAND_RESET_I(1, __VscopeHash, 6554870142523678523ull);
    vlSelf->L1DCache__DOT__victim_lru = VL_SCOPED_RAND_RESET_I(1, __VscopeHash, 7705589901676960468ull);
    vlSelf->L1DCache__DOT__write_hit = VL_SCOPED_RAND_RESET_I(1, __VscopeHash, 7091973442195854079ull);
    vlSelf->L1DCache__DOT__wdc = VL_SCOPED_RAND_RESET_I(8, __VscopeHash, 4796187566150449461ull);
    vlSelf->L1DCache__DOT__rfs_0 = VL_SCOPED_RAND_RESET_I(4, __VscopeHash, 4125684056526582922ull);
    vlSelf->L1DCache__DOT__rfe_0 = VL_SCOPED_RAND_RESET_I(4, __VscopeHash, 5951104817137129794ull);
    vlSelf->L1DCache__DOT__whs_0 = VL_SCOPED_RAND_RESET_I(4, __VscopeHash, 17708898995678632095ull);
    vlSelf->L1DCache__DOT__rfe_1 = VL_SCOPED_RAND_RESET_I(4, __VscopeHash, 11827132596929372248ull);
    vlSelf->L1DCache__DOT__is_word = VL_SCOPED_RAND_RESET_I(1, __VscopeHash, 2921768544348789074ull);
    vlSelf->L1DCache__DOT__be0_h = VL_SCOPED_RAND_RESET_I(1, __VscopeHash, 5540544299595766474ull);
    vlSelf->L1DCache__DOT__be2_h = VL_SCOPED_RAND_RESET_I(1, __VscopeHash, 4965781223242713941ull);
    vlSelf->L1DCache__DOT__is_refill_wait = VL_SCOPED_RAND_RESET_I(1, __VscopeHash, 5158915423741200876ull);
    vlSelf->L1DCache__DOT__refill_done = VL_SCOPED_RAND_RESET_I(1, __VscopeHash, 1363526087057144708ull);
    vlSelf->L1DCache__DOT__data_wr_addr_w0 = VL_SCOPED_RAND_RESET_I(2, __VscopeHash, 12736788125805581735ull);
    VL_SCOPED_RAND_RESET_W(256, vlSelf->L1DCache__DOT__ram_be_w0, __VscopeHash, 12825751458997572474ull);
    VL_SCOPED_RAND_RESET_W(256, vlSelf->L1DCache__DOT__wr_data_w0, __VscopeHash, 10901256234153386407ull);
    vlSelf->L1DCache__DOT__lru_en = VL_SCOPED_RAND_RESET_I(4, __VscopeHash, 5267694988140279134ull);
    vlSelf->L1DCache__DOT__lru_nv = VL_SCOPED_RAND_RESET_I(4, __VscopeHash, 7099333306990886449ull);
    vlSelf->L1DCache__DOT__tag_q_w0_s0 = VL_SCOPED_RAND_RESET_I(25, __VscopeHash, 17584234362386380872ull);
    vlSelf->L1DCache__DOT__tag_q_w0_s1 = VL_SCOPED_RAND_RESET_I(25, __VscopeHash, 18064303985687762253ull);
    vlSelf->L1DCache__DOT__tag_q_w0_s2 = VL_SCOPED_RAND_RESET_I(25, __VscopeHash, 11770457281020409238ull);
    vlSelf->L1DCache__DOT__tag_q_w0_s3 = VL_SCOPED_RAND_RESET_I(25, __VscopeHash, 1967604661696354243ull);
    vlSelf->L1DCache__DOT__tag_q_w1_s0 = VL_SCOPED_RAND_RESET_I(25, __VscopeHash, 14419475107309995005ull);
    vlSelf->L1DCache__DOT__tag_q_w1_s1 = VL_SCOPED_RAND_RESET_I(25, __VscopeHash, 6923128099377545690ull);
    vlSelf->L1DCache__DOT__tag_q_w1_s2 = VL_SCOPED_RAND_RESET_I(25, __VscopeHash, 17255261792389547150ull);
    vlSelf->L1DCache__DOT__tag_q_w1_s3 = VL_SCOPED_RAND_RESET_I(25, __VscopeHash, 2966302259519643852ull);
    vlSelf->L1DCache__DOT__fsm_q_reg = VL_SCOPED_RAND_RESET_I(3, __VscopeHash, 11140322678922024058ull);
    vlSelf->L1DCache__DOT__pend_q_reg = VL_SCOPED_RAND_RESET_I(32, __VscopeHash, 13583622886328675148ull);
    vlSelf->L1DCache__DOT__pend_victim_q_reg = VL_SCOPED_RAND_RESET_I(1, __VscopeHash, 4373652541076582307ull);
    vlSelf->L1DCache__DOT__lru_q_reg = VL_SCOPED_RAND_RESET_I(4, __VscopeHash, 12250914454590751945ull);
    vlSelf->L1DCache__DOT__valid_q_reg = VL_SCOPED_RAND_RESET_I(8, __VscopeHash, 9580897773573269589ull);
    vlSelf->L1DCache__DOT__dirty_q_reg = VL_SCOPED_RAND_RESET_I(8, __VscopeHash, 1822933187246252008ull);
    for (int __Vi0 = 0; __Vi0 < 4; ++__Vi0) {
        VL_SCOPED_RAND_RESET_W(256, vlSelf->L1DCache__DOT__data_ram_w0[__Vi0], __VscopeHash, 8974110423621787814ull);
    }
    for (int __Vi0 = 0; __Vi0 < 4; ++__Vi0) {
        VL_SCOPED_RAND_RESET_W(256, vlSelf->L1DCache__DOT__data_ram_w1[__Vi0], __VscopeHash, 2419209578089177738ull);
    }
    vlSelf->L1DCache__DOT____Vcellinp__u_data_word_mux_w0__in7 = 0;
    vlSelf->L1DCache__DOT____Vcellinp__u_data_word_mux_w0__in5 = 0;
    vlSelf->L1DCache__DOT____Vcellinp__u_data_word_mux_w0__in3 = 0;
    vlSelf->L1DCache__DOT____Vcellinp__u_data_word_mux_w0__in1 = 0;
    vlSelf->L1DCache__DOT____Vcellinp__u_data_word_mux_w1__in7 = 0;
    vlSelf->L1DCache__DOT____Vcellinp__u_data_word_mux_w1__in5 = 0;
    vlSelf->L1DCache__DOT____Vcellinp__u_data_word_mux_w1__in3 = 0;
    vlSelf->L1DCache__DOT____Vcellinp__u_data_word_mux_w1__in1 = 0;
    vlSelf->__VdfgRegularize_h6e95ff9d_0_0 = 0;
    vlSelf->__VdfgRegularize_h6e95ff9d_0_1 = 0;
    vlSelf->__Vdly__L1DCache__DOT__pend_victim_q_reg = 0;
    for (int __Vi0 = 0; __Vi0 < 1; ++__Vi0) {
        vlSelf->__VstlTriggered[__Vi0] = 0;
    }
    for (int __Vi0 = 0; __Vi0 < 2; ++__Vi0) {
        vlSelf->__VicoTriggered[__Vi0] = 0;
    }
    vlSelf->__Vtrigprevexpr___TOP__req_valid__0 = 0;
    vlSelf->__Vtrigprevexpr___TOP__req_we__0 = 0;
    vlSelf->__Vtrigprevexpr___TOP__req_addr__0 = 0;
    vlSelf->__Vtrigprevexpr___TOP__req_wdata__0 = 0;
    vlSelf->__Vtrigprevexpr___TOP__req_size__0 = 0;
    vlSelf->__Vtrigprevexpr___TOP__refill_valid__0 = 0;
    VL_ZERO_RESET_W(256, vlSelf->__Vtrigprevexpr___TOP__refill_data__0);
    vlSelf->__Vtrigprevexpr___TOP__wb_ack__0 = 0;
    vlSelf->__Vtrigprevexpr___TOP__fence_i__0 = 0;
    vlSelf->__Vtrigprevexpr___TOP__clock__0 = 0;
    vlSelf->__Vtrigprevexpr___TOP__reset__0 = 0;
    vlSelf->__VicoDidInit = 0;
    for (int __Vi0 = 0; __Vi0 < 1; ++__Vi0) {
        vlSelf->__VactTriggered[__Vi0] = 0;
    }
    vlSelf->__Vtrigprevexpr___TOP__clock__1 = 0;
    vlSelf->__Vtrigprevexpr___TOP__reset__1 = 0;
    for (int __Vi0 = 0; __Vi0 < 1; ++__Vi0) {
        vlSelf->__VnbaTriggered[__Vi0] = 0;
    }
}
