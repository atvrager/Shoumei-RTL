// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Model implementation (design independent parts)

#include "VL1DCache__pch.h"

//============================================================
// Constructors

VL1DCache::VL1DCache(VerilatedContext* _vcontextp__, const char* _vcname__)
    : VerilatedModel{*_vcontextp__}
    , vlSymsp{new VL1DCache__Syms(contextp(), _vcname__, this)}
    , m_evalLoop{*this, /*convergeLimit:*/ 10000}
    , clock{vlSymsp->TOP.clock}
    , reset{vlSymsp->TOP.reset}
    , req_valid{vlSymsp->TOP.req_valid}
    , req_we{vlSymsp->TOP.req_we}
    , req_size{vlSymsp->TOP.req_size}
    , refill_valid{vlSymsp->TOP.refill_valid}
    , wb_ack{vlSymsp->TOP.wb_ack}
    , fence_i{vlSymsp->TOP.fence_i}
    , resp_valid{vlSymsp->TOP.resp_valid}
    , miss_valid{vlSymsp->TOP.miss_valid}
    , wb_valid{vlSymsp->TOP.wb_valid}
    , stall{vlSymsp->TOP.stall}
    , fence_i_busy{vlSymsp->TOP.fence_i_busy}
    , req_addr{vlSymsp->TOP.req_addr}
    , refill_data{vlSymsp->TOP.refill_data}
    , miss_addr{vlSymsp->TOP.miss_addr}
    , wb_addr{vlSymsp->TOP.wb_addr}
    , wb_data{vlSymsp->TOP.wb_data}
    , req_wdata{vlSymsp->TOP.req_wdata}
    , resp_data{vlSymsp->TOP.resp_data}
    , rootp{&(vlSymsp->TOP)}
{
    // Register model with the context
    contextp()->addModel(this);
}

VL1DCache::VL1DCache(const char* _vcname__)
    : VL1DCache(Verilated::threadContextp(), _vcname__)
{
}

//============================================================
// Destructor

VL1DCache::~VL1DCache() {
    delete vlSymsp;
}

//============================================================
// Evaluation function

#ifdef VL_DEBUG
void VL1DCache___024root___eval_debug_assertions(VL1DCache___024root* vlSelf);
#endif  // VL_DEBUG
VL_ATTR_COLD void VL1DCache___024root___eval_static(VL1DCache___024root* vlSelf);
VL_ATTR_COLD void VL1DCache___024root___eval_initial(VL1DCache___024root* vlSelf);
VL_ATTR_COLD bool VL1DCache___024root___eval_stl(VL1DCache___024root* vlSelf, CData/*0:0*/ firstIteration);
void VL1DCache___024root___eval_sample(VL1DCache___024root* vlSelf);
bool VL1DCache___024root___eval_ico(VL1DCache___024root* vlSelf, CData/*0:0*/ firstIteration);
bool VL1DCache___024root___eval_act(VL1DCache___024root* vlSelf);
bool VL1DCache___024root___eval_inact(VL1DCache___024root* vlSelf);
bool VL1DCache___024root___eval_nba(VL1DCache___024root* vlSelf);
bool VL1DCache___024root___eval_obs(VL1DCache___024root* vlSelf);
bool VL1DCache___024root___eval_react(VL1DCache___024root* vlSelf);
void VL1DCache___024root___eval_postponed(VL1DCache___024root* vlSelf);
VL_ATTR_COLD void VL1DCache___024root___eval_final(VL1DCache___024root* vlSelf);
VL_ATTR_COLD void VL1DCache___024root___eval_dump_triggers__stl(VL1DCache___024root* vlSelf);
VL_ATTR_COLD void VL1DCache___024root___eval_dump_triggers__ico(VL1DCache___024root* vlSelf);
VL_ATTR_COLD void VL1DCache___024root___eval_dump_triggers__act(VL1DCache___024root* vlSelf);
VL_ATTR_COLD void VL1DCache___024root___eval_dump_triggers__nba(VL1DCache___024root* vlSelf);
VL_ATTR_COLD void VL1DCache___024root___eval_dump_triggers__obs(VL1DCache___024root* vlSelf);
VL_ATTR_COLD void VL1DCache___024root___eval_dump_triggers__react(VL1DCache___024root* vlSelf);

void VL1DCache::eval_step() {
    VL_DEBUG_IF(VL_DBG_MSGF("+++++TOP Evaluate VL1DCache::eval_step\n"); );
    m_evalLoop.eval();
}

void VL1DCache::evalBegin() {
#ifdef VL_DEBUG
    // Debug assertions
    VL1DCache___024root___eval_debug_assertions(&(vlSymsp->TOP));
#endif  // VL_DEBUG
    vlSymsp->__Vm_deleter.deleteAll();
}

void VL1DCache::evalEnd() {
    // Evaluate cleanup
    Verilated::endOfEval(vlSymsp->__Vm_evalMsgQp);
}

void VL1DCache::evalStatic() {
    VL1DCache___024root___eval_static(&(vlSymsp->TOP));
}

void VL1DCache::evalInitial() {
    VL1DCache___024root___eval_initial(&(vlSymsp->TOP));
}

bool VL1DCache::evalStl(bool firstIteration) {
    return VL1DCache___024root___eval_stl(&(vlSymsp->TOP), firstIteration);
}

void VL1DCache::evalSample() {
    VL1DCache___024root___eval_sample(&(vlSymsp->TOP));
}

bool VL1DCache::evalIco(bool firstIteration) {
    return VL1DCache___024root___eval_ico(&(vlSymsp->TOP), firstIteration);
}

bool VL1DCache::evalAct() {
    return VL1DCache___024root___eval_act(&(vlSymsp->TOP));
}

bool VL1DCache::evalInact() {
    return VL1DCache___024root___eval_inact(&(vlSymsp->TOP));
}

bool VL1DCache::evalNba() {
    return VL1DCache___024root___eval_nba(&(vlSymsp->TOP));
}

bool VL1DCache::evalObs() {
    return VL1DCache___024root___eval_obs(&(vlSymsp->TOP));
}

bool VL1DCache::evalReact() {
    return VL1DCache___024root___eval_react(&(vlSymsp->TOP));
}

void VL1DCache::evalPostponed() {
    VL1DCache___024root___eval_postponed(&(vlSymsp->TOP));
}

void VL1DCache::evalFinal() {
    VL1DCache___024root___eval_final(&(vlSymsp->TOP));
}

VL_ATTR_COLD void VL1DCache::dumpTriggersStl() {
    VL1DCache___024root___eval_dump_triggers__stl(&(vlSymsp->TOP));
}

VL_ATTR_COLD void VL1DCache::dumpTriggersIco() {
    VL1DCache___024root___eval_dump_triggers__ico(&(vlSymsp->TOP));
}

VL_ATTR_COLD void VL1DCache::dumpTriggersAct() {
    VL1DCache___024root___eval_dump_triggers__act(&(vlSymsp->TOP));
}

VL_ATTR_COLD void VL1DCache::dumpTriggersNba() {
    VL1DCache___024root___eval_dump_triggers__nba(&(vlSymsp->TOP));
}

VL_ATTR_COLD void VL1DCache::dumpTriggersObs() {
    VL1DCache___024root___eval_dump_triggers__obs(&(vlSymsp->TOP));
}

VL_ATTR_COLD void VL1DCache::dumpTriggersReact() {
    VL1DCache___024root___eval_dump_triggers__react(&(vlSymsp->TOP));
}

//============================================================
// Events and timing
bool VL1DCache::eventsPending() { return false; }

uint64_t VL1DCache::nextTimeSlot() {
    VL_FATAL_MT(__FILE__, __LINE__, "", "No delays in the design");
    return 0;
}

//============================================================
// Utilities

const char* VL1DCache::name() const {
    return vlSymsp->name();
}

//============================================================
// Invoke final blocks

VL_ATTR_COLD void VL1DCache::final() {
    contextp()->executingFinal(true);
    evalFinal();
    contextp()->executingFinal(false);
}

//============================================================
// Implementations of abstract methods from VerilatedModel

const char* VL1DCache::hierName() const { return vlSymsp->name(); }
const char* VL1DCache::modelName() const { return "VL1DCache"; }
unsigned VL1DCache::threads() const { return 1; }
void VL1DCache::prepareClone() const { contextp()->prepareClone(); }
void VL1DCache::atClone() const {
    contextp()->threadPoolpOnClone();
}
