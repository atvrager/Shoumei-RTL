// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VL1DCache.h for the primary calling header

#include "VL1DCache__pch.h"

void VL1DCache___024root___ctor_var_reset(VL1DCache___024root* vlSelf);

VL1DCache___024root::VL1DCache___024root(VL1DCache__Syms* symsp, const char* namep)
 {
    vlSymsp = symsp;
    vlNamep = strdup(namep);
    // Reset structure values
    VL1DCache___024root___ctor_var_reset(this);
}

void VL1DCache___024root::__Vconfigure(bool first) {
    (void)first;  // Prevent unused variable warning
}

VL1DCache___024root::~VL1DCache___024root() {
    VL_DO_DANGLING(std::free(const_cast<char*>(vlNamep)), vlNamep);
}
