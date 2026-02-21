// fst_inspect.cpp - Fast FST signal inspector for Shoumei RTL debugging
//
// Build:
//   g++ -O2 -o fst_inspect scripts/fst_inspect.cpp \
//       -I/usr/share/verilator/include/gtkwave -I/tmp/zlib-1.3.1 \
//       /usr/share/verilator/include/gtkwave/fstapi.c -lz -lpthread
//
// Usage:
//   ./scripts/fst_inspect shoumei_cpu.fst --list [pattern]
//   ./scripts/fst_inspect shoumei_cpu.fst --cycles 60-100 --signals rvvi_valid,rvvi_pc_rdata
//   ./scripts/fst_inspect shoumei_cpu.fst --cycles 60-100 --signals sig1,sig2 --when sig1=1

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>
#include <unordered_map>
#include <algorithm>
#include <fnmatch.h>
#include "fstapi.h"

struct SignalInfo {
    fstHandle handle;
    std::string name;
    uint32_t width;
    std::string value;
};

static std::vector<SignalInfo> g_signals;
static std::unordered_map<fstHandle, size_t> g_handle_map;
static std::vector<int> g_col_widths;
static uint64_t g_cy_start, g_cy_end, g_current_cy;
static uint64_t g_next_sample_time;
static int g_clock_period = 2;
static int g_when_idx = -1;
static std::string g_when_val;

static std::string format_value(const std::string& raw, uint32_t width) {
    if (width == 1) return raw;
    if (raw.find('x') != std::string::npos || raw.find('X') != std::string::npos ||
        raw.find('z') != std::string::npos || raw.find('Z') != std::string::npos)
        return raw;
    uint64_t v = 0;
    for (char c : raw) v = (v << 1) | (c == '1' ? 1 : 0);
    int hw = (width + 3) / 4;
    char buf[32];
    snprintf(buf, sizeof(buf), "0x%0*lx", hw, v);
    return buf;
}

static void emit_row() {
    if (g_when_idx >= 0 && g_signals[g_when_idx].value != g_when_val) return;
    printf("%6lu | ", g_current_cy);
    for (size_t i = 0; i < g_signals.size(); i++) {
        std::string fv = format_value(g_signals[i].value, g_signals[i].width);
        printf("%*s", g_col_widths[i], fv.c_str());
        if (i + 1 < g_signals.size()) printf(" | ");
    }
    printf("\n");
}

static void flush_samples_up_to(uint64_t time) {
    while (g_current_cy <= g_cy_end && g_next_sample_time <= time) {
        emit_row();
        g_current_cy++;
        g_next_sample_time = g_current_cy * g_clock_period + g_clock_period / 2;
    }
}

static void value_change_cb(void*, uint64_t time, fstHandle handle, const unsigned char* value) {
    flush_samples_up_to(time);
    auto it = g_handle_map.find(handle);
    if (it != g_handle_map.end()) {
        g_signals[it->second].value = (const char*)value;
    }
}

static void value_change_cb2(void*, uint64_t time, fstHandle handle, const unsigned char* value, uint32_t) {
    value_change_cb(nullptr, time, handle, value);
}

int main(int argc, char** argv) {
    if (argc < 2) {
        fprintf(stderr, "Usage: %s <file.fst> [--list [pattern]] [--cycles S-E --signals s1,s2 [--when sig=val]]\n", argv[0]);
        return 1;
    }

    const char* fst_path = argv[1];
    const char* list_pattern = nullptr;
    const char* signals_str = nullptr;
    const char* cycles_str = nullptr;
    const char* when_str = nullptr;
    const char* scope_filter = nullptr;
    bool do_list = false;

    for (int i = 2; i < argc; i++) {
        if (strcmp(argv[i], "--list") == 0) {
            do_list = true;
            if (i + 1 < argc && argv[i+1][0] != '-') list_pattern = argv[++i];
        } else if (strcmp(argv[i], "--signals") == 0 && i + 1 < argc) {
            signals_str = argv[++i];
        } else if (strcmp(argv[i], "--cycles") == 0 && i + 1 < argc) {
            cycles_str = argv[++i];
        } else if (strcmp(argv[i], "--when") == 0 && i + 1 < argc) {
            when_str = argv[++i];
        } else if (strcmp(argv[i], "--scope") == 0 && i + 1 < argc) {
            scope_filter = argv[++i];
        }
    }

    auto ctx = fstReaderOpen(fst_path);
    if (!ctx) {
        fprintf(stderr, "ERROR: Cannot open FST file: %s\n", fst_path);
        return 1;
    }

    if (do_list) {
        fstHier* hier;
        fstReaderResetScope(ctx);
        fstReaderIterateHierRewind(ctx);
        while ((hier = fstReaderIterateHier(ctx)) != nullptr) {
            switch (hier->htyp) {
                case FST_HT_SCOPE:
                    fstReaderPushScope(ctx, hier->u.scope.name, nullptr);
                    break;
                case FST_HT_UPSCOPE:
                    fstReaderPopScope(ctx);
                    break;
                case FST_HT_VAR: {
                    const char* flat = fstReaderGetCurrentFlatScope(ctx);
                    std::string name = hier->u.var.name ? hier->u.var.name : "";
                    std::string full = (flat && flat[0]) ? std::string(flat) + "." + name : name;
                    if (scope_filter && full.find(scope_filter) == std::string::npos) break;
                    if (list_pattern && fnmatch(list_pattern, name.c_str(), 0) != 0 &&
                        fnmatch(list_pattern, full.c_str(), 0) != 0) break;
                    printf("  [%3u] %s\n", hier->u.var.length, full.c_str());
                    break;
                }
                default: break;
            }
        }
        fstReaderClose(ctx);
        return 0;
    }

    if (!signals_str || !cycles_str) {
        fprintf(stderr, "Need --signals and --cycles\n");
        fstReaderClose(ctx);
        return 1;
    }

    // Parse cycle range
    if (sscanf(cycles_str, "%lu-%lu", &g_cy_start, &g_cy_end) != 2) {
        fprintf(stderr, "Invalid cycle range: %s\n", cycles_str);
        fstReaderClose(ctx);
        return 1;
    }

    // Parse signal names
    std::vector<std::string> sig_names;
    { char* buf = strdup(signals_str); char* tok = strtok(buf, ",");
      while (tok) { sig_names.push_back(tok); tok = strtok(nullptr, ","); }
      free(buf);
    }

    // Build name->handle map from hierarchy using flat scope tracking
    std::unordered_map<std::string, std::pair<fstHandle, uint32_t>> all_sigs;
    {
        fstHier* hier;
        fstReaderResetScope(ctx);
        fstReaderIterateHierRewind(ctx);
        while ((hier = fstReaderIterateHier(ctx)) != nullptr) {
            switch (hier->htyp) {
                case FST_HT_SCOPE:
                    fstReaderPushScope(ctx, hier->u.scope.name, nullptr);
                    break;
                case FST_HT_UPSCOPE:
                    fstReaderPopScope(ctx);
                    break;
                case FST_HT_VAR: {
                    const char* flat = fstReaderGetCurrentFlatScope(ctx);
                    std::string name = hier->u.var.name ? hier->u.var.name : "";
                    std::string full = (flat && flat[0]) ? std::string(flat) + "." + name : name;
                    auto info = std::make_pair(hier->u.var.handle, hier->u.var.length);
                    all_sigs[full] = info;       // full path
                    all_sigs[name] = info;        // leaf name (last wins if ambiguous)
                    break;
                }
                default: break;
            }
        }
    }

    // Resolve requested signals
    for (auto& name : sig_names) {
        auto it = all_sigs.find(name);
        if (it == all_sigs.end()) {
            // Substring match
            for (auto& [sn, info] : all_sigs) {
                if (sn.find(name) != std::string::npos) { it = all_sigs.find(sn); break; }
            }
        }
        if (it != all_sigs.end()) {
            SignalInfo si; si.handle = it->second.first; si.name = name;
            si.width = it->second.second; si.value = "x";
            fprintf(stderr, "  resolved '%s' → handle=%u width=%u\n", name.c_str(), si.handle, si.width);
            g_handle_map[si.handle] = g_signals.size();
            g_signals.push_back(si);
            fstReaderSetFacProcessMask(ctx, si.handle);
        } else {
            fprintf(stderr, "WARNING: signal '%s' not found\n", name.c_str());
        }
    }

    if (g_signals.empty()) { fprintf(stderr, "No signals resolved\n"); fstReaderClose(ctx); return 1; }

    // Parse --when
    if (when_str) {
        const char* eq = strchr(when_str, '=');
        if (eq) {
            std::string wn(when_str, eq); g_when_val = eq + 1;
            for (size_t i = 0; i < g_signals.size(); i++)
                if (g_signals[i].name == wn) { g_when_idx = (int)i; break; }
        }
    }

    // Column widths + header
    for (auto& s : g_signals) g_col_widths.push_back(std::max((int)s.name.size(), 10));
    printf("%6s | ", "cy");
    for (size_t i = 0; i < g_signals.size(); i++) {
        printf("%*s", g_col_widths[i], g_signals[i].name.c_str());
        if (i + 1 < g_signals.size()) printf(" | ");
    }
    printf("\n");
    int hdr_len = 9;
    for (size_t i = 0; i < g_signals.size(); i++) hdr_len += g_col_widths[i] + 3;
    for (int i = 0; i < hdr_len; i++) putchar('-');
    putchar('\n');

    // Set time range and iterate
    uint64_t t_start = g_cy_start * g_clock_period;
    uint64_t t_end = (g_cy_end + 1) * g_clock_period;
    fstReaderSetLimitTimeRange(ctx, t_start, t_end);

    g_current_cy = g_cy_start;
    g_next_sample_time = g_cy_start * g_clock_period + g_clock_period / 2;

    fstReaderIterBlocks2(ctx, value_change_cb, value_change_cb2, nullptr, nullptr);

    // Emit remaining
    while (g_current_cy <= g_cy_end) { emit_row(); g_current_cy++; }

    fstReaderClose(ctx);
    return 0;
}
