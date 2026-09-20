/*
 * sram_dpi.c — generic DPI-C backing store for all SRAM simulation models.
 *
 * Compiled into the Verilator sim alongside sram_dpi.c; the sim Makefile
 * passes -I$(VERILATOR_ROOT)/include/vltstd so svdpi.h is found.
 * The fallback typedef handles builds outside the Verilator tree (e.g. LSP).
 *
 * Interface (declared via DPI import in each generated SV wrapper):
 *
 *   int  sram_dpi_resolve(string path, int depth, int width_bytes)
 *        Called once in `initial`; returns a slot id for subsequent calls.
 *
 *   void sram_dpi_write(int id, int addr, bit[W-1:0] data, int width_bytes)
 *        Clocked write; `data` arrives as uint32_t[] (Verilator svBitVecVal).
 *
 *   void sram_dpi_read(int id, int addr, int width_bytes, output bit[W-1:0] out)
 *        Clocked read; `out` written as uint32_t[] in-place.
 *
 * Supports width up to 512 bits (64 bytes) and depth up to 65536 rows.
 */
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

/* svBitVecVal is uint32_t per IEEE 1800-2012 DPI spec and Verilator's svdpi.h.
 * Define it here so the file compiles without the Verilator include path on
 * the search path (e.g. during LSP analysis or standalone unit tests).
 * The guard prevents a redefinition error when svdpi.h is included first. */
#ifndef INCLUDED_SVDPI
typedef uint32_t svBitVecVal;
#endif

#define SRAM_MAX_SLOTS  256
#define SRAM_MAX_PATH   256

/* Verilator compiles user C sources with the C++ compiler, so the definitions
 * need C linkage to match the `extern "C"` declarations in its DPI wrappers. */
#ifdef __cplusplus
extern "C" {
#endif

typedef struct {
    char     path[SRAM_MAX_PATH];
    uint8_t *data;        /* depth * width_bytes bytes, zero-initialised */
    int      depth;
    int      width_bytes;
} Slot;

static Slot slots[SRAM_MAX_SLOTS];
static int  n_slots = 0;

/* Map instance path → slot id, allocating on first call. */
int sram_dpi_resolve(const char *path, int depth, int width_bytes) {
    for (int i = 0; i < n_slots; i++) {
        if (strcmp(slots[i].path, path) == 0)
            return i;
    }
    if (n_slots >= SRAM_MAX_SLOTS)
        return -1;

    int id = n_slots++;
    strncpy(slots[id].path, path, SRAM_MAX_PATH - 1);
    slots[id].path[SRAM_MAX_PATH - 1] = '\0';
    slots[id].depth       = depth;
    slots[id].width_bytes = width_bytes;
    slots[id].data        = (uint8_t *)calloc((size_t)depth * width_bytes, 1);
    return id;
}

/* Write width_bytes bytes from `data` (Verilator svBitVecVal[], LSW first). */
void sram_dpi_write(int id, int addr,
                    const svBitVecVal *data, int width_bytes) {
    if (id < 0 || id >= n_slots) return;
    const Slot *s = &slots[id];
    if (addr < 0 || addr >= s->depth) return;
    memcpy(s->data + (size_t)addr * s->width_bytes, data, (size_t)width_bytes);
}

/* Read width_bytes bytes into `out` (Verilator svBitVecVal[], LSW first). */
void sram_dpi_read(int id, int addr,
                   int width_bytes, svBitVecVal *out) {
    if (id < 0 || id >= n_slots) {
        memset(out, 0, (size_t)width_bytes);
        return;
    }
    const Slot *s = &slots[id];
    if (addr < 0 || addr >= s->depth) {
        memset(out, 0, (size_t)width_bytes);
        return;
    }
    memcpy(out, s->data + (size_t)addr * s->width_bytes, (size_t)width_bytes);
}

#ifdef __cplusplus
}
#endif
