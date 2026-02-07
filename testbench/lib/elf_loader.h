#ifndef ELF_LOADER_H
#define ELF_LOADER_H

#include <cstdint>
#include <functional>

// Load an ELF32 RISC-V binary into memory via a callback.
// The callback is called for each word: callback(byte_addr, data_word).
// Returns total bytes loaded, or -1 on error.
int load_elf(const char* path, std::function<void(uint32_t, uint32_t)> write_word);

#endif // ELF_LOADER_H
