#include "elf_loader.h"
#include <cstdio>
#include <cstring>
#include <elf.h>

int load_elf(const char* path, std::function<void(uint32_t, uint32_t)> write_word) {
    FILE* f = fopen(path, "rb");
    if (!f) {
        fprintf(stderr, "ERROR: Cannot open ELF file: %s\n", path);
        return -1;
    }

    // Read ELF header
    Elf32_Ehdr ehdr;
    if (fread(&ehdr, sizeof(ehdr), 1, f) != 1) {
        fprintf(stderr, "ERROR: Cannot read ELF header: %s\n", path);
        fclose(f);
        return -1;
    }

    // Validate
    if (memcmp(ehdr.e_ident, ELFMAG, SELFMAG) != 0) {
        fprintf(stderr, "ERROR: Not an ELF file: %s\n", path);
        fclose(f);
        return -1;
    }
    if (ehdr.e_ident[EI_CLASS] != ELFCLASS32) {
        fprintf(stderr, "ERROR: Not a 32-bit ELF: %s\n", path);
        fclose(f);
        return -1;
    }
    if (ehdr.e_machine != EM_RISCV) {
        fprintf(stderr, "ERROR: Not a RISC-V ELF (e_machine=%u): %s\n", ehdr.e_machine, path);
        fclose(f);
        return -1;
    }

    // Read program headers and load PT_LOAD segments
    uint32_t total_bytes = 0;
    for (int i = 0; i < ehdr.e_phnum; i++) {
        Elf32_Phdr phdr;
        fseek(f, ehdr.e_phoff + i * ehdr.e_phentsize, SEEK_SET);
        if (fread(&phdr, sizeof(phdr), 1, f) != 1) {
            fprintf(stderr, "ERROR: Cannot read program header %d\n", i);
            fclose(f);
            return -1;
        }

        if (phdr.p_type != PT_LOAD) continue;
        if (phdr.p_memsz == 0) continue;

        uint32_t base_addr = phdr.p_paddr;
        uint32_t filesz = phdr.p_filesz;
        uint32_t memsz = phdr.p_memsz;

        // Zero-fill the entire region first (handles BSS)
        for (uint32_t off = 0; off < memsz; off += 4) {
            write_word(base_addr + off, 0);
        }

        // Read file data
        if (filesz > 0) {
            fseek(f, phdr.p_offset, SEEK_SET);
            uint32_t words = (filesz + 3) / 4;
            for (uint32_t w = 0; w < words; w++) {
                uint32_t word = 0;
                uint32_t remaining = filesz - w * 4;
                uint32_t to_read = remaining < 4 ? remaining : 4;
                if (fread(&word, 1, to_read, f) != to_read) {
                    fprintf(stderr, "ERROR: Short read in segment %d\n", i);
                    fclose(f);
                    return -1;
                }
                write_word(base_addr + w * 4, word);
            }
        }

        printf("  PT_LOAD: paddr=0x%08x filesz=%u memsz=%u\n", base_addr, filesz, memsz);
        total_bytes += memsz;
    }

    fclose(f);
    printf("Loaded ELF %s (%u bytes total)\n", path, total_bytes);
    return (int)total_bytes;
}
