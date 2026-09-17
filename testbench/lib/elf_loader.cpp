#include "elf_loader.h"
#include <cstdio>
#include <cstring>
#include <elf.h>

int load_elf(const char* path, std::function<void(uint64_t, uint32_t)> write_word) {
    FILE* f = fopen(path, "rb");
    if (!f) {
        fprintf(stderr, "ERROR: Cannot open ELF file: %s\n", path);
        return -1;
    }

    unsigned char e_ident[EI_NIDENT];
    if (fread(e_ident, 1, EI_NIDENT, f) != EI_NIDENT) {
        fprintf(stderr, "ERROR: Cannot read ELF ident: %s\n", path);
        fclose(f);
        return -1;
    }
    if (memcmp(e_ident, ELFMAG, SELFMAG) != 0) {
        fprintf(stderr, "ERROR: Not an ELF file: %s\n", path);
        fclose(f);
        return -1;
    }

    fseek(f, 0, SEEK_SET);
    uint32_t total_bytes = 0;

    if (e_ident[EI_CLASS] == ELFCLASS64) {
        Elf64_Ehdr ehdr;
        if (fread(&ehdr, sizeof(ehdr), 1, f) != 1) {
            fprintf(stderr, "ERROR: Cannot read ELF64 header: %s\n", path);
            fclose(f);
            return -1;
        }
        if (ehdr.e_machine != EM_RISCV) {
            fprintf(stderr, "ERROR: Not a RISC-V ELF (e_machine=%u): %s\n", ehdr.e_machine, path);
            fclose(f);
            return -1;
        }

        for (int i = 0; i < ehdr.e_phnum; i++) {
            Elf64_Phdr phdr;
            fseek(f, ehdr.e_phoff + i * ehdr.e_phentsize, SEEK_SET);
            if (fread(&phdr, sizeof(phdr), 1, f) != 1) continue;
            if (phdr.p_type != PT_LOAD || phdr.p_memsz == 0) continue;

            uint64_t base_addr = phdr.p_paddr;
            uint64_t filesz = phdr.p_filesz;
            uint64_t memsz = phdr.p_memsz;

            for (uint64_t off = 0; off < memsz; off += 4) {
                write_word(base_addr + off, 0);
            }

            if (filesz > 0) {
                fseek(f, phdr.p_offset, SEEK_SET);
                uint64_t words = (filesz + 3) / 4;
                for (uint64_t w = 0; w < words; w++) {
                    uint32_t word = 0;
                    uint64_t remaining = filesz - w * 4;
                    uint64_t to_read = remaining < 4 ? remaining : 4;
                    if (fread(&word, 1, to_read, f) != to_read) {
                        fprintf(stderr, "ERROR: Short read in segment %d\n", i);
                        fclose(f);
                        return -1;
                    }
                    write_word(base_addr + w * 4, word);
                }
            }

            printf("  PT_LOAD: paddr=0x%016lx filesz=%lu memsz=%lu\n", base_addr, filesz, memsz);
            total_bytes += memsz;
        }
    } else if (e_ident[EI_CLASS] == ELFCLASS32) {
        Elf32_Ehdr ehdr;
        if (fread(&ehdr, sizeof(ehdr), 1, f) != 1) {
            fprintf(stderr, "ERROR: Cannot read ELF32 header: %s\n", path);
            fclose(f);
            return -1;
        }
        if (ehdr.e_machine != EM_RISCV) {
            fprintf(stderr, "ERROR: Not a RISC-V ELF (e_machine=%u): %s\n", ehdr.e_machine, path);
            fclose(f);
            return -1;
        }

        for (int i = 0; i < ehdr.e_phnum; i++) {
            Elf32_Phdr phdr;
            fseek(f, ehdr.e_phoff + i * ehdr.e_phentsize, SEEK_SET);
            if (fread(&phdr, sizeof(phdr), 1, f) != 1) continue;
            if (phdr.p_type != PT_LOAD || phdr.p_memsz == 0) continue;

            uint32_t base_addr = phdr.p_paddr;
            uint32_t filesz = phdr.p_filesz;
            uint32_t memsz = phdr.p_memsz;

            for (uint32_t off = 0; off < memsz; off += 4) {
                write_word(base_addr + off, 0);
            }

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
    } else {
        fprintf(stderr, "ERROR: Not a 32-bit or 64-bit ELF: %s\n", path);
        fclose(f);
        return -1;
    }

    fclose(f);
    printf("Loaded ELF %s (%u bytes total)\n", path, total_bytes);
    return (int)total_bytes;
}
