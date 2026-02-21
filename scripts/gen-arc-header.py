#!/usr/bin/env python3
"""Generate C++ header from arcilator --state-file JSON.

Usage:
    python3 scripts/gen-arc-header.py <state.json> <output.h>

Produces a header with:
  - #include for arcilator runtime
  - State struct name and eval function declarations
  - Helper macros for accessing named signals by byte offset
  - Memory array accessor for direct ELF loading
"""

import json
import sys
import os
from pathlib import Path


def main():
    if len(sys.argv) != 3:
        print(f"Usage: {sys.argv[0]} <state.json> <output.h>", file=sys.stderr)
        sys.exit(1)

    state_path = sys.argv[1]
    output_path = sys.argv[2]

    with open(state_path) as f:
        state = json.load(f)

    module_name = state.get("name", "unknown")
    # Sanitize for C++ identifier
    cpp_name = module_name.replace(".", "_").replace("-", "_")

    lines = []
    lines.append(f"// Auto-generated arcilator header for {module_name}")
    lines.append(f"// Source: {os.path.basename(state_path)}")
    lines.append(f"// DO NOT EDIT - regenerate with: python3 scripts/gen-arc-header.py")
    lines.append("")
    lines.append(f"#ifndef {cpp_name.upper()}_ARC_H")
    lines.append(f"#define {cpp_name.upper()}_ARC_H")
    lines.append("")
    lines.append("#include <cstdint>")
    lines.append("#include <cstring>")
    lines.append("")

    # State buffer size
    num_bytes = state.get("numStateBytes", 0)
    lines.append(f"// Total state size: {num_bytes} bytes")
    lines.append(f"static constexpr size_t {cpp_name}_STATE_SIZE = {num_bytes};")
    lines.append("")

    # Eval function declaration (arcilator convention)
    lines.append(f'extern "C" void {cpp_name}_eval(uint8_t* state);')
    lines.append("")

    # Model wrapper struct
    lines.append(f"struct {cpp_name}_model {{")
    lines.append(f"    alignas(16) uint8_t state[{cpp_name}_STATE_SIZE] = {{}};")
    lines.append("")
    lines.append(f"    void eval() {{ {cpp_name}_eval(state); }}")
    lines.append("")

    # Generate accessors for each signal in the state
    # The state JSON has a "states" array with entries like:
    #   {"name": "clk", "offset": 0, "numBits": 1, "type": "input"}
    states = state.get("states", [])

    # Track memory signals for the mem accessor
    mem_offset = None
    mem_stride = None
    mem_depth = None

    for s in states:
        name = s.get("name", "")
        offset = s.get("offset", 0)
        num_bits = s.get("numBits", 0)
        sig_type = s.get("type", "")

        # Sanitize name for C++
        cname = name.replace(".", "_").replace("[", "_").replace("]", "").replace("/", "_")
        if not cname:
            continue

        # Choose C++ type
        if num_bits <= 1:
            cpp_type = "uint8_t"
            mask = "1"
        elif num_bits <= 8:
            cpp_type = "uint8_t"
            mask = f"0x{(1 << num_bits) - 1:x}"
        elif num_bits <= 16:
            cpp_type = "uint16_t"
            mask = f"0x{(1 << num_bits) - 1:x}"
        elif num_bits <= 32:
            cpp_type = "uint32_t"
            mask = f"0x{(1 << num_bits) - 1:x}" if num_bits < 32 else None
        elif num_bits <= 64:
            cpp_type = "uint64_t"
            mask = f"0x{(1 << num_bits) - 1:x}" if num_bits < 64 else None
        else:
            # Large signal - provide raw byte offset only
            lines.append(f"    // {name}: {num_bits} bits at offset {offset} (too wide for scalar accessor)")
            lines.append(f"    static constexpr size_t {cname}_OFFSET = {offset};")
            lines.append(f"    static constexpr size_t {cname}_BITS = {num_bits};")
            lines.append(f"    uint8_t* {cname}_ptr() {{ return &state[{offset}]; }}")
            lines.append("")

            # Detect memory arrays (large signals, usually named *mem* or *ram*)
            if "mem" in name.lower() or "ram" in name.lower():
                mem_offset = offset
                mem_stride = (num_bits + 7) // 8
            continue

        # Getter
        if mask:
            lines.append(f"    {cpp_type} get_{cname}() const {{ {cpp_type} v; std::memcpy(&v, &state[{offset}], sizeof(v)); return v & {mask}; }}")
        else:
            lines.append(f"    {cpp_type} get_{cname}() const {{ {cpp_type} v; std::memcpy(&v, &state[{offset}], sizeof(v)); return v; }}")

        # Setter
        lines.append(f"    void set_{cname}({cpp_type} v) {{ std::memcpy(&state[{offset}], &v, sizeof(v)); }}")
        lines.append("")

    # Memory word write helper (for ELF loading)
    # This writes a 32-bit word at a byte address into the state memory array
    lines.append("    // Write a 32-bit word to the memory region in the model state.")
    lines.append("    // byte_addr is the memory-space byte address.")
    lines.append("    // mem_base_offset and mem_word_stride must be configured for your design.")
    lines.append("    void write_mem_word(size_t mem_base_offset, uint32_t byte_addr, uint32_t data) {")
    lines.append("        size_t state_offset = mem_base_offset + byte_addr;")
    lines.append("        if (state_offset + 4 <= sizeof(state)) {")
    lines.append("            std::memcpy(&state[state_offset], &data, sizeof(data));")
    lines.append("        }")
    lines.append("    }")
    lines.append("")

    lines.append("};")
    lines.append("")
    lines.append(f"#endif // {cpp_name.upper()}_ARC_H")
    lines.append("")

    with open(output_path, "w") as f:
        f.write("\n".join(lines))

    print(f"Generated {output_path} ({len(states)} signals, {num_bytes} state bytes)")


if __name__ == "__main__":
    main()
