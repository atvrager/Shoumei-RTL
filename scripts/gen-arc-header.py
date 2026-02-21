#!/usr/bin/env python3
"""Generate C++ header from arcilator --state-file JSON.

Usage:
    python3 scripts/gen-arc-header.py <state.json> <output.h> [top_module]

Produces a header with:
  - Eval function declaration (extern "C")
  - Model wrapper struct with typed get/set accessors for all signals
  - Memory word write helper for ELF loading
"""

import json
import sys
import os


def main():
    if len(sys.argv) < 3:
        print(f"Usage: {sys.argv[0]} <state.json> <output.h> [top_module]", file=sys.stderr)
        sys.exit(1)

    state_path = sys.argv[1]
    output_path = sys.argv[2]
    top_hint = sys.argv[3] if len(sys.argv) > 3 else None

    with open(state_path) as f:
        data = json.load(f)

    # The JSON is a list of modules. Find the top module.
    if isinstance(data, list):
        modules = data
    else:
        modules = [data]

    # Find top module: by hint, or pick the one with most state bytes
    if top_hint:
        state = next((m for m in modules if m["name"] == top_hint), None)
        if not state:
            print(f"ERROR: module '{top_hint}' not found in {state_path}", file=sys.stderr)
            print(f"Available: {[m['name'] for m in modules]}", file=sys.stderr)
            sys.exit(1)
    else:
        state = max(modules, key=lambda m: m.get("numStateBytes", 0))

    module_name = state["name"]
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

    num_bytes = state.get("numStateBytes", 0)
    lines.append(f"// Total state size: {num_bytes} bytes")
    lines.append(f"static constexpr size_t {cpp_name}_STATE_SIZE = {num_bytes};")
    lines.append("")

    # Eval function declarations
    init_fn = state.get("initialFnSym", "")
    eval_fn = f"{cpp_name}_eval"
    final_fn = state.get("finalFnSym", "")

    lines.append(f'extern "C" void {eval_fn}(uint8_t* state);')
    if init_fn:
        lines.append(f'extern "C" void {init_fn}(uint8_t* state);')
    if final_fn:
        lines.append(f'extern "C" void {final_fn}(uint8_t* state);')
    lines.append("")

    # Model wrapper struct
    lines.append(f"struct {cpp_name}_model {{")
    lines.append(f"    alignas(16) uint8_t state[{cpp_name}_STATE_SIZE] = {{}};")
    lines.append("")
    lines.append(f"    void eval() {{ {eval_fn}(state); }}")
    if init_fn:
        lines.append(f"    void init() {{ {init_fn}(state); }}")
    lines.append("")

    states = state.get("states", [])

    for s in states:
        name = s.get("name", "")
        offset = s.get("offset", 0)
        num_bits = s.get("numBits", 0)

        cname = name.replace(".", "_").replace("[", "_").replace("]", "").replace("/", "_")
        if not cname:
            continue

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
            # Wide signal — raw byte access only
            lines.append(f"    // {name}: {num_bits} bits at offset {offset}")
            lines.append(f"    static constexpr size_t {cname}_OFFSET = {offset};")
            lines.append(f"    static constexpr size_t {cname}_BITS = {num_bits};")
            lines.append(f"    uint8_t* {cname}_ptr() {{ return &state[{offset}]; }}")
            lines.append("")
            continue

        if mask:
            lines.append(f"    {cpp_type} get_{cname}() const {{ {cpp_type} v; std::memcpy(&v, &state[{offset}], sizeof(v)); return v & {mask}; }}")
        else:
            lines.append(f"    {cpp_type} get_{cname}() const {{ {cpp_type} v; std::memcpy(&v, &state[{offset}], sizeof(v)); return v; }}")
        lines.append(f"    void set_{cname}({cpp_type} v) {{ std::memcpy(&state[{offset}], &v, sizeof(v)); }}")
        lines.append("")

    lines.append("};")
    lines.append("")
    lines.append(f"#endif // {cpp_name.upper()}_ARC_H")
    lines.append("")

    with open(output_path, "w") as f:
        f.write("\n".join(lines))

    print(f"Generated {output_path} for {module_name} ({len(states)} signals, {num_bytes} state bytes)")


if __name__ == "__main__":
    main()
