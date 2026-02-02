# TODO: Future Improvements

## High Priority

### Wire Naming Cleanup
**Problem**: Current wire names are ugly and inconsistent
**Examples**:
- Input wires: `issue_opcode0`, `issue_opcode1`, ... (no delimiters)
- Entry wires: `e00`, `e01`, `e013`, `e020` (ambiguous indexing)
- Should be: `issue_opcode[0]`, `entry[0].valid`, `entry[0].src1_ready`

**Impact**: Makes generated SV/Chisel hard to read and debug

**Solution Options**:
1. **Add wire naming conventions** to DSL
   - Support bracket notation: `mkWire "foo[3]"` → valid SV/Chisel array syntax
   - Support hierarchical naming: `mkWire "entry.0.valid"`
   - Codegen translates to language-specific syntax

2. **Structured wire types**
   - Add BusWire type: `BusWire { baseName : String, indices : List Nat }`
   - Auto-generates indexed names with proper delimiters
   - Example: `mkBus "opcode" 6` → opcode[0..5]

3. **Hierarchical circuit composition**
   - CircuitInstance port maps use structured names
   - Codegen flattens to valid identifiers per language
   - Example: `instance.port.bit` → `instance_port_bit` (SV) or `instance.port(bit)` (Chisel)

**Effort**: Medium (2-3 days)
**Priority**: High (affects all generated code readability)

---

## Medium Priority

### Priority Encoder Primitive
**Problem**: Converting one-hot → binary requires custom logic per use
**Current workaround**: Manual gate-level encoding in each circuit
**Solution**: Add `mkPriorityEncoder n` primitive
- Input: n-bit one-hot
- Output: log2(n)-bit binary
- Example: `mkPriorityEncoder 4` → 4-bit one-hot → 2-bit binary

**Effort**: Low (half day)
**Use cases**: RS4 dispatch, CDB arbitration, any mux selection from arbiter

---

## Low Priority

### Comparator Port Naming
**Issue**: Comparator has 5 outputs (eq, lt, ltu, gt, gtu) but most uses only need `eq`
**Current**: Must map all 5 ports even when unused
**Solution**: Support partial port mapping in CircuitInstance
- Only specify ports actually used
- Codegen leaves others dangling (OK for combinational logic)

**Effort**: Low (1 day)

---

## Notes

- Wire naming is the biggest usability issue right now
- Affects debugging, LEC verification, and collaboration
- Should fix before adding more complex circuits

**Created**: 2026-02-01
**Last Updated**: 2026-02-01
