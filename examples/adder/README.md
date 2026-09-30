# Full adder example

This example demonstrates a 1-bit full adder circuit implemented in the Shoumei RTL DSL.

## Circuit description

A full adder adds three single-bit inputs:
- `a`: First input bit
- `b`: Second input bit
- `cin`: Carry input bit

It produces two outputs:
- `sum`: Sum output bit
- `cout`: Carry output bit

## Truth table

| a | b | cin | sum | cout |
|---|---|-----|-----|------|
| 0 | 0 | 0   | 0   | 0    |
| 0 | 0 | 1   | 1   | 0    |
| 0 | 1 | 0   | 1   | 0    |
| 0 | 1 | 1   | 0   | 1    |
| 1 | 0 | 0   | 1   | 0    |
| 1 | 0 | 1   | 0   | 1    |
| 1 | 1 | 0   | 0   | 1    |
| 1 | 1 | 1   | 1   | 1    |

## Logic equations

```
sum  = a ⊕ b ⊕ cin
cout = (a ∧ b) ∨ (cin ∧ (a ⊕ b))
```

## Circuit implementation

The implementation lives in `lean/Shoumei/Examples/Adder.lean` and uses the following gates:

1. `ab_xor = a ⊕ b`: XOR gate for first two inputs
2. `sum = ab_xor ⊕ cin`: XOR gate for final sum
3. `ab_and = a ∧ b`: AND gate for first two inputs
4. `cin_ab = cin ∧ ab_xor`: AND gate for carry propagation
5. `cout = ab_and ∨ cin_ab`: OR gate for final carry

## Gate-level diagram

```
       a ─┬─────────┐
           │         │
       b ─┼────┬────┤ XOR ──┬─ ab_xor ─┬─────────┐
           │    │    │       │          │         │
       cin ┤    │    └───────┘          │         │
           │    │                       │         │ XOR ── sum
           │    │                       │         │
           │    └───────────────────────┘         │
           │                                      │
           │                           └──────────┘
           │
           ├────┬─── AND ── ab_and ─┬─────┐
           │    │                    │     │
           │    └────────────────────┘     │
           │                               │ OR ─── cout
           │                               │
           └────┬─── AND ── cin_ab ─┬──────┘
                │                   │
       cin ─────┴───────────────────┘
```

## Generated outputs

`bazel build //:rtl` emits, among others, for this circuit:

- **SystemVerilog**: `output/sv-from-lean/FullAdder.sv` (hierarchical)
- **Netlist SystemVerilog**: `output/sv-netlist/FullAdder.sv` (flat)
- **C++ simulation**: `output/cpp_sim/` (`.h` + `.cpp`)

## Verification

`lean/Shoumei/Examples/AdderProofs.lean` proves the full adder's truth table,
commutativity and arithmetic correctness in Lean. slang elaborates the emitted
SystemVerilog, and `bazel test //verification:smoke_test` checks its ports and
gate expressions.

## Building

```bash
# Generate code for all circuits
bazel build //:rtl

# Or run the presubmit verification suite
bazel test //:presubmit
```

## Next steps

1. Add more complex examples (ripple carry adder, and more)
