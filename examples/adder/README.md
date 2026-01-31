# Full Adder Example

This example demonstrates a 1-bit full adder circuit implemented in the Shoumei RTL DSL.

## Circuit Description

A full adder adds three single-bit inputs:
- `a`: First input bit
- `b`: Second input bit
- `cin`: Carry input bit

And produces two outputs:
- `sum`: Sum output bit
- `cout`: Carry output bit

## Truth Table

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

## Logic Equations

```
sum  = a ⊕ b ⊕ cin
cout = (a ∧ b) ∨ (cin ∧ (a ⊕ b))
```

## Circuit Implementation

The full adder is implemented in `lean/Shoumei/Examples/Adder.lean` using the following gates:

1. `ab_xor = a ⊕ b` - XOR gate for first two inputs
2. `sum = ab_xor ⊕ cin` - XOR gate for final sum
3. `ab_and = a ∧ b` - AND gate for first two inputs
4. `cin_ab = cin ∧ ab_xor` - AND gate for carry propagation
5. `cout = ab_and ∨ cin_ab` - OR gate for final carry

## Gate-Level Diagram

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

## Generated Outputs

When code generation is implemented, this example will generate:

- **SystemVerilog**: `output/sv-from-lean/FullAdder.sv`
- **Chisel**: `chisel/src/main/scala/generated/FullAdder.scala`
- **Compiled SV**: `output/sv-from-chisel/FullAdder.sv` (from Chisel via firtool)

## Verification

The logical equivalence checker (LEC) will verify that both SystemVerilog outputs are functionally identical.

## Building

```bash
# Generate code (TODO: not yet implemented)
make codegen

# Compile Chisel to SystemVerilog
make chisel

# Run equivalence checking
make lec

# Or run the entire pipeline
make all
```

## Next Steps

1. Implement code generation executable in LEAN
2. Fill in stubbed semantic evaluation functions
3. Prove correctness theorems about the full adder
4. Add more complex examples (ripple carry adder, etc.)
