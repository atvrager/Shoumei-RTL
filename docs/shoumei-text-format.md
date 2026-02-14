# Design: Shoumei Text Format (`.shoumei`)

## Status: Draft
## Date: 2025-02

---

## 1. Motivation

Today, every circuit in the project is defined as a Lean 4 expression that builds a
`Circuit` value. This works well for formal verification — proofs attach directly to
these values — but it creates a barrier for hardware engineers who want to read, write,
or modify circuits without learning Lean.

The core DSL data model is simple: wires, gates, instances. A text format can expose
that structure directly, making circuit definitions accessible to anyone who has seen a
netlist or a structural Verilog file.

**Goals:**

1. A human-readable text format that maps 1:1 to `Circuit` values
2. A pretty printer (`Circuit → String`) that emits `.shoumei` files
3. A parser (`String → Except String Circuit`) that reads them back
4. Round-trip validation: parse a `.shoumei` file, generate SystemVerilog, LEC against
   the original Lean-generated SV — if it passes, the text format is semantically faithful
5. Eventually, large modules (including the CPU) can be authored and maintained as
   `.shoumei` files while proofs remain in Lean

**Non-goals:**

- Behavioral semantics (no `always` blocks, no expressions beyond gate application)
- Replacing Lean for proofs — the text format is a circuit *description*, not a proof language
- Synthesis pragmas, timing constraints, or other backend concerns

---

## 2. Relationship to the DSL

The text format is a direct serialization of the `Circuit` type from `DSL.lean`:

```
Circuit
├── name       : String
├── inputs     : List Wire
├── outputs    : List Wire
├── gates      : List Gate               -- 8 gate types
├── instances  : List CircuitInstance     -- hierarchical submodules
├── signalGroups  : List SignalGroup      -- bus annotations (codegen)
├── inputBundles  : List InterfaceBundle  -- interface annotations (codegen)
├── outputBundles : List InterfaceBundle  -- interface annotations (codegen)
├── rams          : List RAMPrimitive     -- RAM blocks (codegen)
└── keepHierarchy : Bool                  -- codegen hint
```

Every field has a representation in the text format. The core (name, inputs, outputs,
gates, instances) is expressed in the main syntax. The codegen annotations
(signalGroups, bundles, rams, keepHierarchy) are expressed as `@`-prefixed annotations,
since they don't affect circuit semantics and many circuits omit them entirely.

---

## 3. Text Format Specification

### 3.1 Module header

```
module <Name>(<inputs> -> <outputs>) {
  <body>
}
```

Inputs and outputs are comma-separated. Buses use bracket notation:

```
module ALU32(a[32], b[32], op[4] -> result[32])
```

Single-bit signals have no brackets:

```
module FullAdder(a, b, cin -> sum, cout)
```

Sequential circuits include `clock` and `reset` as regular inputs:

```
module Register32(d[32], clock, reset -> q[32])
```

**Mapping:**
- `a[32]` → `makeIndexedWires "a" 32` → `[Wire.mk "a_0", ..., Wire.mk "a_31"]`
- `a[32]` also generates `SignalGroup { name := "a", width := 32, wires := ... }`
- `cin` → `[Wire.mk "cin"]` (single wire, no signal group)
- Everything left of `->` is an input; everything right is an output

### 3.2 Gate statements

Each gate is a single line. The output wire is on the left, the gate type and inputs
on the right:

```
<output> = <GATE>(<input>, ...)
```

The eight gate types and their arities:

| Gate | Inputs | Example |
|------|--------|---------|
| `AND` | 2 | `x = AND(a, b)` |
| `OR` | 2 | `x = OR(a, b)` |
| `NOT` | 1 | `x = NOT(a)` |
| `XOR` | 2 | `x = XOR(a, b)` |
| `BUF` | 1 | `x = BUF(a)` |
| `MUX` | 3 | `x = MUX(in0, in1, sel)` — sel ? in1 : in0 |
| `DFF` | 3 | `q = DFF(d, clock, reset)` — async reset to 0 |
| `DFF_SET` | 3 | `q = DFF_SET(d, clock, reset)` — async reset to 1 |

Bus indexing in gate statements:

```
result[3] = AND(a[3], b[3])
```

Here `a[3]` refers to the wire `Wire.mk "a_3"` (the 4th wire of bus `a`).
This is indexing, not declaration — the bus must be declared in the module header
or as an internal bus.

### 3.3 Loop expansion

A `for` suffix on a gate statement replicates it across an index range:

```
result[i] = XOR(a[i], b[i])  for i in 0..32
```

This expands to 32 gate statements:

```
result[0] = XOR(a[0], b[0])
result[1] = XOR(a[1], b[1])
...
result[31] = XOR(a[31], b[31])
```

The range `0..N` means `[0, 1, ..., N-1]` (exclusive upper bound, matching
`List.range N` in Lean).

Loops can appear on any gate statement. The index variable can be used in any
wire reference within the statement.

Multiple loops are allowed (each on its own line). Nested loops are not supported —
if you need 2D indexing, flatten it.

### 3.4 Internal bus declarations

Wires that appear only inside the body (not in the header) are internal. Single
wires are inferred from usage — no declaration needed. Buses must be declared
explicitly so the parser knows their width:

```
module Subtractor32(a[32], b[32], one -> diff[32], borrow) {
  wire b_inv[32]
  wire ksa_sum[32]

  b_inv[i] = NOT(b[i])  for i in 0..32

  inst KoggeStoneAdder32 u_ksa(
    a = a, b = b_inv, cin = one
    -> sum = ksa_sum
  )

  diff[i] = BUF(ksa_sum[i])  for i in 0..32
  borrow = BUF(zero_internal)
  zero_internal = XOR(one, one)
}
```

**Mapping:** `wire b_inv[32]` creates `makeIndexedWires "b_inv" 32` and an internal
`SignalGroup`. Scalar internal wires (like `zero_internal` above) need no declaration;
they are created as `Wire.mk "zero_internal"` when first encountered.

### 3.5 Instance statements

Hierarchical instantiation uses `inst`:

```
inst <ModuleName> <instName>(
  <port> = <wire>, ...
  -> <port> = <wire>, ...
)
```

The `->` separates input port mappings from output port mappings. This distinction
is cosmetic in the text format (both become `portMap` entries in `CircuitInstance`)
but improves readability.

**Bus-to-bus connections:**

```
inst KoggeStoneAdder32 u_ksa(
  a = a, b = b_inv, cin = one
  -> sum = ksa_sum
)
```

When `a` is a bus (declared as `a[32]` in the header or as `wire a[32]`), and the
target module has ports `a0, a1, ..., a31`, the connection `a = a` expands to:

```
("a0", Wire.mk "a_0"), ("a1", Wire.mk "a_1"), ..., ("a31", Wire.mk "a_31")
```

This expansion requires knowing the submodule's port naming convention. The pretty
printer can always emit the expanded form; the parser supports both compressed and
expanded forms.

**Explicit per-bit mapping** (always valid, never ambiguous):

```
inst KoggeStoneAdder32 u_ksa(
  a0 = a[0], a1 = a[1], ..., a31 = a[31],
  b0 = b_inv[0], ...,
  cin = one
  -> sum0 = ksa_sum[0], ..., sum31 = ksa_sum[31]
)
```

### 3.6 Annotations

Optional `@`-prefixed directives placed between the module header and the opening
brace. These map to codegen-only fields on `Circuit` and have no effect on circuit
semantics or LEC.

**`@keepHierarchy`** — sets `Circuit.keepHierarchy := true`:

```
module PhysRegFile(...)
  @keepHierarchy
{
  ...
}
```

**`@ram`** — declares a `RAMPrimitive`:

```
module PhysRegFile(
  wr_en, wr_addr[6], wr_data[32],
  rd1_addr[6], rd2_addr[6],
  clock
  ->
  rd1_data[32], rd2_data[32]
)
  @ram RegFile {
    depth = 64, width = 32, sync = false,
    write(en = wr_en, addr = wr_addr, data = wr_data),
    read(addr = rd1_addr, data = rd1_data),
    read(addr = rd2_addr, data = rd2_data)
  }
{
  ...
}
```

**Mapping:**

```lean
RAMPrimitive {
  name := "RegFile", depth := 64, width := 32, syncRead := false,
  clock := Wire.mk "clock",
  writePorts := [{ en := Wire.mk "wr_en",
                   addr := makeIndexedWires "wr_addr" 6,
                   data := makeIndexedWires "wr_data" 32 }],
  readPorts := [{ addr := makeIndexedWires "rd1_addr" 6,
                  data := makeIndexedWires "rd1_data" 32 },
                { addr := makeIndexedWires "rd2_addr" 6,
                  data := makeIndexedWires "rd2_data" 32 }]
}
```

**`@bundle`** — declares an `InterfaceBundle` on an input or output group:

```
module Queue1_32(
  enq_bits[32], enq_valid, enq_ready,
  deq_ready, clock, reset
  ->
  deq_bits[32], deq_valid
)
  @bundle input enq { bits: UInt(32), valid: Bool, ready: Bool, protocol: decoupled }
  @bundle output deq { bits: UInt(32), valid: Bool, protocol: decoupled }
{
  ...
}
```

### 3.7 Comments

Line comments with `//`:

```
// Invert B for 2's complement subtraction
b_inv[i] = NOT(b[i])  for i in 0..32
```

Comments are discarded by the parser and not preserved in round-trips.

---

## 4. Full Example: Subtractor32

### As Lean today

```lean
def mkSubtractor32 : Circuit :=
  let n := 32
  let a := makeIndexedWires "a" n
  let b := makeIndexedWires "b" n
  let diff := makeIndexedWires "diff" n
  let borrow := Wire.mk "borrow"
  let one := Wire.mk "one"
  let b_inv := makeIndexedWires "b_inv" n
  let not_gates := List.zipWith (fun bw bi => Gate.mkNOT bw bi) b b_inv
  let ksa_sum := makeIndexedWires "ksa_sum" n
  let ksa_inst : CircuitInstance := {
    moduleName := "KoggeStoneAdder32"
    instName := "u_ksa_sub"
    portMap :=
      (List.range n |>.flatMap (fun i =>
        [ (s!"a{i}", a[i]!)
        , (s!"b{i}", b_inv[i]!)
        , (s!"sum{i}", ksa_sum[i]!)
        ]
      )) ++ [("cin", one)]
  }
  let diff_bufs := List.zipWith (fun src dst => Gate.mkBUF src dst) ksa_sum diff
  let zero_internal := Wire.mk "zero_internal"
  let zero_gen := Gate.mkXOR one one zero_internal
  let borrow_buf := Gate.mkBUF zero_internal borrow
  { name := "Subtractor32"
    inputs := a ++ b ++ [one]
    outputs := diff ++ [borrow]
    gates := not_gates ++ diff_bufs ++ [zero_gen, borrow_buf]
    instances := [ksa_inst]
    signalGroups := [
      { name := "a", width := n, wires := a },
      { name := "b", width := n, wires := b },
      { name := "diff", width := n, wires := diff },
      { name := "b_inv", width := n, wires := b_inv },
      { name := "ksa_sum", width := n, wires := ksa_sum }
    ]
    keepHierarchy := true
  }
```

### As `.shoumei`

```
module Subtractor32(a[32], b[32], one -> diff[32], borrow)
  @keepHierarchy
{
  wire b_inv[32]
  wire ksa_sum[32]

  // Invert B for 2's complement
  b_inv[i] = NOT(b[i])  for i in 0..32

  // A + ~B + 1 via Kogge-Stone adder
  inst KoggeStoneAdder32 u_ksa_sub(
    a = a, b = b_inv, cin = one
    -> sum = ksa_sum
  )

  // Route results
  diff[i] = BUF(ksa_sum[i])  for i in 0..32
  zero_internal = XOR(one, one)
  borrow = BUF(zero_internal)
}
```

20 lines of Lean → 16 lines of `.shoumei`. More importantly, the `.shoumei` version
requires no knowledge of Lean, list comprehensions, or the `Circuit` structure type.

---

## 5. Full Example: Queue1_32

A 1-entry decoupled FIFO — sequential, with DFFs and combinational control logic.

```
module Queue1_32(
  enq_bits[32], enq_valid, deq_ready, clock, reset
  ->
  enq_ready, deq_bits[32], deq_valid
)
  @bundle input enq { bits: UInt(32), valid: Bool, ready: Bool, protocol: decoupled }
  @bundle output deq { bits: UInt(32), valid: Bool, protocol: decoupled }
{
  // State: 32-bit data register + 1-bit valid register
  data_reg[i] = DFF(data_next[i], clock, reset)  for i in 0..32
  valid_reg = DFF(valid_next, clock, reset)

  // Handshake
  enq_ready = NOT(valid_reg)
  enq_fire = AND(enq_valid, enq_ready)
  deq_fire = AND(valid_reg, deq_ready)

  // Next-state logic
  not_deq_fire = NOT(deq_fire)
  valid_hold = AND(valid_reg, not_deq_fire)
  valid_next = OR(enq_fire, valid_hold)
  data_next[i] = MUX(data_reg[i], enq_bits[i], enq_fire)  for i in 0..32

  // Outputs
  deq_valid = BUF(valid_reg)
  deq_bits[i] = BUF(data_reg[i])  for i in 0..32
}
```

---

## 6. Implementation Plan

### 6.1 Architecture

All implementation lives in Lean. Two new modules under `lean/Shoumei/ShoumeiText/`:

```
lean/Shoumei/ShoumeiText/
├── Emit.lean          -- Pretty printer: Circuit → String
├── Parse.lean         -- Parser: String → Except String (List ParsedModule)
└── RoundTrip.lean     -- Round-trip test harness
```

Plus an executable entry point:

```
GenerateAllShoumei.lean   -- lake exe generate_all_shoumei
```

### 6.2 Pretty Printer (`Emit.lean`)

**Input:** `Circuit` value + optional `allCircuits` list (for submodule port direction lookup)

**Output:** `.shoumei` text string

**Key operations:**

1. **Bus detection.** Use `signalGroups` to identify buses. For a signal group
   `{ name := "a", width := 32, wires := [a_0, ..., a_31] }`, emit `a[32]` in the
   header instead of 32 separate wires. Wires not in any signal group emit as scalars.

2. **Header emission.** Partition wires into inputs and outputs, apply bus compression,
   emit `module Name(inputs -> outputs)`.

3. **Annotation emission.** Emit `@keepHierarchy`, `@ram`, `@bundle` directives from
   the corresponding `Circuit` fields.

4. **Gate emission.** For each gate, emit `output = GATE(inputs)`. Apply bus indexing:
   if the output wire is `Wire.mk "a_3"` and belongs to signal group `"a"`, emit
   `a[3]` instead of `a_3`.

5. **Loop compression** (optional, best-effort). Detect sequences of gates that differ
   only by index (e.g., 32 consecutive `XOR` gates on `a_0..a_31`). Emit as a single
   `for i in 0..32` line. If detection fails, emit individual lines — correctness is
   not affected.

6. **Instance emission.** For each `CircuitInstance`, emit `inst ModuleName instName(...)`.
   Compress per-bit port mappings to bus connections where possible.

**Estimated size:** ~150–200 lines of Lean.

### 6.3 Parser (`Parse.lean`)

**Input:** `.shoumei` text string

**Output:** `Except String (List Circuit)` — one `Circuit` per `module` block

**Parsing strategy:** Hand-rolled recursive descent using `String.Iterator` or
`Lean.Parsec`. The grammar is small enough that a parser combinator library is
overkill.

**Grammar (informal):**

```
file        = module*
module      = 'module' IDENT '(' portlist '->' portlist ')' annotations '{' body '}'
portlist    = port (',' port)*
port        = IDENT ('[' NAT ']')?
annotations = ('@' annotation)*
annotation  = 'keepHierarchy'
            | 'ram' IDENT '{' ram_body '}'
            | 'bundle' ('input'|'output') IDENT '{' bundle_body '}'
body        = (wire_decl | gate_stmt | inst_stmt | comment)*
wire_decl   = 'wire' IDENT '[' NAT ']'
gate_stmt   = wire_ref '=' GATE '(' wire_ref (',' wire_ref)* ')' for_clause?
inst_stmt   = 'inst' IDENT IDENT '(' port_map '->' port_map ')'
for_clause  = 'for' IDENT 'in' NAT '..' NAT
wire_ref    = IDENT ('[' (NAT | IDENT) ']')?
port_map    = (IDENT '=' wire_ref (',' IDENT '=' wire_ref)*)?
GATE        = 'AND' | 'OR' | 'NOT' | 'XOR' | 'BUF' | 'MUX' | 'DFF' | 'DFF_SET'
```

**Wire expansion rules:**

- `a[32]` in header → `makeIndexedWires "a" 32`
- `a[3]` in body → `Wire.mk "a_3"` (index lookup)
- `a[i]` in a `for` loop → `Wire.mk "a_{i}"` for each iteration value
- `cin` (no brackets) → `Wire.mk "cin"`

**Instance port expansion:**

When `a = a` appears in an `inst` block and `a` is a known bus of width 32, expand to:
`("a0", Wire.mk "a_0"), ("a1", Wire.mk "a_1"), ..., ("a31", Wire.mk "a_31")`

The port naming convention on the submodule side (e.g., `a0` vs `a_0`) must match
what the submodule's `Circuit` definition uses. The pretty printer will always emit
the expanded form if there's any ambiguity.

**Estimated size:** ~300–400 lines of Lean.

### 6.4 Round-Trip Test (`RoundTrip.lean`)

For each circuit in `allCircuits`:

1. Pretty-print to `.shoumei` text via `Emit`
2. Parse the text back via `Parse`
3. Generate SystemVerilog from the parsed `Circuit`
4. Write to `output/sv-roundtrip/<Name>.sv`

Then the existing LEC infrastructure compares `sv-from-lean/<Name>.sv` against
`sv-roundtrip/<Name>.sv`. If LEC passes, the round-trip is semantically faithful.

**What this validates:**
- The pretty printer doesn't lose information
- The parser reconstructs the circuit correctly
- Wire names, gate connectivity, and instance port maps survive the round-trip

**What this does NOT validate:**
- Comments (discarded by design)
- Whitespace and formatting (cosmetic)
- Signal group ordering (doesn't affect semantics)

### 6.5 Executable (`GenerateAllShoumei.lean`)

```lean
def main : IO Unit := do
  IO.FS.createDirAll "output/shoumei"
  IO.FS.createDirAll "output/sv-roundtrip"
  for c in allCircuits do
    -- Emit .shoumei
    let text := Circuit.toShoumei c allCircuits
    IO.FS.writeFile s!"output/shoumei/{c.name}.shoumei" text
    -- Round-trip: parse back, regenerate SV
    match parseShoumei text with
    | .ok circuits =>
      let reconstructed := circuits.head!
      let sv := SystemVerilog.toSystemVerilog reconstructed allCircuits
      IO.FS.writeFile s!"output/sv-roundtrip/{c.name}.sv" sv
    | .error msg =>
      IO.eprintln s!"Parse error for {c.name}: {msg}"
  IO.println s!"Generated {allCircuits.length} .shoumei files"
```

**lakefile entry:**

```lean
lean_exe generate_all_shoumei where
  root := `GenerateAllShoumei
```

### 6.6 LEC integration

Add a mode to `verification/run-lec.sh` that compares `sv-from-lean/` against
`sv-roundtrip/`:

```bash
./verification/run-lec.sh --roundtrip   # LEC sv-from-lean vs sv-roundtrip
```

This reuses the existing LEC infrastructure (SAT miter for combinational,
induction for sequential, compositional certs for large modules). No new
verification logic needed.

---

## 7. Implementation Phases

| Phase | Scope | Modules covered | Validates |
|-------|-------|-----------------|-----------|
| 1 | Flat combinational: gate emit/parse, scalars + buses, `for` loops | FullAdder, RippleCarryAdder32, LogicUnit32, XorArray, etc. | Basic round-trip, LEC on ~20 modules |
| 2 | Hierarchical combinational: `inst` emit/parse, bus port compression | Subtractor32, Comparator32, ALU32, MuxTree, etc. | Instance port maps survive round-trip |
| 3 | Sequential circuits: DFF/DFF_SET, clock/reset handling | Register32, Queue1_32, Counter, ShiftRegister, etc. | Sequential LEC (induction) |
| 4 | Annotations: `@keepHierarchy`, `@ram`, `@bundle` | PhysRegFile, QueueRAM, FreeList, etc. | Codegen metadata round-trips |
| 5 | Full coverage: all 89 modules | Everything including CPU_RV32IM | 100% LEC on round-trip SV |

Phase 1 is the critical path — it forces all syntax decisions to become concrete and
proves the pipeline works end-to-end. Phases 2–4 are incremental extensions. Phase 5
is the payoff.

---

## 8. Future Directions

### 8.1 `.shoumei` as source of truth

Once the round-trip is validated for all modules, `.shoumei` files can become the
primary authoring format:

```
hardware engineer writes .shoumei
  → parser produces Circuit
    → codegen produces SV + Chisel
      → LEC validates equivalence
  → Lean proofs attach to the Circuit value
```

The Lean definitions (`mkSubtractor32`, etc.) become generated artifacts rather than
hand-written code. Circuit authoring moves to a format that requires no Lean knowledge.

### 8.2 The CPU in `.shoumei`

`CPU_RV32IM.shoumei` would be a large file (~hundreds of lines) but entirely readable:

```
module CPU_RV32IM(clock, reset, imem_addr[32], ... -> ...)
  @keepHierarchy
{
  // === Fetch ===
  inst ProgramCounter u_pc(
    next_pc = next_pc, clock = clock, reset = reset
    -> pc = pc
  )

  // === Decode ===
  inst InstructionDecoder u_dec(
    insn = insn -> opcode = opcode, rd = rd, rs1 = rs1, ...
  )

  // === Execute ===
  inst ALU32 u_alu(a = alu_a, b = alu_b, op = alu_op -> result = alu_result)
  inst Multiplier32 u_mul(...)
  inst Divider32 u_div(...)

  // === Memory ===
  inst LoadStoreUnit u_lsu(...)

  // === Writeback ===
  inst PhysRegFile u_rf(...)

  // === Control ===
  next_pc = MUX(pc_plus_4, branch_target, branch_taken)
  pipeline_flush = OR(branch_taken, exception)
}
```

A hardware engineer can read this, understand the pipeline structure, and modify
wiring — without touching Lean. The formal proofs remain in Lean, attached to the
`Circuit` value that the parser produces from this file.

### 8.3 Parameterized modules

The current format does not support parameterized modules (the `N` in `mkRegisterN`).
A future extension could add:

```
module Register<N>(d[N], clock, reset -> q[N]) {
  q[i] = DFF(d[i], clock, reset)  for i in 0..N
}
```

This would require the parser to handle symbolic width parameters and deferred
expansion. For now, each concrete instantiation (Register32, Register64, etc.) is
its own module — matching how the Lean definitions work today.

### 8.4 IDE support

The grammar is simple enough for straightforward editor support:
- Syntax highlighting (VS Code, vim, emacs)
- Goto-definition for `inst` references
- Wire usage tracking (find all uses of a signal)
- Lint: unused wires, undriven outputs, width mismatches

### 8.5 External tooling

The text format could also serve as an interchange format:
- Import from structural Verilog (gate-level netlists)
- Export to other formal verification tools
- Programmatic generation from Python/TypeScript scripts

---

## 9. Design Decisions

| Decision | Choice | Rationale |
|----------|--------|-----------|
| Output on the left | `x = AND(a, b)` | Reads like assignment. Familiar from Verilog `assign`. |
| Explicit gate types | `AND`, `OR`, etc. | 1:1 with `GateType`. No ambiguity, no operator precedence. |
| `for` as suffix | `... for i in 0..N` | Python-inspired. Reads naturally. Trivially expandable. |
| `->` in module header | inputs `->` outputs | Clear I/O separation. Avoids `input`/`output` keywords per signal. |
| `->` in `inst` block | input ports `->` output ports | Same convention. Cosmetic only (both become `portMap` entries). |
| `@` annotations | Between header and `{` | Separates semantics from metadata. Can be ignored entirely. |
| No `wire` for scalars | Inferred from usage | Reduces boilerplate. Only buses need explicit `wire` declarations. |
| Bus naming: `a_0` not `a[0]` | Wire names use underscore | Matches existing `makeIndexedWires` convention. `a[0]` in text is sugar for `Wire.mk "a_0"`. |
| Comments not preserved | `//` comments are discarded | Simplifies round-trip. Comments can be re-added by humans. |
| No behavioral constructs | Structural only | Behavioral semantics live in Lean proofs. The text format is a netlist, not an HDL. |
| Implementation in Lean | Not Python/external | Stays in the build system. Parser output is a real `Circuit` value. Proofs can reference it directly. |

---

## 10. Grammar (Formal)

For reference, the complete grammar in approximate EBNF:

```ebnf
file          = { module } ;
module        = 'module' IDENT '(' portlist '->' portlist ')' { annotation } '{' { statement } '}' ;

portlist      = port { ',' port } ;
port          = IDENT [ '[' NAT ']' ] ;

annotation    = '@' 'keepHierarchy'
              | '@' 'ram' IDENT '{' ram_body '}'
              | '@' 'bundle' direction IDENT '{' bundle_body '}' ;
direction     = 'input' | 'output' ;
ram_body      = ram_field { ',' ram_field } ;
ram_field     = IDENT '=' value
              | 'write' '(' port_map ')'
              | 'read'  '(' port_map ')' ;
bundle_body   = bundle_field { ',' bundle_field } ;
bundle_field  = IDENT ':' type_expr
              | 'protocol' ':' IDENT ;
type_expr     = 'Bool' | 'UInt' '(' NAT ')' | 'SInt' '(' NAT ')' ;

statement     = wire_decl | gate_stmt | inst_stmt | comment ;
wire_decl     = 'wire' IDENT '[' NAT ']' ;
gate_stmt     = wire_ref '=' GATE '(' arglist ')' [ for_clause ] ;
inst_stmt     = 'inst' IDENT IDENT '(' port_map [ '->' port_map ] ')' ;

arglist       = wire_ref { ',' wire_ref } ;
for_clause    = 'for' IDENT 'in' NAT '..' NAT ;
wire_ref      = IDENT [ '[' ( NAT | IDENT ) ']' ] ;
port_map      = [ port_bind { ',' port_bind } ] ;
port_bind     = IDENT '=' wire_ref ;

GATE          = 'AND' | 'OR' | 'NOT' | 'XOR' | 'BUF' | 'MUX' | 'DFF' | 'DFF_SET' ;
IDENT         = letter { letter | digit | '_' } ;
NAT           = digit { digit } ;
comment       = '//' { any char except newline } ;
value         = NAT | 'true' | 'false' ;
```
