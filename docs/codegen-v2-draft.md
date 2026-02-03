# Codegen V2: Signal Naming & Output Modes

Draft sketches for the three code generation targets.
Feedback welcome -- nothing here is implemented yet.

## Decisions (locked in)

| Question | Decision | Notes |
|----------|----------|-------|
| Register type | **Option B: `ShoumeiReg` wrapper** | Thin helper, async reset, reset-to-zero, no hierarchy. Returns plain `UInt`. |
| Struct naming | **Option C: Hybrid auto-derive with dedup** | Auto-derive from annotations, canonicalize by field names + types |
| Netlist flattening | **Full flatten + RAM primitive** | Flatten everything to gates, but add RAM as a DSL primitive to stop at |
| Bus reconstruction | **Option A: Pattern-match in codegen** | Group gates by (type, shared control), check contiguous buses, emit vectorized |
| SV types | **`struct packed`** with `yosys-slang` | Shared SV package, `read_slang` for LEC |
| Chisel style | **Single-assign, no `when`** | Every signal has exactly one `:=`. Next-state is `Mux` chains. |
| Chisel Decoupled | **`ShoumeiDecoupled` wrapper** | Same philosophy as `ShoumeiReg` -- own our types, control naming |
| Multi-port RAM | **Option A: Configurable port lists** | `RAMPrimitive` has `writePorts : List RAMWritePort`, `readPorts : List RAMReadPort` |
| Mem vs SyncReadMem | **Flag on primitive** | `syncRead : Bool` on `RAMPrimitive`. `false` → `Mem` (async), `true` → `SyncReadMem` (sync) |
| LEC pairing | **Two pairs, trust transitivity** | netlist↔hier + hier↔Chisel. No direct netlist↔Chisel check needed. |
| Struct ports in LEC | **Flat ports everywhere** | Structs internal only. All module ports are flat → names match by construction. |
| Module vs RawModule | **Auto-detect** | Sequential → `Module`, combinational → `RawModule` |
| BlackBox escape | **Eliminated by bus reconstruction** | Keep as fallback only if vectorization doesn't collapse enough |
| RAM semantics | **Proved, no axioms** | Functional `RAM` model, properties by `simp`. LEC validates codegen matches. |

---

## Running Example: Queue1_32

A 1-entry, 32-bit decoupled FIFO queue.

**Ports:**
- `enq` (Decoupled sink): `enq.bits[31:0]`, `enq.valid`, `enq.ready`
- `deq` (Decoupled source): `deq.bits[31:0]`, `deq.valid`, `deq.ready`
- `clock`, `reset`

**Internals:**
- `data_reg[31:0]` -- 32 DFFs storing the data
- `valid_reg` -- 1 DFF tracking occupancy
- `enq_fire`, `deq_fire` -- handshake fires
- `valid_next`, `data_next[31:0]` -- next-state logic

---

## Current Output (for reference)

What the codegen produces today:

### Current SV

```systemverilog
module Queue1_32(enq_data_0, enq_data_1, ..., enq_data_31,
                 enq_valid, deq_ready, clock, reset,
                 enq_ready, data_reg_0, ..., data_reg_31, valid);
  input enq_data_0, enq_data_1, ..., enq_data_31;
  input enq_valid, deq_ready, clock, reset;
  output enq_ready;
  output reg data_reg_0, data_reg_1, ..., data_reg_31;
  output reg valid;

  wire enq_fire;
  wire deq_fire;
  wire not_deq_fire;
  wire valid_hold;
  wire valid_next;
  wire [31:0] data_next;

  assign enq_ready = ~valid;
  assign enq_fire = enq_valid & enq_ready;
  assign deq_fire = valid & deq_ready;
  assign not_deq_fire = ~deq_fire;
  assign valid_hold = valid & not_deq_fire;
  assign valid_next = enq_fire | valid_hold;
  assign data_next[0] = enq_fire ? enq_data_0 : data_reg_0;
  assign data_next[1] = enq_fire ? enq_data_1 : data_reg_1;
  // ... 30 more lines ...

  always @(posedge clock or posedge reset) begin
    if (reset) valid <= 1'b0;
    else       valid <= valid_next;
  end
  always @(posedge clock or posedge reset) begin
    if (reset) data_reg_0 <= 1'b0;
    else       data_reg_0 <= data_next_0;
  end
  // ... 31 more always blocks ...
endmodule
```

**Problems:**
1. Port names leak internal structure (`data_reg_0` instead of `deq_bits_0`)
2. Every bit is a separate port -- no buses
3. 32 individual `always` blocks instead of one
4. No struct grouping for the decoupled interface
5. When >200 ports: collapses to `inputs_0`, `inputs_1` ... total loss of semantics

### Current Chisel

```scala
class Queue1_32 extends RawModule {
  val clock = IO(Input(Clock()))
  val reset = IO(Input(AsyncReset()))
  val enq_data_0 = IO(Input(Bool()))
  val enq_data_1 = IO(Input(Bool()))
  // ... 30 more Bool inputs ...
  val enq_valid = IO(Input(Bool()))
  val deq_ready = IO(Input(Bool()))
  val enq_ready = IO(Output(Bool()))
  val data_reg_0 = IO(Output(Bool()))
  // ... 31 more Bool outputs ...
  val valid = IO(Output(Bool()))

  val data_reg_0_reg = withClockAndReset(clock, reset) { RegInit(false.B) }
  // ... 32 RegInit declarations ...

  val enq_fire = Wire(Bool())
  enq_fire := enq_valid & enq_ready
  // ... gate-by-gate assignments ...
}
```

**Problems:**
1. Everything is `Bool()` -- no `UInt`, no `Vec`, no `Bundle`
2. Individual `RegInit(false.B)` per bit
3. Chisel's type system is completely wasted

---

## Proposed: Mode 1 -- SV Netlist (Flat)

Everything flattened to primitives. No module hierarchy.
Signal names carry **full hierarchical path** so you know where each wire came from.

Use case: formal tools, ABC, equivalence checking, gate-level simulation.

```systemverilog
// Auto-generated by Shoumei -- netlist mode (flat)
// Source: Queue1_32
module Queue1_32(
  input  logic        clock,
  input  logic        reset,
  // -- enqueue interface --
  input  logic [31:0] enq_bits,
  input  logic        enq_valid,
  output logic        enq_ready,
  // -- dequeue interface --
  output logic [31:0] deq_bits,
  output logic        deq_valid,
  output logic        deq_ready   // note: deq_ready is an input in decoupled,
                                  // but the port direction is set by the protocol
);

  // === internal wires (hierarchical names from flattening) ===
  logic        ctrl__enq_fire;
  logic        ctrl__deq_fire;
  logic        ctrl__not_deq_fire;
  logic        ctrl__valid_hold;

  // === next-state ===
  logic        valid_next;
  logic [31:0] data_next;

  // === state (registers) ===
  logic        valid_reg;
  logic [31:0] data_reg;

  // === control logic ===
  assign enq_ready           = ~valid_reg;
  assign ctrl__enq_fire      = enq_valid & enq_ready;
  assign ctrl__deq_fire      = valid_reg & deq_ready;
  assign ctrl__not_deq_fire  = ~ctrl__deq_fire;
  assign ctrl__valid_hold    = valid_reg & ctrl__not_deq_fire;
  assign valid_next          = ctrl__enq_fire | ctrl__valid_hold;

  // === datapath mux (vectorized) ===
  assign data_next = ctrl__enq_fire ? enq_bits : data_reg;

  // === sequential elements ===
  always_ff @(posedge clock or posedge reset) begin
    if (reset) begin
      valid_reg <= 1'b0;
      data_reg  <= 32'b0;
    end else begin
      valid_reg <= valid_next;
      data_reg  <= data_next;
    end
  end

  // === output assignments ===
  assign deq_bits  = data_reg;
  assign deq_valid = valid_reg;

endmodule
```

**What changed vs. current:**
| Aspect | Current | Proposed |
|--------|---------|----------|
| Port style | `enq_data_0, enq_data_1, ...` (1 bit each) | `enq_bits [31:0]` (bus) |
| Port names | Leak internal names (`data_reg_0`) | Semantic interface names (`deq_bits`) |
| Internal wires | `enq_fire` | `ctrl__enq_fire` (hierarchy prefix) |
| DFF blocks | One `always` per bit | One `always_ff` block, vectorized |
| Bus detection | Heuristic (name suffix parsing) | Type-driven from DSL |
| SV style | Verilog-95 | SystemVerilog (logic, always_ff) |
| Bundled I/O hack | `inputs_0` for >200 ports | Never needed -- buses handle it |

**Hierarchical name convention for netlist mode:**
When a hierarchical module is flattened, internal wires get prefixed:
```
u_regfile__read_port__data[31:0]     -- from instance u_regfile, sub-block read_port
u_queue__ctrl__enq_fire              -- from instance u_queue, control section
```
Double underscore `__` separates hierarchy levels (single `_` stays in signal names).

---

## Proposed: Mode 2 -- SV Hierarchical

Like a human would write it. Module instantiation, SV structs for interfaces.

Use case: synthesis, readable RTL, waveform debugging.

### Struct Definitions (shared header or per-package)

```systemverilog
// Auto-generated by Shoumei -- interface definitions
// File: shoumei_interfaces.svh (or package)

typedef struct packed {
  logic [31:0] bits;
  logic        valid;
  logic        ready;
} decoupled32_t;

// Other commonly-used structs
typedef struct packed {
  logic [31:0] addr;
  logic [31:0] data;
  logic [1:0]  size;
} mem_req_t;

typedef struct packed {
  logic [5:0]  phys_rd;
  logic [4:0]  arch_rd;
  logic        valid;
} rename_entry_t;
```

### Module Output

```systemverilog
// Auto-generated by Shoumei -- hierarchical mode
// Source: Queue1_32
module Queue1_32(
  input  logic           clock,
  input  logic           reset,
  // -- enqueue (sink) --
  input  logic [31:0]    enq_bits,
  input  logic           enq_valid,
  output logic           enq_ready,
  // -- dequeue (source) --
  output logic [31:0]    deq_bits,
  output logic           deq_valid,
  input  logic           deq_ready
);

  // --- state ---
  logic        valid_reg;
  logic [31:0] data_reg;

  // --- control ---
  logic enq_fire, deq_fire;

  assign enq_ready = ~valid_reg;
  assign enq_fire  = enq_valid & enq_ready;
  assign deq_fire  = deq_valid & deq_ready;

  // --- next-state ---
  logic        valid_next;
  logic [31:0] data_next;

  assign valid_next = enq_fire | (valid_reg & ~deq_fire);
  assign data_next  = enq_fire ? enq_bits : data_reg;

  // --- flops ---
  always_ff @(posedge clock or posedge reset) begin
    if (reset) begin
      valid_reg <= 1'b0;
      data_reg  <= '0;
    end else begin
      valid_reg <= valid_next;
      data_reg  <= data_next;
    end
  end

  // --- outputs ---
  assign deq_bits  = data_reg;
  assign deq_valid = valid_reg;

endmodule
```

### Hierarchical Example: Queue4_32 (4-entry Queue)

Shows real module instantiation with struct-typed ports.

```systemverilog
module Queue4_32(
  input  logic           clock,
  input  logic           reset,
  input  logic [31:0]    enq_bits,
  input  logic           enq_valid,
  output logic           enq_ready,
  output logic [31:0]    deq_bits,
  output logic           deq_valid,
  input  logic           deq_ready
);

  // --- pointer / count state ---
  logic [1:0] head_ptr, tail_ptr;
  logic [2:0] count;
  logic       full, empty;

  assign full  = (count == 3'd4);
  assign empty = (count == 3'd0);

  // --- storage: 4 x 32-bit register bank ---
  logic [31:0] mem [0:3];

  // --- control ---
  logic enq_fire, deq_fire;

  assign enq_ready = ~full;
  assign enq_fire  = enq_valid & enq_ready;
  assign deq_valid = ~empty;
  assign deq_fire  = deq_valid & deq_ready;

  // --- pointer update ---
  always_ff @(posedge clock or posedge reset) begin
    if (reset) begin
      head_ptr <= '0;
      tail_ptr <= '0;
      count    <= '0;
    end else begin
      if (enq_fire) tail_ptr <= tail_ptr + 1'b1;
      if (deq_fire) head_ptr <= head_ptr + 1'b1;
      case ({enq_fire, deq_fire})
        2'b10:   count <= count + 1'b1;
        2'b01:   count <= count - 1'b1;
        default: count <= count;   // 2'b00 or 2'b11
      endcase
    end
  end

  // --- memory write ---
  always_ff @(posedge clock) begin
    if (enq_fire)
      mem[tail_ptr] <= enq_bits;
  end

  // --- memory read ---
  assign deq_bits = mem[head_ptr];

endmodule
```

### Bigger Hierarchical Example: ReservationStation

Shows struct ports + submodule instantiation.

```systemverilog
module ReservationStation4(
  input  logic            clock,
  input  logic            reset,
  // -- dispatch (write) --
  input  rs_entry_t       dispatch_data,
  input  logic            dispatch_valid,
  output logic            dispatch_ready,
  // -- issue (read, oldest-ready) --
  output rs_entry_t       issue_data,
  output logic            issue_valid,
  input  logic            issue_ready,
  // -- CDB broadcast (wake-up) --
  input  cdb_entry_t      cdb          [0:3],
  input  logic [3:0]      cdb_valid,
  // -- flush --
  input  logic            flush
);

  // --- entry storage ---
  rs_entry_t  entries [0:3];
  logic [3:0] entry_valid;
  logic [3:0] entry_ready;   // src1_ready & src2_ready

  // --- submodule: age-based priority picker ---
  PriorityPicker4 u_picker(
    .valid     (entry_valid & entry_ready),
    .grant     (issue_grant)
  );

  // --- submodule: CAM for wakeup matching ---
  genvar i;
  generate
    for (i = 0; i < 4; i++) begin : gen_wakeup
      WakeupLogic u_wakeup(
        .entry     (entries[i]),
        .cdb       (cdb),
        .cdb_valid (cdb_valid),
        .wakeup    (wakeup[i])
      );
    end
  endgenerate

  // ...
endmodule
```

---

## Proposed: Mode 3 -- Chisel Hierarchical

Proper Chisel idioms: `Bundle`, `Decoupled`, `Vec`, `UInt`.

### Bundle Definitions (shared file)

```scala
// Auto-generated by Shoumei -- Chisel bundles
// File: generated/Interfaces.scala
package generated

import chisel3._
import chisel3.util._

/** Rename mapping entry */
class RenameEntry extends Bundle {
  val physRd = UInt(6.W)
  val archRd = UInt(5.W)
  val valid  = Bool()
}

/** Memory request */
class MemReq extends Bundle {
  val addr = UInt(32.W)
  val data = UInt(32.W)
  val size = UInt(2.W)
}

/** CDB broadcast entry */
class CDBEntry extends Bundle {
  val tag  = UInt(6.W)
  val data = UInt(32.W)
}
```

### Module Output: Queue1_32

```scala
// Auto-generated by Shoumei -- Chisel hierarchical mode
// Source: Queue1_32
package generated

import chisel3._
import chisel3.util._

class Queue1_32 extends Module {
  val io = IO(new Bundle {
    // enqueue (sink)
    val enq_bits  = Input(UInt(32.W))
    val enq_valid = Input(Bool())
    val enq_ready = Output(Bool())
    // dequeue (source)
    val deq_bits  = Output(UInt(32.W))
    val deq_valid = Output(Bool())
    val deq_ready = Input(Bool())
  })

  // --- state ---
  val valid_reg = ShoumeiReg.bool(clock, reset)
  val data_reg  = ShoumeiReg(32, clock, reset)

  // --- control (single assign per signal) ---
  val enq_fire = Wire(Bool())
  val deq_fire = Wire(Bool())

  io.enq_ready := ~valid_reg
  io.deq_valid := valid_reg
  enq_fire     := io.enq_valid & io.enq_ready
  deq_fire     := io.deq_valid & io.deq_ready

  // --- next-state (pure combinational, Mux only) ---
  val valid_next = Wire(Bool())
  val data_next  = Wire(UInt(32.W))

  valid_next := enq_fire | (valid_reg & ~deq_fire)
  data_next  := Mux(enq_fire, io.enq_bits, data_reg)

  // --- register update (exactly one := per reg) ---
  valid_reg := valid_next
  data_reg  := data_next

  // --- output ---
  io.deq_bits := data_reg
}
```

### Hierarchical Example: Queue4_32

```scala
class Queue4_32 extends Module {
  val io = IO(new Bundle {
    val enq_bits  = Input(UInt(32.W))
    val enq_valid = Input(Bool())
    val enq_ready = Output(Bool())
    val deq_bits  = Output(UInt(32.W))
    val deq_valid = Output(Bool())
    val deq_ready = Input(Bool())
  })

  // --- pointer / count ---
  val head_ptr = ShoumeiReg(2, clock, reset)
  val tail_ptr = ShoumeiReg(2, clock, reset)
  val count    = ShoumeiReg(3, clock, reset)

  val full  = count === 4.U
  val empty = count === 0.U

  // --- storage (RAM primitive) ---
  val mem = ShoumeiMem(4, 32)  // depth=4, width=32

  // --- control ---
  io.enq_ready := ~full
  io.deq_valid := ~empty

  val enq_fire = Wire(Bool())
  val deq_fire = Wire(Bool())
  enq_fire := io.enq_valid & io.enq_ready
  deq_fire := io.deq_valid & io.deq_ready

  // --- next-state (single assign, Mux only, no when) ---
  val head_next = Wire(UInt(2.W))
  val tail_next = Wire(UInt(2.W))
  val count_next = Wire(UInt(3.W))

  tail_next := Mux(enq_fire, tail_ptr + 1.U, tail_ptr)
  head_next := Mux(deq_fire, head_ptr + 1.U, head_ptr)
  count_next := Mux(enq_fire & ~deq_fire, count + 1.U,
                Mux(~enq_fire & deq_fire, count - 1.U,
                    count))

  // --- register update (one := per reg) ---
  head_ptr := head_next
  tail_ptr := tail_next
  count    := count_next

  // --- memory (write uses enable arg, not when) ---
  mem.write(tail_ptr, io.enq_bits, enq_fire)
  io.deq_bits := mem.read(head_ptr)
}
```

### Bigger Hierarchical: ReservationStation

```scala
class RSEntry extends Bundle {
  val opcode    = UInt(4.W)
  val src1_tag  = UInt(6.W)
  val src1_data = UInt(32.W)
  val src1_rdy  = Bool()
  val src2_tag  = UInt(6.W)
  val src2_data = UInt(32.W)
  val src2_rdy  = Bool()
  val dst_tag   = UInt(6.W)
}

class ReservationStation4 extends Module {
  val io = IO(new Bundle {
    // dispatch (sink)
    val dispatch_opcode    = Input(UInt(4.W))
    val dispatch_src1_rdy  = Input(Bool())
    val dispatch_src1_tag  = Input(UInt(6.W))
    val dispatch_src1_data = Input(UInt(32.W))
    val dispatch_src2_rdy  = Input(Bool())
    val dispatch_src2_tag  = Input(UInt(6.W))
    val dispatch_src2_data = Input(UInt(32.W))
    val dispatch_dst_tag   = Input(UInt(6.W))
    val dispatch_valid     = Input(Bool())
    val dispatch_ready     = Output(Bool())
    // issue (source)
    val issue_opcode    = Output(UInt(4.W))
    val issue_src1_data = Output(UInt(32.W))
    val issue_src2_data = Output(UInt(32.W))
    val issue_dst_tag   = Output(UInt(6.W))
    val issue_valid     = Output(Bool())
    val issue_ready     = Input(Bool())
    // CDB broadcast (4 ports)
    val cdb_0_tag   = Input(UInt(6.W))
    val cdb_0_data  = Input(UInt(32.W))
    val cdb_0_valid = Input(Bool())
    val cdb_1_tag   = Input(UInt(6.W))
    val cdb_1_data  = Input(UInt(32.W))
    val cdb_1_valid = Input(Bool())
    val cdb_2_tag   = Input(UInt(6.W))
    val cdb_2_data  = Input(UInt(32.W))
    val cdb_2_valid = Input(Bool())
    val cdb_3_tag   = Input(UInt(6.W))
    val cdb_3_data  = Input(UInt(32.W))
    val cdb_3_valid = Input(Bool())
    // flush
    val flush = Input(Bool())
  })

  // --- entry storage (registered state) ---
  val entries     = Reg(Vec(4, new RSEntry))
  val entry_valid = RegInit(VecInit(Seq.fill(4)(false.B)))

  // --- combinational readiness ---
  val entry_ready = Wire(Vec(4, Bool()))
  (0 until 4).foreach { i =>
    entry_ready(i) := entries(i).src1_rdy & entries(i).src2_rdy
  }

  // --- age-based picker (submodule) ---
  val u_picker = Module(new PriorityPicker4)
  u_picker.io.valid := entry_valid.asUInt & entry_ready.asUInt

  // --- CDB wakeup: compute next entry state (pure Mux, no when) ---
  val entries_next = Wire(Vec(4, new RSEntry))
  (0 until 4).foreach { i =>
    // Start with current entry
    var src1_rdy_next  = entries(i).src1_rdy
    var src1_data_next = entries(i).src1_data
    var src2_rdy_next  = entries(i).src2_rdy
    var src2_data_next = entries(i).src2_data

    // Chain Muxes for each CDB port (priority: last CDB wins)
    (0 until 4).foreach { j =>
      val src1_match = io.cdb(j).valid & ~entries(i).src1_rdy &
                       (entries(i).src1_tag === io.cdb(j).bits.tag)
      val src2_match = io.cdb(j).valid & ~entries(i).src2_rdy &
                       (entries(i).src2_tag === io.cdb(j).bits.tag)

      src1_rdy_next  = Mux(src1_match, true.B,            src1_rdy_next)
      src1_data_next = Mux(src1_match, io.cdb(j).bits.data, src1_data_next)
      src2_rdy_next  = Mux(src2_match, true.B,            src2_rdy_next)
      src2_data_next = Mux(src2_match, io.cdb(j).bits.data, src2_data_next)
    }

    entries_next(i)          := entries(i)       // default: hold
    entries_next(i).src1_rdy  := src1_rdy_next
    entries_next(i).src1_data := src1_data_next
    entries_next(i).src2_rdy  := src2_rdy_next
    entries_next(i).src2_data := src2_data_next
  }

  // --- dispatch: compute next valid + entry (Mux, no when) ---
  val free_slot = PriorityEncoder(~entry_valid.asUInt)
  io.dispatch.ready := ~entry_valid.asUInt.andR

  val dispatch_fire = io.dispatch.valid & io.dispatch.ready
  val entry_valid_after_dispatch = Wire(Vec(4, Bool()))
  val entries_after_dispatch     = Wire(Vec(4, new RSEntry))
  (0 until 4).foreach { i =>
    val is_target = dispatch_fire & (free_slot === i.U)
    entry_valid_after_dispatch(i) := Mux(is_target, true.B,              entry_valid(i))
    entries_after_dispatch(i)     := Mux(is_target, io.dispatch.bits,    entries_next(i))
  }

  // --- issue: compute next valid (Mux, no when) ---
  io.issue.valid := (entry_valid.asUInt & entry_ready.asUInt).orR
  io.issue.bits  := entries(u_picker.io.grant)

  val issue_fire = io.issue.valid & io.issue.ready
  val entry_valid_after_issue = Wire(Vec(4, Bool()))
  (0 until 4).foreach { i =>
    val is_issued = issue_fire & (u_picker.io.grant === i.U)
    entry_valid_after_issue(i) := Mux(is_issued, false.B,
                                      entry_valid_after_dispatch(i))
  }

  // --- flush: compute final next valid (Mux, no when) ---
  val entry_valid_next = Wire(Vec(4, Bool()))
  (0 until 4).foreach { i =>
    entry_valid_next(i) := Mux(io.flush, false.B, entry_valid_after_issue(i))
  }

  // --- register update (exactly one := per reg) ---
  (0 until 4).foreach { i =>
    entries(i)     := entries_after_dispatch(i)
    entry_valid(i) := entry_valid_next(i)
  }
}
```

---

## DSL Changes Required

To support the above, the DSL needs type information.

### Option A: Lightweight -- Signal Groups (minimal DSL change)

Add a `SignalGroup` annotation layer on top of existing `Wire`:

```lean
-- Annotation: groups of wires that form a logical signal
structure SignalGroup where
  name     : String
  wires    : List Wire
  width    : Nat            -- bit width (wires.length)
  deriving Repr

-- Annotation: interface bundle (group of groups)
structure InterfaceBundle where
  name     : String
  signals  : List SignalGroup
  protocol : Option String  -- "decoupled", "valid", "none"
  deriving Repr

-- Circuit gets optional annotations (backward compatible)
structure Circuit where
  name      : String
  inputs    : List Wire
  outputs   : List Wire
  gates     : List Gate
  instances : List CircuitInstance
  -- v2 annotations (optional, codegen uses if present)
  signalGroups : List SignalGroup := []
  interfaces   : List InterfaceBundle := []
```

**Pro:** Backward compatible. Existing circuits still work. Annotations are additive.
**Con:** Two sources of truth (wire list + annotations). Can get out of sync.

### Option B: Full -- Typed Wires (bigger DSL change)

```lean
-- Signal types
inductive SignalType where
  | Bool                                        -- 1 bit
  | UInt (width : Nat)                          -- unsigned multi-bit
  | SInt (width : Nat)                          -- signed multi-bit
  | Struct (name : String) (fields : List (String x SignalType))
  | Vec (n : Nat) (elem : SignalType)
  deriving Repr

-- Typed port (replaces Wire for I/O)
structure Port where
  name      : String
  type      : SignalType
  direction : Direction    -- In | Out | Flip (for decoupled)
  deriving Repr

-- Circuit v2
structure Circuit where
  name      : String
  ports     : List Port            -- replaces inputs/outputs
  gates     : List Gate            -- still flat for netlist core
  instances : List CircuitInstance
```

**Pro:** Single source of truth. Type info flows through entire pipeline.
**Con:** Large refactor. Every circuit definition, proof, codegen needs updating.

### Recommendation

**Start with Option A.** Ship the three output modes with annotations.
Migrate to Option B incrementally as the RV32IM build-out demands richer types.

The key insight: the **flat gate list is still the proof core**. The annotations
are for codegen only. This preserves all existing proofs.

---

## Signal Naming Rules

### Port Names

| Current | Proposed | Rationale |
|---------|----------|-----------|
| `enq_data_0` ... `enq_data_31` | `enq_bits[31:0]` | Bus, matches Decoupled convention |
| `data_reg_0` (as output) | `deq_bits[31:0]` | Interface name, not internal name |
| `valid` (as output) | `deq_valid` | Scoped to interface |
| `enq_valid` | `enq_valid` | Already good |
| `deq_ready` | `deq_ready` | Already good |
| `inputs_0` ... `inputs_N` | Never happens | Buses + structs handle any port count |

### Internal Wire Names

| Current | Proposed (hierarchical) | Proposed (netlist) |
|---------|------------------------|-------------------|
| `enq_fire` | `enq_fire` | `ctrl__enq_fire` |
| `data_next_0` | `data_next[0]` | `data_next[0]` |
| `valid_hold` | `valid_hold` | `ctrl__valid_hold` |
| `_wires(42)` | Never happens | Never happens |

### Hierarchy Separator

- Single underscore `_` : within a signal name (`enq_fire`, `data_reg`)
- Double underscore `__` : hierarchy level in netlist mode (`u_queue__ctrl__fire`)
- Dot `.` : SV hierarchical reference in waveforms (`u_queue.ctrl.fire`)

---

## LEC Implications

The current LEC flow compares Lean SV vs. Chisel SV bit-for-bit. With three modes:

| Lean Output | Chisel Output | LEC Method |
|-------------|---------------|------------|
| SV Netlist | -- | Self-consistent (single source) |
| SV Hierarchical | Chisel Hierarchical (via CIRCT) | Existing SEC/SAT flow |
| SV Netlist | SV Hierarchical | Flatten-and-compare (Yosys `flatten`) |

The netlist mode is the "ground truth" for proofs. The hierarchical modes must
be provably equivalent to it. This is easier than the current situation because
both hierarchical modes share the same structure -- only syntax differs.

---

## Open Questions (Detailed)

---

### Q1: Struct Naming -- Auto-derived or Manually Specified?

The question is whether struct types should be created automatically from
`InterfaceBundle` annotations, or defined once in a shared library.

#### The real interface shapes in our codebase today

Looking at what the RISC-V modules actually use, there are ~7 distinct shapes:

```
Shape 1: Decoupled (ready/valid handshake)
  {name}_bits[W-1:0], {name}_valid, {name}_ready
  Used by: Queue enq/deq ports

Shape 2: Operand bundle (reservation station source operand)
  {src}_ready, {src}_tag[5:0], {src}_data[31:0]
  Used by: ReservationStation4 issue_src1, issue_src2, dispatch_src1, dispatch_src2

Shape 3: CDB broadcast
  cdb_valid, cdb_tag[5:0], cdb_data[31:0]
  Used by: ReservationStation4 CDB input

Shape 4: Register write port
  {name}_en, {name}_addr[N-1:0], {name}_data[W-1:0]
  Used by: RAT write port, PhysRegFile write port

Shape 5: Register read port
  {name}_addr[N-1:0], {name}_data[W-1:0]
  Used by: RAT rs1/rs2, PhysRegFile rd1/rd2

Shape 6: Dispatch entry (full RS entry)
  dispatch_en, dispatch_opcode[5:0], dispatch_dest_tag[5:0],
  dispatch_src1_ready, dispatch_src1_tag[5:0], dispatch_src1_data[31:0],
  dispatch_src2_ready, dispatch_src2_tag[5:0], dispatch_src2_data[31:0]
  Used by: ReservationStation4 dispatch input

Shape 7: Issue output
  issue_valid, issue_opcode[5:0], issue_dest_tag[5:0],
  issue_src1_data[31:0], issue_src2_data[31:0]
  Used by: ReservationStation4 issue output
```

#### Option A: Auto-derive per module

Each module declares its own struct shapes inline. The codegen infers struct
definitions from `InterfaceBundle` annotations.

```systemverilog
// Auto-generated for ReservationStation4 -- unique to this module
typedef struct packed {
  logic        ready;
  logic [5:0]  tag;
  logic [31:0] data;
} ReservationStation4_operand_t;
```

**Pro:** No manual struct library to maintain. Each module is self-contained.
**Con:** If Queue and RS both have a 32-bit decoupled port, they generate
two separate struct types. A parent module that connects them needs a cast.
Struct name proliferation: `Queue1_32_deq_t` vs `RS4_dispatch_decoupled_t`
for the same shape.

#### Option B: Shared struct library (manually defined)

Define a canonical set of interface types in one place:

```lean
-- In DSL/Interfaces.lean
def operandBundle : InterfaceShape := {
  name := "operand"
  fields := [("ready", Bool), ("tag", UInt 6), ("data", UInt 32)]
}
def cdbEntry : InterfaceShape := {
  name := "cdb_entry"
  fields := [("valid", Bool), ("tag", UInt 6), ("data", UInt 32)]
}
```

Generates a shared header:
```systemverilog
// shoumei_types.svh -- shared across all modules
typedef struct packed { logic ready; logic [5:0] tag; logic [31:0] data; } operand_t;
typedef struct packed { logic valid; logic [5:0] tag; logic [31:0] data; } cdb_entry_t;
```

**Pro:** Canonical types. Connecting modules is trivial (same type = same struct).
**Con:** Need to maintain the library. New interface shapes require explicit
addition. Can't just define a circuit and have it "work".

#### Option C: Hybrid -- auto-derive with dedup

The codegen auto-derives struct types, but canonicalizes by shape.
Two interfaces with identical field types and widths get the same struct name,
regardless of which module they appear in.

```
operand_t  = {ready: Bool, tag: UInt(6), data: UInt(32)}
cdb_entry_t = {valid: Bool, tag: UInt(6), data: UInt(32)}
```

These have the same bit layout but different field names. Options:
- Same struct (field names ignored)? Loses semantic info.
- Different structs (field names matter)? Keeps meaning, minimal dedup.

**Decision: Option C (hybrid).** Auto-derive struct types from annotations,
but canonicalize by field names + types. Two interfaces with the same fields
(`ready: Bool, tag: UInt(6), data: UInt(32)`) get the same struct name.
Different field names = different struct, even if bit layout is identical
(`operand_t` vs `cdb_entry_t`). The shared interface library (`Interfaces.lean`)
provides canonical names for the common shapes; module-specific shapes get
auto-derived names.

---

### Q2: Netlist Flattening Depth

In netlist mode, how deep do we flatten?

#### Current hierarchy levels in the project

```
Level 0 (top): ReservationStation4, StoreBuffer8, CPU (future)
Level 1:       Queue64_32, PhysRegFile_64x32, RAT_32x6
Level 2:       Register91, QueueRAM_64x32, Mux64x32, Mux32x6
Level 3:       Register64, Register16, Register8, Register2, Register1
Level 4:       Individual DFF gates
```

#### Option A: Flatten to gates (full netlist)

Every module decomposed to AND/OR/NOT/XOR/MUX/DFF primitives. No instances
remain. This is what `Circuit.inline` already does for combinational logic.

```systemverilog
// Queue64_32 fully flattened: ~4000+ gates
module Queue64_32(...);
  // hierarchical names preserve origin
  logic u_mem__reg_0_to_63__dff_0;
  logic u_mem__reg_0_to_63__dff_1;
  // ... thousands of wires ...
  assign u_ctrl__enq_fire = enq_valid & u_ctrl__enq_ready;
  // ... thousands of assigns ...
  always_ff @(posedge clock or posedge reset) begin
    if (reset) u_mem__reg_0_to_63__dff_0 <= 1'b0;
    else       u_mem__reg_0_to_63__dff_0 <= u_mem__reg_0_to_63__dff_0_next;
  end
  // ... thousands of always blocks ...
endmodule
```

**Pro:** Single module, no dependencies. ABC/formal tools get everything.
Hierarchical names tell you where each wire came from.
**Con:** Huge files for big modules. Queue64_32 would be ~4000 gates.
PhysRegFile_64x32 would be ~130K gates. Not human-readable at all.
No RAM inference (synth tools can't reconstruct `Mem` from flat DFFs).

#### Option B: Flatten to "technology primitives"

Stop at primitives that map to real FPGA/ASIC cells:
- DFF (flip-flop)
- Single-bit gates (AND, OR, NOT, XOR)
- MUX
- But NOT: RAM blocks, register files, multiplexer trees

This means some submodules stay as instances:

```systemverilog
// Queue64_32 partially flattened
module Queue64_32(...);
  // Control logic is flat gates
  assign ctrl__enq_fire = enq_valid & ctrl__enq_ready;
  // ...
  // Storage stays as an instance (RAM primitive)
  QueueRAM_64x32 u_mem(
    .wr_addr(tail_ptr),
    .wr_data(enq_bits),
    .rd_addr(head_ptr),
    .rd_data(deq_bits),
    // ...
  );
endmodule
```

**Pro:** Synth tools can infer RAM blocks. Reasonable file sizes.
**Con:** Not truly flat. Need to define what counts as a "technology primitive".

#### Option C: User-controlled depth

A parameter controls how many hierarchy levels to flatten:
- `depth=0`: No flattening (same as hierarchical mode)
- `depth=1`: Flatten one level (inline immediate children)
- `depth=∞`: Flatten everything (full netlist)

```lean
-- In codegen call
let sv := toSystemVerilogNetlist myCircuit (flattenDepth := 2)
```

**Pro:** Flexible. User picks the right level for their use case.
**Con:** More codegen complexity. Hierarchical names change with depth.

#### What about RAM?

This is the crux of the issue. Our current DSL has no RAM primitive. A 64x32
register file is 2048 DFFs + a 64:1 mux tree. Flattening it to gates is
technically correct but produces output that no synthesis tool would recognize
as a RAM.

Two paths:
1. **Add a RAM gate type to the DSL** (`GateType.RAM`). Proofs would treat it
   as an opaque axiom with read/write semantics.
2. **Keep DFFs, let the synth tool figure it out.** This works for small
   register files but fails for anything >16 entries.

**Decision: Full flatten + RAM primitive.**

Add RAM as a DSL primitive so the flattener stops there instead of
decomposing into thousands of DFFs + mux trees:

```lean
-- New circuit instance attribute
structure CircuitInstance where
  moduleName : String
  instName   : String
  portMap    : List (String × Wire)
  isPrimitive : Bool := false   -- NEW: don't inline in netlist mode

-- Or: a dedicated RAM type (more semantic)
structure RAMPrimitive where
  name     : String
  depth    : Nat                -- number of entries (e.g., 64)
  width    : Nat                -- bits per entry (e.g., 32)
  wrEn     : Wire
  wrAddr   : List Wire          -- log2(depth) wires
  wrData   : List Wire          -- width wires
  rdAddr   : List Wire          -- log2(depth) wires
  rdData   : List Wire          -- width wires (outputs)
  clock    : Wire

-- Circuit gains a ram field
structure Circuit where
  name       : String
  inputs     : List Wire
  outputs    : List Wire
  gates      : List Gate
  instances  : List CircuitInstance
  rams       : List RAMPrimitive := []  -- NEW
  ...
```

The RAM primitive is opaque to the proof core. Its semantics are axiomatized:

```lean
-- RAM behavioral spec (for proofs)
axiom ram_read_after_write (r : RAMPrimitive) (addr : Fin r.depth) (data : BitVec r.width) :
  (r.write addr data).read addr = data

axiom ram_read_no_write (r : RAMPrimitive) (addr1 addr2 : Fin r.depth) (data : BitVec r.width) :
  addr1 ≠ addr2 → (r.write addr1 data).read addr2 = r.read addr2
```

Code generators emit the RAM as:
- **SV netlist:** `reg [31:0] mem [0:63];` + read/write assigns (stays as one block)
- **SV hierarchical:** Same, or instantiate a RAM module
- **Chisel:** `val mem = Mem(64, UInt(32.W))` + `mem.read`/`mem.write`

This solves the PhysRegFile problem: instead of 2048 DFFs + 64:1 mux tree,
it's one `RAMPrimitive` that every codegen knows how to handle.

Netlist mode flattens everything EXCEPT RAM primitives and other
`isPrimitive` instances. For formal tools, the RAM is a known semantic
block they can reason about directly.

---

### Q3: Multi-bit Gate Reconstruction

The DSL is bit-level. Every gate operates on single wires. But readable output
needs buses: `assign data_next = enq_fire ? enq_bits : data_reg` instead of
32 separate MUX assignments.

#### What "reconstruction" means concretely

Current gate list for a 32-bit mux:

```lean
Gate.mkMUX (Wire.mk "data_reg_0")  (Wire.mk "enq_bits_0")  (Wire.mk "enq_fire") (Wire.mk "data_next_0"),
Gate.mkMUX (Wire.mk "data_reg_1")  (Wire.mk "enq_bits_1")  (Wire.mk "enq_fire") (Wire.mk "data_next_1"),
-- ... 30 more ...
Gate.mkMUX (Wire.mk "data_reg_31") (Wire.mk "enq_bits_31") (Wire.mk "enq_fire") (Wire.mk "data_next_31"),
```

The codegen needs to recognize this as one vectorized operation.

#### Option A: Pattern-match in codegen (reconstruct)

The codegen analyzes the gate list and groups operations:

```
Step 1: Group gates by (gateType, control signals)
  MUX gates sharing the same sel wire "enq_fire" → candidate bus operation

Step 2: Check if inputs/outputs form contiguous buses
  data_reg_0..31 → data_reg[31:0] ✓
  enq_bits_0..31 → enq_bits[31:0] ✓
  data_next_0..31 → data_next[31:0] ✓

Step 3: Emit vectorized
  assign data_next = enq_fire ? enq_bits : data_reg;
```

Algorithm sketch:

```lean
-- Group MUX gates by select wire
def groupMuxBySelect (gates : List Gate) : HashMap Wire (List Gate)

-- Check if a gate group forms a contiguous bus operation
def isContiguousBusOp (group : List Gate) : Option BusOp

-- BusOp: vectorized operation descriptor
structure BusOp where
  gateType : GateType
  inputs : List (String × Nat)  -- (basename, width) for each input bus
  output : String × Nat          -- (basename, width) for output bus
  control : Option Wire          -- select wire for MUX
```

**Pro:** No DSL changes. Proof core untouched. Works with existing circuits.
The reconstruction is purely cosmetic -- the bit-level semantics are preserved.
**Con:** Heuristic. Won't catch every pattern. Partial buses (e.g., bits 0-15
muxed by sel_a, bits 16-31 muxed by sel_b) won't merge.

#### What patterns actually appear in our circuits?

Looking at the real gate lists:

| Pattern | Frequency | Reconstructible? |
|---------|-----------|-------------------|
| N parallel MUX, same select | Very common (Queue, RS, PRF) | Yes -- straightforward |
| N parallel AND/OR/XOR, same structure | Common (ALU bitwise ops) | Yes |
| N parallel DFF, same clock/reset | Universal (every register) | Yes |
| Ripple-carry adder chain | Moderate (ALU, Comparator) | Harder -- carry chain |
| OR-tree (reduction) | Moderate (equality check) | Could emit `\|` reduction |
| Shift barrel mux tree | Rare (Shifter) | Unlikely to reconstruct |

The first three patterns cover ~80% of all gates. The ripple-carry and
reduction patterns are nice-to-have. The barrel shifter is probably not
worth reconstructing -- it would still be readable as individual MUXes.

#### Option B: Add multi-bit gate types to DSL

```lean
inductive GateType where
  | AND | OR | NOT | XOR | BUF | MUX | DFF
  -- New: vectorized operations
  | ANDN (width : Nat)  -- N-bit AND
  | ORN (width : Nat)   -- N-bit OR
  | MUXN (width : Nat)  -- N-bit MUX (shared select)
  | DFFN (width : Nat)  -- N-bit register
```

**Pro:** No heuristic reconstruction needed. Intent is explicit.
**Con:** Every circuit definition, every proof, every existing codegen path
needs to handle both scalar and vector gates. `native_decide` proofs may
need changes. The type theory becomes more complex.

#### Option C: Annotate at circuit level

Keep the bit-level gates but add annotations that explicitly declare buses:

```lean
structure Circuit where
  ...
  gates : List Gate
  instances : List CircuitInstance
  -- Codegen hints (don't affect proofs)
  busAnnotations : List BusAnnotation := []

structure BusAnnotation where
  basename : String
  width : Nat
  gateIndices : List Nat  -- which gates form this bus operation
```

**Pro:** Proofs untouched. Circuit builder can emit annotations alongside gates.
**Con:** Two sources of truth. Annotations can get out of sync with gates.

**Recommendation:** Option A (reconstruct in codegen). The patterns are
regular enough. The algorithm is:
1. Group gates by `(gateType, shared_control_wires)`
2. Sort each group by output wire index
3. Check if inputs/outputs form contiguous buses
4. Emit vectorized if yes, scalar if no

For the 20% of gates that don't reconstruct, scalar output is fine -- that's
already what the current codegen does.

---

### Q4: SV `struct packed` vs `interface` with `modport`

Both are SystemVerilog constructs for grouping signals. They serve different purposes.

#### `struct packed`

```systemverilog
typedef struct packed {
  logic        valid;
  logic [5:0]  tag;
  logic [31:0] data;
} cdb_entry_t;

module ReservationStation4(
  input  cdb_entry_t cdb [0:3],
  // ...
);
```

**Properties:**
- Fully synthesizable (IEEE 1800-2017)
- Can be used as port types, signal types, array elements
- Has a defined bit layout (packed = contiguous bits)
- Can be assigned, compared, passed through hierarchies

#### `interface` with `modport`

```systemverilog
interface decoupled_if #(parameter WIDTH = 32);
  logic [WIDTH-1:0] bits;
  logic             valid;
  logic             ready;

  modport source(output bits, output valid, input  ready);
  modport sink  (input  bits, input  valid, output ready);
endinterface

module Queue1_32(
  decoupled_if.sink  enq,
  decoupled_if.source deq,
  input logic clock,
  input logic reset
);
```

**Properties:**
- More powerful: modports encode direction, can contain tasks/functions
- Heavier syntax, more boilerplate
- Excellent for verification testbenches

#### Yosys + yosys-slang: Struct Support Status

Our LEC scripts currently use `read_verilog -sv` (Yosys built-in parser).
The struct situation has improved significantly:

**Yosys built-in parser (`read_verilog -sv`):**
- `typedef struct packed` on module ports: [fixed in PR #2312 (Feb 2021)](https://github.com/YosysHQ/yosys/issues/2348)
- Global typedef'd packed structs: [fixed in PR #5143](https://github.com/YosysHQ/yosys/issues/4653)
- Arrays of packed structs in struct members: [still open (#2677)](https://github.com/YosysHQ/yosys/issues/2677)
- SV `interface`/`modport`: not supported

So modern Yosys (>=0.10, ~2021) can handle basic struct ports. Nested
struct arrays are still broken in the built-in parser.

**[yosys-slang](https://github.com/povik/yosys-slang) (`read_slang`):**
- Uses the [slang](https://github.com/MikePopoloski/slang) library -- the
  most compliant open-source SV frontend
- Full SV 2017/2023 support including structs, packages, interfaces, etc.
- Proven at scale: ETH Zürich used it for a chip tapeout (Koopa, 2025)
- Parses Black Parrot, Ibex, OpenTitan successfully
- Active project: 566 commits, 16 contributors, Yosys 0.44-0.58 compat

**What switching to `read_slang` would unlock for us:**

| Feature | `read_verilog -sv` | `read_slang` |
|---------|-------------------|--------------|
| `typedef struct packed` on ports | Yes (post-2021) | Yes |
| Struct member access (`.field`) | Yes | Yes |
| Arrays of structs (`cdb[0].tag`) | Broken | Yes |
| Nested structs | Partial | Yes |
| SV packages (`import pkg::*`) | Partial | Yes |
| SV `interface`/`modport` | No | Yes |

The LEC migration would be small -- change `read_verilog -sv` to `read_slang`
in `run-lec.sh`. The equivalence checking commands (`equiv_make`, `equiv_induct`,
SAT) are Yosys-native and don't change.

#### Comparison for our use case

| Criterion | `struct packed` | `interface` |
|-----------|----------------|-------------|
| Yosys LEC (read_slang) | Full | Full |
| Yosys LEC (read_verilog) | Basic (no nested arrays) | No |
| Readability | Good | Better (direction in modport) |
| Synthesis (commercial) | Universal | Tool-dependent |
| Complexity | Simple | Significant |
| Port declarations | Flat with struct type | Interface type with modport |
| Cross-module connection | Assign struct to struct | Interface auto-connect |

#### What structs would look like for our modules

With `read_slang`, we can use structs on ports. Example for ReservationStation4:

```systemverilog
// shoumei_types.svh -- shared package
package shoumei_types;
  typedef struct packed {
    logic        ready;
    logic [5:0]  tag;
    logic [31:0] data;
  } operand_t;

  typedef struct packed {
    logic [5:0]  tag;
    logic [31:0] data;
  } cdb_entry_t;

  typedef struct packed {
    logic [5:0]  opcode;
    logic [5:0]  dest_tag;
    operand_t    src1;
    operand_t    src2;
  } rs_dispatch_t;
endpackage

// Module using struct ports
module ReservationStation4
  import shoumei_types::*;
(
  input  logic          clock,
  input  logic          reset,
  // dispatch (write)
  input  rs_dispatch_t  dispatch_data,
  input  logic          dispatch_valid,
  output logic          dispatch_ready,
  // issue (read)
  output rs_dispatch_t  issue_data,
  output logic          issue_valid,
  input  logic          issue_ready,
  // CDB broadcast
  input  cdb_entry_t    cdb      [0:3],
  input  logic [3:0]    cdb_valid,
  // flush
  input  logic          flush
);
  // Internal use: struct field access
  always_ff @(posedge clock) begin
    if (dispatch_valid && dispatch_ready) begin
      entries[free_slot].src1 <= dispatch_data.src1;
      entries[free_slot].src2 <= dispatch_data.src2;
    end
  end
endmodule
```

Compare that to the current output with 200+ flat `inputs_0` ports. Massive
readability improvement, and each field is self-documenting.

#### LEC consideration with struct ports

When Yosys reads struct-typed ports via `read_slang`, it flattens them
internally to individual bit signals for equivalence checking. The key
question is what names those flattened signals get, and whether they match
across the Lean SV and Chisel SV.

Yosys/slang typically flattens `input cdb_entry_t cdb [0:3]` to something
like `cdb[0].tag`, `cdb[0].data`, `cdb[1].tag`, etc. The LEC `equiv_make`
command matches ports by name, so both sides need to agree on this
flattening convention.

Two strategies:
1. **Both sides use structs** -- both Lean SV and Chisel SV use the same
   package/struct definitions. Yosys flattens identically. Clean.
2. **Only hierarchical SV uses structs, netlist stays flat** -- LEC compares
   netlist (flat) vs Chisel (structs flattened). Need to ensure name mapping.

Strategy 1 is cleaner. If both `read_slang` invocations see the same
`shoumei_types` package, the flattened names match by construction.

**Recommendation (revised):** Use `struct packed` with a shared SV package.
Switch LEC to `read_slang`. This gives us struct ports, nested structs,
arrays of structs -- everything we need. Skip `interface`/`modport` for now
(structs handle our use cases and are simpler). The migration cost is low:
one line change in `run-lec.sh` + adding yosys-slang as a dependency.

---

### Q5: Chisel `Decoupled` vs Custom `Bundle`

Chisel has a built-in `DecoupledIO` (via `Decoupled()` sugar) from `chisel3.util`.
We could use it directly or define our own bundles.

#### Chisel stdlib `Decoupled`

```scala
// What Chisel provides
class DecoupledIO[+T <: Data](gen: T) extends Bundle {
  val ready = Input(Bool())
  val valid = Output(Bool())
  val bits  = Output(gen)
}

// Usage:
val io = IO(new Bundle {
  val enq = Flipped(Decoupled(UInt(32.W)))  // sink: valid/bits are Input, ready is Output
  val deq = Decoupled(UInt(32.W))           // source: valid/bits are Output, ready is Input
})

// Connection:
io.enq.ready := !full
when(io.enq.fire) { ... }  // .fire = valid && ready
```

**Properties:**
- Industry-standard naming (`bits`, `valid`, `ready`)
- `Flipped()` handles direction reversal for sink ports
- `.fire` helper built in
- CIRCT lowers to standard port names: `enq_bits`, `enq_valid`, `enq_ready`
- This is the dominant pattern in the Chisel ecosystem

**Potential concern:** The CIRCT-generated SV port names must match our
Lean-generated SV port names for LEC. CIRCT lowers `Decoupled` to:
```
io_enq_bits      (with io_ prefix by default)
io_enq_valid
io_enq_ready
```

We'd need to either:
- Match this naming in Lean SV codegen (add `io_` prefix)
- Strip the prefix in Chisel (use `@public` or `IO` naming overrides)
- Use Yosys `rename` commands in LEC to normalize

#### Custom Bundle (no stdlib dependency)

```scala
class ShoumeiDecoupled(width: Int) extends Bundle {
  val bits  = UInt(width.W)
  val valid = Bool()
  val ready = Bool()
  // No Flipped -- direction set at IO declaration
}

val io = IO(new Bundle {
  val enq_bits  = Input(UInt(32.W))
  val enq_valid = Input(Bool())
  val enq_ready = Output(Bool())
  val deq_bits  = Output(UInt(32.W))
  val deq_valid = Output(Bool())
  val deq_ready = Input(Bool())
})
```

**Pro:** Full control over port naming. No `io_` prefix. Exact match with
Lean SV names. No CIRCT surprises.
**Con:** Lose `.fire`, `Flipped()`, and other Decoupled conveniences.
Less idiomatic -- anyone reading the Chisel output expects to see `Decoupled`.

#### What about our other interface shapes?

Beyond Decoupled, we have operand bundles, CDB entries, register ports, etc.
These don't exist in Chisel stdlib, so they'd be custom Bundles regardless:

```scala
class Operand extends Bundle {
  val ready = Bool()
  val tag   = UInt(6.W)
  val data  = UInt(32.W)
}

class CDBEntry extends Bundle {
  val tag  = UInt(6.W)
  val data = UInt(32.W)
}

class RegWritePort(addrWidth: Int, dataWidth: Int) extends Bundle {
  val en   = Bool()
  val addr = UInt(addrWidth.W)
  val data = UInt(dataWidth.W)
}

class RegReadPort(addrWidth: Int, dataWidth: Int) extends Bundle {
  val addr = Input(UInt(addrWidth.W))
  val data = Output(UInt(dataWidth.W))
}
```

These would be shared across modules in a `generated/Interfaces.scala` file.

#### LEC port name matching

This is the real constraint. The LEC flow compares Lean SV ports against
Chisel-generated SV ports by name. Currently both use flat `Bool()` ports
with matching names. With Bundles, CIRCT flattens them:

| Chisel Bundle | CIRCT-generated SV port name |
|---------------|------------------------------|
| `io.enq.bits` | `io_enq_bits` |
| `io.enq.valid` | `io_enq_valid` |
| `io.cdb(0).tag` | `io_cdb_0_tag` |
| `io.dispatch.src1.data` | `io_dispatch_src1_data` |

So Lean SV codegen needs to emit matching names:
```systemverilog
// Lean SV hierarchical mode -- must match CIRCT naming
module ReservationStation4(
  input  logic [5:0]  io_dispatch_src1_tag,
  input  logic [31:0] io_dispatch_src1_data,
  input  logic        io_dispatch_src1_ready,
  // ...
);
```

Or we strip the `io_` prefix on the Chisel side with:
```scala
override def desiredName = "ReservationStation4"
// and use experimental.prefix or @public to control naming
```

**Decision: `ShoumeiDecoupled` wrapper.** Same philosophy as `ShoumeiReg` --
own our types, control naming, enforce our protocol semantics.

```scala
/** Shoumei ready/valid interface.
  * Same shape as Chisel Decoupled but we control:
  * - Port naming (no io_ prefix, matches Lean SV exactly)
  * - Fire semantics (explicit Wire, not .fire method)
  * - Direction convention (explicit, not Flipped magic)
  */
class ShoumeiDecoupled(width: Int) extends Bundle {
  val bits  = UInt(width.W)
  val valid = Bool()
  val ready = Bool()
}

object ShoumeiDecoupled {
  /** Source (output) side: we drive bits+valid, observe ready */
  def source(width: Int): ShoumeiDecoupled = {
    val d = new ShoumeiDecoupled(width)
    // Direction set at IO() call site, not here
    d
  }

  /** Fire signal: explicit Wire, single-assign style */
  def fire(d: ShoumeiDecoupled): Bool = d.valid & d.ready
}
```

Usage in generated code:

```scala
class Queue1_32 extends Module {
  val io = IO(new Bundle {
    // Input side (sink): bits+valid are Input, ready is Output
    val enq_bits  = Input(UInt(32.W))
    val enq_valid = Input(Bool())
    val enq_ready = Output(Bool())
    // Output side (source): bits+valid are Output, ready is Input
    val deq_bits  = Output(UInt(32.W))
    val deq_valid = Output(Bool())
    val deq_ready = Input(Bool())
  })

  // Fire signals (explicit, single-assign)
  val enq_fire = Wire(Bool())
  val deq_fire = Wire(Bool())
  enq_fire := io.enq_valid & io.enq_ready
  deq_fire := io.deq_valid & io.deq_ready

  // ... rest of single-assign logic ...
}
```

**Why not stdlib Decoupled:**

| Issue | Chisel stdlib | ShoumeiDecoupled |
|-------|--------------|------------------|
| Port naming | `io_enq_bits` (CIRCT adds `io_` prefix) | `enq_bits` (exact match to Lean SV) |
| Direction | `Flipped(Decoupled(...))` magic | Explicit `Input`/`Output` per signal |
| Fire | `.fire` method (hides `&&`) | Explicit `Wire(Bool())`, single-assign |
| `when` temptation | `when(io.enq.fire) { ... }` | Not available -- forces Mux style |
| Bundle nesting | `io.enq.bits` (2-level) | `io.enq_bits` (flat) |
| LEC matching | Need `@public` or prefix stripping | Names match by construction |

The flat port style (`enq_bits`, `enq_valid`, `enq_ready` as separate
IO signals) is actually closer to what CIRCT ultimately generates anyway.
We just skip the Bundle→flatten round-trip. And it means the codegen
doesn't need to understand `Flipped` -- it just emits `Input`/`Output`
per signal based on the annotation direction.

For the other interface shapes (Operand, CDB, RegPort), same approach:
flat ports with consistent naming prefix, not nested Bundles.

---

### Q6 (New): Signal Group Detection Algorithm

Not originally listed but implied: how does the codegen decide which wires
form a bus?

#### Current approach (heuristic)

```lean
-- SystemVerilog.lean: splitWireName
-- "write_data_0" → ("write_data", 0)
-- "a3"           → ("a", 3) only if basename ≥ 3 chars
-- "e01"          → rejected (looks like a single signal)
```

This breaks on:
- `valid` (single bit, no index) -- correctly not split
- `src1_data_0` vs `src10_data` -- ambiguous split point
- `enq_bits_0` vs `enq_bits0` -- different heuristic paths

#### Proposed approach (type-driven)

If we have `SignalGroup` annotations (Option A from DSL changes):

```lean
def queue1_32_annotations : List SignalGroup := [
  { name := "enq_bits",  wires := makeIndexedWires "enq_bits" 32, width := 32 },
  { name := "data_reg",  wires := makeIndexedWires "data_reg" 32, width := 32 },
  { name := "data_next", wires := makeIndexedWires "data_next" 32, width := 32 },
]
```

The codegen doesn't guess -- it uses the annotations directly.

For wires NOT covered by annotations, fall back to the heuristic.
This gives a clean migration path: annotate the important buses,
let the heuristic handle the rest.

**Detection algorithm with annotations:**
```
1. For each wire in the circuit:
   a. Check if it belongs to a SignalGroup → use group's basename and index
   b. Else, apply splitWireName heuristic → best-effort grouping
   c. Else, treat as standalone scalar signal

2. For each SignalGroup, verify:
   - All wires exist in circuit.inputs/outputs/gates
   - Indices are contiguous (0..width-1)
   - No wire belongs to multiple groups
```

---

### Q7 (New): What Does the >200 Port Hack Actually Need to Become?

The current `inputs_0`/`outputs_0` hack exists because individual `Bool()`
port declarations blow up Chisel compilation and SV port lists. With buses,
this problem goes away entirely.

#### Current triggering modules

| Module | Input wires | Output wires | Total | Currently bundled? |
|--------|-------------|--------------|-------|--------------------|
| StoreBuffer8 | 108 | 73 | 181 | Yes (hardcoded map) |
| ReservationStation4 | ~140 | ~69 | ~209 | Yes (generic) |
| PhysRegFile_64x32 | ~2100 | ~64 | ~2164 | Yes (generic) |
| RAT_32x6 | ~200 | ~12 | ~212 | Yes (generic) |
| Queue64_32 | ~34 | ~32 | ~66 | No |
| Mux64x32 | ~2080 | ~32 | ~2112 | Yes (internal) |

#### Why the hack exists

In Chisel, each `val x = IO(Input(Bool()))` declaration:
- Creates a JVM object
- Adds to the module's port list
- Generates a line in the FIRRTL output

2000+ individual Bool declarations cause:
- JVM method size limits (>64KB bytecode per method)
- CIRCT compilation slowdowns
- Unreadable port lists

#### How buses eliminate the problem

With `UInt(32.W)` instead of 32x `Bool()`:

| Module | Chisel ports (current) | Chisel ports (with buses) |
|--------|----------------------|--------------------------|
| PhysRegFile_64x32 | 2164 x Bool() | ~10 ports (2 read ports, 1 write port, clk, rst) |
| Mux64x32 | 2112 x Bool() | 66 ports (64 x UInt(32) inputs, 1 x UInt(6) sel, 1 x UInt(32) out) |
| RAT_32x6 | 212 x Bool() | ~8 ports (2 read ports, 1 write port, clk, rst) |
| StoreBuffer8 | 181 x Bool() | ~15 ports (decoupled in/out, lookup, commit) |

The bundled IO hack, the hardcoded StoreBuffer8 mapping, the
`moduleUsesBundledIO` list, `mapPortNameToSVBundle` -- all of it goes away.
Replaced by proper typing at the DSL level.

This is arguably the single biggest win from the codegen v2 work.

---

## Implementation Plan

Chisel hierarchical first. No external tool dependencies, fast feedback
(`sbt run` fails immediately on bad output), and it forces us to get the
DSL annotations right before touching the SV generators.

### Phase 0: DSL Annotations (foundation for everything)

**Goal:** Add type info to `Circuit` without breaking any existing proofs.

**Files to change:**
- `lean/Shoumei/DSL.lean` -- add `SignalGroup`, `InterfaceBundle`, optional fields on `Circuit`
- `lean/Shoumei/DSL/Interfaces.lean` -- **new** shared interface library

```lean
-- DSL.lean additions
inductive SignalType where
  | Bool
  | UInt (width : Nat)
  | SInt (width : Nat)

structure SignalGroup where
  name  : String
  width : Nat
  wires : List Wire          -- the underlying flat wires
  stype : SignalType := .UInt width

structure InterfaceBundle where
  name     : String
  signals  : List (String × SignalType)  -- field name → type
  protocol : Option String := none       -- "decoupled" | "regport" | none

-- Circuit gets optional annotations (all default to [])
structure Circuit where
  name       : String
  inputs     : List Wire
  outputs    : List Wire
  gates      : List Gate
  instances  : List CircuitInstance
  -- v2: codegen annotations (ignored by proofs)
  signalGroups : List SignalGroup       := []
  inputBundles : List InterfaceBundle   := []
  outputBundles : List InterfaceBundle  := []
  rams : List RAMPrimitive             := []

-- RAM primitive (opaque to proofs, known to codegen)
structure RAMPrimitive where
  name    : String
  depth   : Nat            -- number of entries
  width   : Nat            -- bits per entry
  wrEn    : Wire
  wrAddr  : List Wire      -- log2(depth) wires
  wrData  : List Wire      -- width wires
  rdAddr  : List Wire      -- log2(depth) wires
  rdData  : List Wire      -- width wires (outputs)
  clock   : Wire
```

ShoumeiReg + ShoumeiMem Chisel helpers (emitted once in `ShoumeiPrimitives.scala`):

```scala
package generated

import chisel3._

object ShoumeiReg {
  /** DFF with async reset to zero. Returns plain UInt. */
  def apply(width: Int, clock: Clock, reset: AsyncReset): UInt =
    withClockAndReset(clock, reset) { RegInit(0.U(width.W)) }

  def bool(clock: Clock, reset: AsyncReset): Bool =
    withClockAndReset(clock, reset) { RegInit(false.B) }
}

object ShoumeiMem {
  /** RAM primitive. Wraps Chisel Mem with consistent interface. */
  def apply(depth: Int, width: Int): SyncReadMem[UInt] =
    SyncReadMem(depth, UInt(width.W))
}
```

```lean
-- DSL/Interfaces.lean - canonical interface types
def decoupledBundle (width : Nat) : InterfaceBundle := {
  name := "decoupled"
  signals := [("bits", .UInt width), ("valid", .Bool), ("ready", .Bool)]
  protocol := some "decoupled"
}

def operandBundle : InterfaceBundle := {
  name := "operand"
  signals := [("ready", .Bool), ("tag", .UInt 6), ("data", .UInt 32)]
}

def cdbEntryBundle : InterfaceBundle := {
  name := "cdb_entry"
  signals := [("tag", .UInt 6), ("data", .UInt 32)]
}

def regWriteBundle (addrW dataW : Nat) : InterfaceBundle := {
  name := "reg_write"
  signals := [("en", .Bool), ("addr", .UInt addrW), ("data", .UInt dataW)]
}

def regReadBundle (addrW dataW : Nat) : InterfaceBundle := {
  name := "reg_read"
  signals := [("addr", .UInt addrW), ("data", .UInt dataW)]
}
```

**Validation:** `lake build` passes. All existing circuits compile
unchanged (default `[]` annotations). No proofs break.

**Deliverable:** DSL is ready. Nothing visible changes in output yet.

---

### Phase 1: Annotate Existing Circuits

**Goal:** Add annotations to circuit definitions so codegen can use them.
Start with a vertical slice -- one simple, one medium, one large module.

**Vertical slice (3 circuits):**

| Module | Why | Key annotations |
|--------|-----|-----------------|
| Queue1_32 | Simple, has Decoupled ports | 2 interface bundles (enq, deq), 2 signal groups (data_reg, data_next) |
| ALU32 | Medium combinational, lots of buses | ~10 signal groups (a, b, op, result, add_result, ...) |
| ReservationStation4 | Large, currently broken by >200 port hack | operand, CDB, dispatch bundles |

**Example annotation for Queue1_32:**

```lean
def mkQueue1_32_annotated : Circuit :=
  let base := mkQueue1StructuralComplete 32
  { base with
    inputBundles := [
      { name := "enq", signals := [("bits", .UInt 32), ("valid", .Bool)]
        protocol := some "decoupled" },
    ]
    outputBundles := [
      { name := "enq", signals := [("ready", .Bool)]   -- enq.ready is output
        protocol := some "decoupled" },
      { name := "deq", signals := [("bits", .UInt 32), ("valid", .Bool)]
        protocol := some "decoupled" },
    ]
    signalGroups := [
      { name := "data_reg",  width := 32, wires := makeIndexedWires "data_reg" 32 },
      { name := "data_next", width := 32, wires := makeIndexedWires "data_next" 32 },
    ]
  }
```

**Validation:** `lake build` passes. Annotations are plumbed through.
Write a small test that reads annotations back (`#eval`).

**Deliverable:** Three annotated circuits ready for codegen to consume.

---

### Phase 2: Chisel Hierarchical Codegen

**Goal:** New `toChiselV2` that produces proper Chisel with Bundles, UInt,
Decoupled. Runs alongside existing `toChisel` (no breaking changes).

**Files to change:**
- `lean/Shoumei/Codegen/ChiselV2.lean` -- **new** generator
- `lean/Shoumei/Codegen/Unified.lean` -- add `writeCircuitChiselV2`
- `chisel/src/main/scala/generated/Interfaces.scala` -- **new** shared Bundles

**Step 2a: Chisel Bundle generation**

From `InterfaceBundle` definitions, emit `Interfaces.scala`:

```scala
package generated

import chisel3._
import chisel3.util._

class Operand extends Bundle {
  val ready = Bool()
  val tag   = UInt(6.W)
  val data  = UInt(32.W)
}

class CDBEntry extends Bundle {
  val tag  = UInt(6.W)
  val data = UInt(32.W)
}

class RegWritePort(addrWidth: Int, dataWidth: Int) extends Bundle {
  val en   = Bool()
  val addr = UInt(addrWidth.W)
  val data = UInt(dataWidth.W)
}

class RegReadPort(addrWidth: Int, dataWidth: Int) extends Bundle {
  val addr = UInt(addrWidth.W)
  val data = UInt(dataWidth.W)
}
```

**Step 2b: Module IO generation**

For a circuit with annotations, emit typed IO instead of flat Bool ports:

```lean
-- Old codegen (current):
--   val enq_data_0 = IO(Input(Bool()))
--   val enq_data_1 = IO(Input(Bool()))
--   ...

-- New codegen:
--   val io = IO(new Bundle {
--     val enq = Flipped(Decoupled(UInt(32.W)))
--     val deq = Decoupled(UInt(32.W))
--   })
```

Logic to emit:
1. Check `inputBundles`/`outputBundles` for protocol
2. If "decoupled" → emit `Decoupled(UInt(W.W))` or `Flipped(Decoupled(...))`
3. If named bundle matches a known interface → emit that Bundle class
4. Remaining flat wires → emit as `UInt(W.W)` or `Bool()` individually

**Step 2c: Internal signal generation**

Replace `_wires(N)` array with named signals:

```lean
-- Old: val _wires = Wire(Vec(500, Bool()))
--      _wires(42) := _wires(10) & _wires(11)

-- New: val enq_fire = Wire(Bool())
--      val data_next = Wire(UInt(32.W))
--      enq_fire := io.enq.valid && io.enq.ready
--      data_next := Mux(enq_fire, io.enq.bits, data_reg)
```

For annotated signal groups → emit as `UInt(W.W)` with vectorized ops.
For unannotated wires → keep as individual `Bool()` (safe fallback).

**Step 2d: Bus reconstruction for gate emission**

Implement the pattern-matching algorithm from Q3:
1. Group MUX/AND/OR/DFF gates by shared control wire
2. Check if inputs/outputs belong to the same SignalGroup
3. If yes → emit one vectorized operation
4. If no → emit individual scalar ops (existing behavior)

**Step 2e: Register generation + single-assign style**

**Style rule: no `when` blocks.** Every signal has exactly one `:=`.
Next-state logic is pure `Mux` chains. This maps 1:1 to the DSL (each wire
has one gate driving it) and makes the codegen straightforward -- no need
to reconstruct priority-encoded `when/elsewhen/otherwise` from flat gates.

```scala
// BAD -- when block, multiple assigns to same reg, implicit priority
when(reset.asBool) {
  data_reg := 0.U
}.elsewhen(enq_fire) {
  data_reg := io.enq.bits
}

// GOOD -- single assign, explicit Mux, one driver per signal
val data_next = Mux(enq_fire, io.enq.bits, data_reg)
data_reg := Mux(reset.asBool, 0.U, data_next)

// BEST -- separate next-state from register, matches DSL exactly
//   MUX gates → data_next (combinational)
//   DFF gate  → data_reg  (sequential, single assign)
val data_next = Wire(UInt(32.W))
data_next := Mux(enq_fire, io.enq.bits, data_reg)
data_reg  := data_next   // DFF: just captures, reset handled below
```

**Register type: custom wrapper vs bare `RegInit`**

Three options:

*Option A: Bare `RegInit` (simplest)*
```scala
val data_reg = withClockAndReset(clock, reset.asAsyncReset) {
  RegInit(0.U(32.W))
}
data_reg := data_next
```
Pro: minimal code, CIRCT optimizes freely.
Con: async reset is implicit in `withClockAndReset` scope -- easy to
get wrong. Reset semantics are baked into RegInit, not separated.

*Option B: `ShoumeiReg` helper (thin wrapper, no hierarchy)*
```scala
object ShoumeiReg {
  def apply(width: Int, clock: Clock, reset: AsyncReset): UInt = {
    withClockAndReset(clock, reset) { RegInit(0.U(width.W)) }
  }
}

val data_reg = ShoumeiReg(32, clock, reset)
data_reg := data_next
```
Pro: enforces async reset + reset-to-zero convention in one place.
No extra hierarchy for CIRCT. Name is a codegen marker ("I know this
came from a DFF in the DSL"). Still a plain `UInt` for downstream ops.
Con: minor boilerplate for the helper definition.

*Option C: Instantiate verified Register modules (full hierarchy)*
```scala
val u_data_reg = Module(new Register32)
u_data_reg.io.d := data_next
val data_reg = u_data_reg.io.q
```
Pro: structural match to Lean SV -- both outputs contain `Register32`
instances. LEC is trivial (same module name, same ports). Compositional
verification works directly.
Con: CIRCT can't optimize across module boundaries as well. Every
32-bit reg is a module instance -- verbose, and CIRCT may not inline
them. Requires all RegisterN variants to exist as Chisel modules too.

**Recommendation:** Option B. The helper enforces our DFF contract (async
reset, reset-to-zero, explicit clock) without adding hierarchy that blocks
CIRCT optimization. The single-assign style means each register has exactly
one `:= data_next` line. The `ShoumeiReg` name makes it searchable and
self-documenting.

If LEC has structural matching issues, we can fall back to Option C for
specific modules, but Option B should be the default.

**Bus grouping for registers:**

DFF groups sharing the same clock/reset with contiguous output wires
in a SignalGroup → one `ShoumeiReg(width)` call instead of N individual ones.

```scala
// 32 individual DFFs in DSL → one typed register in Chisel
val data_reg = ShoumeiReg(32, clock, reset)     // UInt(32.W)
val valid_reg = ShoumeiReg(1, clock, reset)      // UInt(1.W), or:
val valid_reg = ShoumeiReg.bool(clock, reset)    // Bool() variant
```

**Step 2f: Delete the hacks**

- Remove `moduleUsesBundledIO` hardcoded list
- Remove `mapPortNameToVecRef` and StoreBuffer8 special-case mapping
- Remove `useWireArray`/`useIOBundle`/`useRegArray` threshold logic
- Remove method chunking (typed signals = smaller methods naturally)

**Validation at each step:**
- `lake build` passes (Lean compiles)
- `lake exe generate_all` produces new Chisel files in a v2 output dir
- `cd chisel && sbt compile` passes (Chisel code is syntactically valid)
- `cd chisel && sbt run` passes (CIRCT generates SV)
- Manually inspect output for Queue1_32, ALU32, RS4

**Deliverable:** Chisel output that looks like a human wrote it. Three
annotated modules generate correct, readable Chisel. All other modules
continue using the v1 codegen path unchanged.

---

### Phase 3: Annotate Remaining Circuits

**Goal:** Once the vertical slice works, annotate all 63 modules.

Rough grouping by effort:

| Group | Modules | Effort | Notes |
|-------|---------|--------|-------|
| Simple combinational | FullAdder, RCA, Subtractor, Comparator, LogicUnit, Decoder | Low | Just signal groups for buses (a, b, result) |
| Medium combinational | ALU32, Shifter, MuxTree, Arbiter, Multiplier | Low-Med | Multiple bus groups, some shared patterns |
| Simple sequential | DFF, Register*, QueuePointer, QueueCounter | Low | data_reg groups, clock/reset already detected |
| Queue variants | Queue1_8, Queue1_32, QueueN_*, QueueRAM_* | Med | Decoupled bundles, storage arrays |
| RISC-V rename | RAT, FreeList, PhysRegFile | Med | RegRead/RegWrite bundles, eliminate bundled IO |
| Execution | IntExec, MemExec, RS4, MulDiv* | High | Operand, CDB, dispatch bundles, most complex |
| Top-level | ROB, StoreBuffer, LSU, Fetch, Rename, CPU | High | Composed of many sub-interfaces |

**Strategy:** Bottom-up. Annotate leaf modules first (they're simpler and
their annotations inform the parent modules' port mappings).

Order:
1. All Phase 1 combinational modules (bulk, mostly mechanical)
2. Register/Queue building blocks
3. Mux/Decoder (internal to RISC-V modules)
4. RAT, FreeList, PhysRegFile (rename stage)
5. ReservationStation, execution units
6. ROB, StoreBuffer, LSU
7. CPU top-level

**Validation:** After each group, `sbt run` passes for all modules.

---

### Phase 4: SV Hierarchical Codegen

**Goal:** New `toSystemVerilogV2` producing readable SV with buses and
struct types. Requires yosys-slang for LEC.

**Files to change:**
- `lean/Shoumei/Codegen/SystemVerilogV2.lean` -- **new** generator
- `lean/Shoumei/Codegen/Unified.lean` -- add `writeCircuitSVV2`
- `output/sv-from-lean/shoumei_types.sv` -- **new** shared package

**Step 4a: SV Package generation**

From the same `InterfaceBundle` definitions used for Chisel:

```systemverilog
package shoumei_types;
  typedef struct packed { ... } operand_t;
  typedef struct packed { ... } cdb_entry_t;
  // etc.
endpackage
```

**Step 4b: Module generation**

Same annotation-driven logic as Chisel, but emitting SV syntax:
- Typed ports: `input logic [31:0] enq_bits` instead of 32 individual ports
- Struct ports: `input cdb_entry_t cdb [0:3]` (with yosys-slang)
- Vectorized assigns: `assign data_next = enq_fire ? enq_bits : data_reg`
- Single `always_ff` blocks for register groups

**Step 4c: Instance generation**

Submodule instantiation with named ports:
```systemverilog
Register32 u_data_reg(
  .d   (data_next),
  .q   (data_reg),
  .clock(clock),
  .reset(reset)
);
```

**Validation:**
- `yosys -m slang.so` reads generated SV without errors
- LEC passes between SV hierarchical and Chisel SV (via CIRCT)

---

### Phase 5: yosys-slang Integration + LEC Update

**Goal:** Switch LEC from `read_verilog -sv` to `read_slang`.

**Files to change:**
- `verification/run-lec.sh` -- replace `read_verilog -sv` with `read_slang`
- `Makefile` or CI -- add yosys-slang install step

**Migration:**
1. Install yosys-slang plugin
2. Change 6 lines in `run-lec.sh` (`read_verilog -sv` → `read_slang`)
3. Run full LEC suite -- all 63 modules should pass
4. If any fail, debug port name mismatches (struct flattening convention)

**Validation:** `./verification/run-lec.sh` passes for all modules.

---

### Phase 6: SV Netlist Codegen

**Goal:** Flat netlist output for formal tools. Everything is primitives.

**Files to change:**
- `lean/Shoumei/Codegen/SystemVerilogNetlist.lean` -- **new** generator
- `lean/Shoumei/Codegen/Unified.lean` -- add `writeCircuitNetlist`

**Key logic:**
1. Recursive inline: walk `instances`, replace each with flattened gates
   using `Circuit.inline` with wire remapping
2. Hierarchical naming: prepend `{instName}__` to all remapped wires
3. Bus reconstruction: same algorithm as Phase 2 step 2d
4. Emit single flat module with:
   - Typed ports (from annotations)
   - Hierarchical internal wire names (`u_mem__reg_0_to_63__dff_0`)
   - Vectorized assigns where possible
   - One `always_ff` per register group

**Validation:** Yosys reads it, `equiv_make` + SAT proves it equivalent
to the hierarchical SV (both flattened internally by Yosys).

---

### Phase 7: Cleanup

- Remove v1 codegen (`Chisel.lean`, `SystemVerilog.lean`) once v2 is stable
- Remove `ChiselContext` with `useWireArray`/`useIOBundle`/`useRegArray`
- Remove all hardcoded module name lists
- Update `CLAUDE.md`, `docs/adding-a-module.md`
- Run full verification suite one last time

---

### Dependency Graph

```
Phase 0 (DSL annotations)
  │
  ├──→ Phase 1 (annotate 3 circuits)
  │       │
  │       └──→ Phase 2 (Chisel hierarchical codegen)
  │               │
  │               └──→ Phase 3 (annotate all 63 circuits)
  │                       │
  │                       ├──→ Phase 4 (SV hierarchical codegen)
  │                       │       │
  │                       │       └──→ Phase 5 (yosys-slang + LEC)
  │                       │
  │                       └──→ Phase 6 (SV netlist codegen)
  │
  └──────────────────────────→ Phase 7 (cleanup, after 5+6 done)
```

Phases 4 and 6 can run in parallel once Phase 3 is done.
Phase 5 depends on Phase 4 (need SV hierarchical output to LEC against).
Phase 7 waits for everything.

---

### Risk Checklist

| Risk | Mitigation |
|------|------------|
| Annotations get out of sync with wire lists | Validation function: check every annotated wire exists in circuit |
| Bus reconstruction misgroups wires | Conservative: only merge when ALL wires in a SignalGroup participate. Fall back to scalar. |
| CIRCT port naming doesn't match Lean SV naming | Test one module end-to-end in Phase 2 before annotating everything |
| yosys-slang struct flattening convention differs between Lean SV and Chisel SV | Both import same `shoumei_types` package → flattened identically |
| `native_decide` proofs break with new Circuit fields | Default values (`[]`) ensure backward compat. Proofs only see gates/inputs/outputs. |
| sbt compile hits JVM limits with new codegen | Typed signals are inherently smaller than Bool() arrays. If still big, keep chunking as fallback. |

---

## Remaining Open Questions

### Q8: Multi-port RAM

The `RAMPrimitive` as drafted has 1 write port + 1 read port. But
PhysRegFile has **1 write + 2 reads**, and future structures (ROB, store
buffer) may need 2W+2R or more.

Current PhysRegFile implementation (`PhysRegFile.lean:106-134`):
- 64 x 32-bit storage: 2048 DFFs + 64 x 32 write-data MUXes
- Read port 1: instantiates `Mux64x32` (2080 inputs → 32 outputs)
- Read port 2: instantiates another `Mux64x32`

Options:

**A. Multi-port RAMPrimitive (configurable)**
```lean
structure RAMPrimitive where
  name      : String
  depth     : Nat
  width     : Nat
  writePorts : List RAMWritePort   -- each has (en, addr, data)
  readPorts  : List RAMReadPort    -- each has (addr, data_out)
  clock     : Wire
```

Pro: one primitive handles all cases. PhysRegFile becomes one RAM with
1W+2R. Con: more complex type, code generators need to handle
arbitrary port counts.

**B. Separate read-only / write-only ports, compose**
```lean
-- One RAM for storage (1W+1R), plus extra read mux instances
-- Read port 2 is a separate Mux64x32 instance reading the same storage
```

Pro: simpler RAM type. Con: doesn't model multi-port correctly -- the
mux reads are logically part of the register file, not separate.

**C. One primitive per port configuration**

Define `RAM_1W1R`, `RAM_1W2R`, etc. as named variants.

Pro: each is a known shape. Con: combinatorial explosion if we need
`2W2R`, `1W3R`, etc.

**Decision: Option A.** Port lists handle any configuration. The common
cases are 1W1R (queues, store buffer) and 1W2R (register files). Code
generators emit:
- SV: `reg [31:0] mem [0:63];` with separate `always_ff` per write port
  and `assign rd_data = mem[rd_addr]` per read port
- Chisel: `val mem = Mem(...)` or `SyncReadMem(...)` with multiple
  `.read()` / `.write()` calls

**Decided.** ✓

---

### Q9: Mem vs SyncReadMem (async vs sync read)

The `ShoumeiMem` helper uses `SyncReadMem` (read requires a clock edge).
But our PhysRegFile reads are **combinational** -- output changes
immediately when the read address changes. That's `Mem`, not `SyncReadMem`.

| Chisel type | Read behavior | Maps to |
|-------------|---------------|---------|
| `Mem` | Async (combinational read) | Register file, small LUTs |
| `SyncReadMem` | Sync (read output registered) | SRAM, block RAM |

Our current circuits:
- **PhysRegFile**: async read (Mux64x32 is combinational). Use `Mem`.
- **QueueRAM**: could be either. Currently uses DFF + Mux = async. Use `Mem`.
- **Future SRAM**: would need `SyncReadMem` for actual memory blocks.

```scala
object ShoumeiMem {
  /** Async-read memory (register file, small arrays). */
  def apply(depth: Int, width: Int): Mem[UInt] =
    Mem(depth, UInt(width.W))

  /** Sync-read memory (SRAM, block RAM). */
  def syncRead(depth: Int, width: Int): SyncReadMem[UInt] =
    SyncReadMem(depth, UInt(width.W))
}
```

The `RAMPrimitive` in the DSL carries a `syncRead : Bool` flag to
distinguish the two.

**Decided.** ✓ Flag on primitive: `syncRead := false` → `Mem`, `syncRead := true` → `SyncReadMem`.

---

### Q10: LEC Pairing -- What Gets Compared to What?

Current: Lean SV ↔ Chisel SV (one pair, `read_verilog -sv` both sides).

With three output modes, what do we actually LEC?

| Gold | Candidate | Method | Purpose |
|------|-----------|--------|---------|
| SV netlist (flat) | SV hierarchical | Yosys `flatten` both → SAT | Validate SV hier codegen |
| SV hierarchical | Chisel SV (via CIRCT) | `equiv_make` → `equiv_induct` | Validate Chisel codegen |
| SV netlist | Chisel SV | `flatten` + SAT | End-to-end sanity check |

That's 3 LEC runs per module instead of 1. Or we could pick one canonical
pair and trust transitivity:
- If netlist == hierarchical (LEC 1) and hierarchical == Chisel (LEC 2),
  then netlist == Chisel (by transitivity).
- Only need 2 runs, not 3.

But the netlist is generated from a different code path (flattened inline)
vs hierarchical (instances preserved). LEC 1 validates the flattener.
LEC 2 validates the Chisel codegen. Together they cover everything.

**Decision:** LEC 1 + LEC 2 (two pairs, transitive). Drop the direct
netlist-vs-Chisel check.

**Decided.** ✓

---

### Q11: SV Struct Ports vs Chisel Flat Ports -- LEC Name Mismatch

The plan has SV hierarchical using struct ports (`input cdb_entry_t cdb[0:3]`)
but Chisel using flat ports (`val cdb_0_tag = Input(UInt(6.W))`).

When yosys-slang reads the struct side, it flattens to something like
`cdb[0].tag`. When CIRCT compiles the flat Chisel side, it emits `cdb_0_tag`.
These names don't match → `equiv_make` can't pair ports.

Options:

**A. Both sides flat ports**

SV hierarchical also uses flat ports (like we showed in the sketches):
`input logic [5:0] cdb_0_tag`. Structs only used internally for readability.
LEC sees identical port names on both sides.

**B. Both sides struct ports**

Chisel uses nested Bundles, CIRCT flattens to struct-matching names.
But we decided against nested Bundles (ShoumeiDecoupled = flat ports).

**C. Rename in LEC**

Yosys `rename` commands to normalize port names before `equiv_make`.
Fragile, but possible.

**Decision: Option A.** Both SV modes use the same flat port names as
Chisel. Structs are internal only. This is consistent with the
ShoumeiDecoupled decision (flat ports, matching names by construction).

The SV hierarchical sketches already show flat ports + struct internals,
so this is already where the draft landed for Q4. Struct-typed ports are
NOT used for top-level module ports -- only for internal signal grouping
and sub-module connections where both sides use the same `shoumei_types`
package.

**Decided.** ✓

---

### Q12: Module vs RawModule (Chisel)

Current codegen uses:
- `RawModule` for combinational circuits (no implicit clock/reset)
- `Module` for sequential circuits (with implicit clock/reset)

The `ShoumeiReg` helper takes explicit `clock` and `reset` arguments.
In a `Module`, these are available as `this.clock` and `this.reset`.
In a `RawModule`, they're explicit IO ports.

V2 should maintain this distinction:
```scala
// Combinational: no clock, no reset, no registers
class ALU32 extends RawModule {
  val io = IO(new Bundle { ... })
  // pure assign logic
}

// Sequential: clock + reset from Module
class Queue1_32 extends Module {
  val io = IO(new Bundle { ... })
  val data_reg = ShoumeiReg(32, clock, reset)  // implicit clock/reset
}
```

The codegen decision is simple: if `circuit.rams.length > 0` or
`circuit.gates.any DFF` or `circuit.instances` reference sequential
children → `Module`. Otherwise → `RawModule`.

Not a real open question, just flagging it -- the plan's Phase 2 sketches
all show `Module` but the combinational modules need `RawModule`.

---

### Q13: BlackBox Escape Hatch

Current codegen uses `ExtModule` (BlackBox) for circuits >2000 gates
(`Chisel.lean:742`). This includes ALU32, Shifter32, Multiplier, and
the large Mux trees.

With the v2 codegen, these modules get proper typed ports and bus
reconstruction. But the gate count is still >2000. Does the JVM limit
still apply?

The JVM 64KB method limit triggers when too many statements appear in
one method body. With buses:
- ALU32: 11000+ gates → with reconstruction, maybe ~500 statements
  (vectorized ops). Probably fits.
- Mux64x32: 2080 gates → with reconstruction, ~65 statements
  (64 `val in_N = ...` + 1 mux). Fits easily.

**Likely resolved by bus reconstruction.** The BlackBox escape hatch
probably isn't needed for v2. But keep it as a fallback for any module
where reconstruction doesn't collapse enough.

---

### Q14: Axiom vs Proof for RAM Semantics

The RAM primitive uses `axiom` for read-after-write semantics. This is
trusted, not proved. In a project where the whole point is formal
verification, axioms are a liability.

Options:

**A. Axioms (pragmatic)**

Trust the RAM semantics. They're simple and universal (every RAM in
existence satisfies read-after-write). The risk of getting this wrong
is near zero.

**B. Model RAM as function, prove properties**

```lean
def RAM (depth width : Nat) := Fin depth → BitVec width

def RAM.write (mem : RAM d w) (addr : Fin d) (val : BitVec w) : RAM d w :=
  fun a => if a == addr then val else mem a

def RAM.read (mem : RAM d w) (addr : Fin d) : BitVec w := mem addr

-- Proven, not axiomatized
theorem ram_read_after_write ...  := by simp [RAM.write, RAM.read]
theorem ram_read_no_write ... := by simp [RAM.write, RAM.read]
```

**Pro:** No axioms. Fully proved. Consistent with project philosophy.
**Con:** The proofs need to connect this functional model to the
`RAMPrimitive` structural definition. Two levels of abstraction.

**Decision: Option B.** The proofs are trivial (`simp` handles them).
The connection to `RAMPrimitive` is: the codegen generates code that
implements this functional spec, and LEC verifies it.

**Decided.** ✓ No axioms. Fully proved functional RAM model.
