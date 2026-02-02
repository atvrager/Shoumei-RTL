# ReservationStation4 Architecture - Using Verified Primitives

## Problem with Current Stub

Current design manually instantiates 364 individual DFFs - this is error-prone and doesn't leverage our verified Register abstraction.

## Correct Approach: Compose Verified Building Blocks

### Available Primitives (All Verified)

1. **`mkRegisterN n`** - N-bit register (parallel DFFs with shared clock/reset)
2. **`mkComparatorN n`** - N-bit comparator (eq, lt, ltu, gt, gtu outputs)
3. **`mkMuxTree m n`** - m:1 mux, n bits wide
4. **`mkDecoder k`** - k→2^k decoder (one-hot)
5. **`mkPriorityArbiter n`** - N-input priority arbiter

### RS4 Storage: Use Register Instances

Instead of 364 individual DFFs, use **4 instances of `mkRegisterN 91`**:

```lean
-- Per entry: 91 bits
-- - valid: 1 bit
-- - opcode: 6 bits
-- - dest_tag: 6 bits
-- - src1_ready: 1 bit, src1_tag: 6 bits, src1_data: 32 bits
-- - src2_ready: 1 bit, src2_tag: 6 bits, src2_data: 32 bits
-- Total: 1 + 6 + 6 + (1+6+32) + (1+6+32) = 91 bits

-- Instances:
let entry0_reg := mkRegisterN 91  -- Entry 0 storage
let entry1_reg := mkRegisterN 91  -- Entry 1 storage
let entry2_reg := mkRegisterN 91  -- Entry 2 storage
let entry3_reg := mkRegisterN 91  -- Entry 3 storage

let alloc_ptr_reg := mkRegisterN 2  -- Allocation pointer (2 bits)
```

### CDB Tag Comparison: Use Comparator Instances

For CDB snooping, we need 6-bit tag equality checking:

```lean
-- Per entry: 2 comparators (one for each source)
-- Entry i, src1 tag comparison
let entry_i_src1_cmp : CircuitInstance := {
  moduleName := "Comparator6"
  instName := s!"u_entry{i}_src1_cmp"
  portMap := [
    ("a", cdb_tag[0..5]),      -- CDB broadcast tag
    ("b", entry_i_src1_tag),   -- Entry's src1 tag
    ("eq", entry_i_src1_match) -- Use only eq output
    -- Ignore lt, ltu, gt, gtu
  ]
}

-- Total: 4 entries × 2 sources = 8 Comparator6 instances
```

**Why Comparator instead of manual XOR chain?**
- Verified building block (proven correct)
- Generates optimized comparison logic
- Reuses existing LEC-validated module
- Only 9×6 = 54 gates per comparator

### Dispatch Muxing: Use MuxTree

4:1 selection for dispatch output (74 bits total):

```lean
-- Opcode mux (6 bits, 4:1)
let dispatch_opcode_mux : CircuitInstance := {
  moduleName := "Mux4x6"
  instName := "u_dispatch_opcode_mux"
  portMap := [
    ("in0_b0", entry0_opcode[0]), ... // Entry 0
    ("in1_b0", entry1_opcode[0]), ... // Entry 1
    ("in2_b0", entry2_opcode[0]), ... // Entry 2
    ("in3_b0", entry3_opcode[0]), ... // Entry 3
    ("sel0", dispatch_grant[0]),      // From arbiter
    ("sel1", dispatch_grant[1]),
    ("out0", dispatch_opcode[0]), ...
  ]
}

-- Similarly for src1_data (32 bits), src2_data (32 bits), dest_tag (6 bits)
let dispatch_src1_mux := mkMuxTree 4 32  // 4:1, 32 bits wide
let dispatch_src2_mux := mkMuxTree 4 32
let dispatch_tag_mux := mkMuxTree 4 6
```

### Issue Selection: Use Decoder + Mux

```lean
-- Decoder for allocation pointer (2→4 one-hot)
let issue_decoder : CircuitInstance := {
  moduleName := "Decoder2"
  instName := "u_issue_dec"
  portMap := [
    ("in0", alloc_ptr[0]),
    ("in1", alloc_ptr[1]),
    ("out0", issue_sel[0]),  // Select entry 0
    ("out1", issue_sel[1]),  // Select entry 1
    ("out2", issue_sel[2]),  // Select entry 2
    ("out3", issue_sel[3])   // Select entry 3
  ]
}

-- Write muxes: select between hold vs issue data
-- Per entry: 91-bit 2:1 mux (hold current value vs write new issue data)
```

### Ready Selection: Use PriorityArbiter4

```lean
-- Ready signal per entry: valid AND src1_ready AND src2_ready
let ready_gates := [
  Gate.mkAND entry0_valid entry0_src1_ready tmp0,
  Gate.mkAND tmp0 entry0_src2_ready ready[0],
  // ... repeat for entries 1, 2, 3
]

-- Arbiter selects first ready entry
let ready_arbiter : CircuitInstance := {
  moduleName := "PriorityArbiter4"
  instName := "u_ready_arbiter"
  portMap := [
    ("request0", ready[0]),
    ("request1", ready[1]),
    ("request2", ready[2]),
    ("request3", ready[3]),
    ("grant0", dispatch_grant[0]),
    ("grant1", dispatch_grant[1]),
    ("grant2", dispatch_grant[2]),
    ("grant3", dispatch_grant[3]),
    ("valid", dispatch_valid)
  ]
}
```

## Final Instance Breakdown

### CircuitInstances (12 total)
1. `Decoder2` - Issue allocation select (1)
2. `Register91` - Entry storage (4)
3. `Register2` - Allocation pointer (1)
4. `Comparator6` - CDB tag matching (8: 4 entries × 2 sources)
5. `PriorityArbiter4` - Ready selection (1)
6. `Mux4x6` - Dispatch opcode mux (1)
7. `Mux4x32` - Dispatch src1_data mux (1)
8. `Mux4x32` - Dispatch src2_data mux (1)
9. `Mux4x6` - Dispatch dest_tag mux (1)

**Wait, that's 19 instances!** Let me recalculate:
- Decoder2: 1
- Register91: 4 (entries)
- Register2: 1 (alloc_ptr)
- Comparator6: 8 (tag matching)
- PriorityArbiter4: 1
- Mux4x6: 2 (opcode + dest_tag)
- Mux4x32: 2 (src1_data + src2_data)

**Total: 19 instances**

### Gates (Additional Logic)
- **Wakeup logic**: ~200 gates (AND/OR for capture conditions)
- **Next-state muxing**: ~300 gates (select issue vs CDB wakeup vs hold)
- **Ready checking**: 12 AND gates
- **Issue_full logic**: 4:1 mux for valid bit selection
- **Allocation increment**: 5 gates (2-bit increment with wrap)

**Total: ~520 gates + 19 instances**

## Advantages of This Approach

1. **Verified components**: All instances are LEC-validated
2. **Maintainable**: Clear hierarchy, not 364 individual DFFs
3. **Debuggable**: Can inspect Register91 state, not scattered DFFs
4. **Reusable**: Same Comparator6 used in other modules
5. **Provable**: Can reason about Register behavior via RegisterLemmas
6. **Smaller**: ~520 gates vs ~1100 gates (leverages optimized primitives)

## Next Steps

Implement RS4 using this clean architecture:
1. Instantiate 4 × Register91 for entries
2. Instantiate 8 × Comparator6 for CDB tag matching
3. Wire up wakeup logic (combinational gates between comparators and registers)
4. Instantiate Mux4xN for dispatch output selection
5. Wire up next-state logic with priority: dispatch_clear > cdb_wakeup > issue > hold

This will be much cleaner and more maintainable than the manual DFF approach!
