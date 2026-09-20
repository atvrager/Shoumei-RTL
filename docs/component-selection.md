# Component Selection and PDK Technology Mapping

Two layers that keep structure choices out of the use sites and keep the
emitted cells tied to a PDK:

```
  use site              requirement            selected circuit
  --------              -----------            ----------------
  ALU32 u_add   ->  AdderSpec.minDelay 32 .none  ->  KoggeStoneAdder32NoCin
  FPAdder s4_normexp -> AdderSpec.minArea 8 .one ->  SklanskyAdder8WithCin1

  proven Circuit  ->  TechMap (peephole)  ->  CellNetlist  ->  SV per PDK
```

## Requirement and selection (`lean/Shoumei/Components/`)

- `Spec.lean` — `DesignTarget` (PDK, clock period, aim) and `AdderSpec`
  (width, carry-in mode, aim, period, PDK, optional `pinned` structure).
- `Cost.lean` — analytic area/delay per `GateType`, seeded from the PDK
  Liberty typical tables; `estDelay` relaxes the gate list to a fixpoint.
- `Select.lean` — `legal` (width rules plus `validPrefixNetwork`), `selectAdder`
  (timing filter, then cheapest by aim, ties by `AdderImpl.precedence`),
  `adderModule` / `selectedAdderCircuit`, and the inline builders `mkAddFor` /
  `mkSubFor`.
- `AdderLibrary.lean` — `adderCircuit` for each structure; Kogge-Stone
  delegates to the long-standing `KoggeStoneAdder*.lean` definitions, so the
  emitted SV for every pre-existing module is byte-identical.

At the default target the selector resolves to Kogge-Stone on every
timing-critical site (`AdderLibraryProofs.default_target_picks_koggeStone`).
A site that needs a different structure pins it with `AdderSpec.pinned`.

Structures: `rippleCarry`, `carrySelect`, `brentKung`, `sklansky`,
`hanCarlson`, `koggeStone` (`Circuits/Combinational/PrefixAdder.lean`,
`CarrySelectAdder.lean`).  A tree is only selectable at a width where its
network forms a valid full-prefix network.

### Adder correctness

`Circuits/Combinational/PrefixAdderProofs.lean` proves the network algebra
(`prefixNetwork_correct`: a valid network's wires hold the full-prefix group
of each bit) and checks every selectable network (`prefixLevels_valid`), plus
exhaustive gate-level arithmetic at width 4 and 8.
`CarrySelectAdderProofs.lean` covers the carry-select structure.

## PDK technology mapping (`lean/Shoumei/Codegen/`)

- `CellLibrary.lean` — `CellFunction` with a single `model` shared by every
  PDK, `StandardCell` (function, pins, drive, area), `CellLibrary.find`.
- `CellLibs/{ASAP7,GF180}.lean` — cell tables read from the PDK Liberty
  typical tables.  ASAP7 has no mux cell and its `FAx1`/`HAxp5` drive inverted
  pins, so `.mux2`/`.fa`/`.ha` are absent there and the mapper falls back.
- `TechMap.lean` — peepholes the ordered gate list into complex cells
  (`ao21`, `ao22`, `fa`, `ha`, `mux2`), with `aoi21`+`inv` / `aoi22`+`inv`
  where the PDK lacks a non-inverting AND-OR cell.  A peephole only fires when
  every wire it removes is read nowhere else.
- `CellNetlist.lean` — the cell-level IR, its `eval` (the mapping's meaning),
  and the SystemVerilog emitter.
- `Unified.lean` — emits `output/sv-<pdk>/` for ASAP7 and GF180MCU.

### Verifying the mapping

| Tier | What | Where |
|---|---|---|
| 1 | peephole lemmas (cell function == gate pattern) | `Codegen/TechMapProofs.lean` |
| 1 | exhaustive end-to-end checks, both PDKs | `Codegen/TechMapProofs.lean` |
| 2 | Yosys miter LEC, every mapped module | `make techmap-equiv` |
| — | tables vs Liberty functions | `scripts/check-cell-tables.py` |

Tier 2 uses cell models translated from the Liberty `function` of each output
pin (`scripts/gen-pdk-cell-models.py`), so it also cross-checks the tables
against the PDK.  RAM-bearing modules are skipped there (Yosys cannot flatten
memory-bearing modules for SAT); their RAMs are copied verbatim by the emitter.

## Commands

```bash
make techmap-equiv            # Yosys LEC: mapped vs gate-level, both PDKs
make cell-models              # regenerate cell models + check tables vs Liberty
python3 verification/slang-lint.py output/sv-gf180
lake exe generate_adder_matrix && python3 scripts/calibrate-adders.py --refit
```

`scripts/calibrate-adders.py` measures real area and critical delay per adder
and PDK and reports the scale factors implied for `Cost.lean`'s seeds.  The
selector never reads the results; a factor outside 0.75-1.25 is the signal to
re-seed the analytic model.
