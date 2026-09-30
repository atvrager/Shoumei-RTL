# Host tools

The Bazel build fetches every tool that it runs. `MODULE.bazel` pins Lean 4,
Yosys, Verilator, the RISC-V compiler, node, typescript, `pyslang`,
shellcheck, cppcheck, ruff and ty. A test receives a pinned tool through
`verification/tool_path.sh`.

These scripts run by hand and still read a tool from the host PATH. Each one
needs a Bazel target that passes the pinned tool.

|Script|Host tool|
|---|---|
|`physical/run-yosys-asap7.sh`|`yosys`|
|`physical/run-yosys-gf180.sh`|`yosys`|
|`physical/run-openroad.sh`|`docker`|
|`physical/export-artifacts.sh`|`uv`, `python3`|
|`scripts/gen-sram-macros.sh`|`openram`|

A script under `verification/` keeps a `command -v` guard. The test that calls
the script puts the pinned tool on PATH first, so the guard passes. A hand run
still needs the host tool.
