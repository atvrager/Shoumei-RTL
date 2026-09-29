"""Bazel rules for SystemVerilog linting with slang (pyslang)."""

def _slang_lint_test_impl(ctx):
    sv = ctx.file.sv
    runner = ctx.actions.declare_file(ctx.attr.name + ".sh")

    flags = []
    if ctx.attr.sram:
        flags.append("--sram")
    if ctx.attr.lean_sv:
        flags.append("--lean-dir=\"${ROOT}/" + ctx.file.lean_sv.short_path + "\"")

    runfiles_files = [
        ctx.file.linter,
        sv,
    ]
    if ctx.attr.lean_sv:
        runfiles_files.append(ctx.file.lean_sv)
    if ctx.file.pdk_cells:
        runfiles_files.append(ctx.file.pdk_cells)

    script_content = """#!/usr/bin/env bash
set -euo pipefail

# Find user site-packages for pyslang in sandbox
if [ -z "${{PYTHONPATH:-}}" ]; then
    for p in /usr/local/google/home/*/.local/lib/python*/site-packages "$HOME/.local/lib/python*/site-packages"; do
        if [ -d "$p" ]; then
            export PYTHONPATH="${{PYTHONPATH:+$PYTHONPATH:}}$p"
        fi
    done
fi

ROOT="$(pwd)"
python3 "{linter}" "{sv_dir}" {flags}
""".format(
        linter = ctx.file.linter.short_path,
        sv_dir = sv.short_path,
        flags = " ".join(flags),
    )

    ctx.actions.write(
        output = runner,
        content = script_content,
        is_executable = True,
    )

    return [
        DefaultInfo(
            executable = runner,
            runfiles = ctx.runfiles(files = runfiles_files),
        ),
    ]

slang_lint_test = rule(
    implementation = _slang_lint_test_impl,
    test = True,
    attrs = {
        "sv": attr.label(
            allow_single_file = True,
            mandatory = True,
            doc = "The SystemVerilog directory target (e.g. //:sv).",
        ),
        "lean_sv": attr.label(
            allow_single_file = True,
            doc = "Optional base Lean SystemVerilog directory (e.g. //:sv) for SEC/mapped linting.",
        ),
        "sram": attr.bool(
            default = False,
            doc = "Whether to lint the SHOUMEI_SRAM_MACROS branch against generated macro stubs.",
        ),
        "linter": attr.label(
            default = Label("//verification:slang-lint.py"),
            allow_single_file = True,
            doc = "The slang-lint.py script.",
        ),
        "pdk_cells": attr.label(
            allow_single_file = True,
            doc = "Optional PDK cell model stub file.",
        ),
    },
)
