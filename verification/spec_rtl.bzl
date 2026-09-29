"""Rule for generating spec-backed SystemVerilog directory from emitted RTL and specs."""

def _shoumei_spec_rtl_impl(ctx):
    out_dir = ctx.actions.declare_directory(ctx.attr.name)
    sv_file = ctx.files.sv[0]
    dual_rtl_file = ctx.files.dual_rtl[0]
    specs_dir = ctx.files.specs[0].dirname

    script = ctx.actions.declare_file(ctx.label.name + "_gen.sh")
    content = """#!/usr/bin/env bash
set -euo pipefail

python3 "{generator}" \
    --sv-dir="{sv_dir}" \
    --spec-dir="{spec_dir}" \
    --dual-rtl="{dual_rtl}" \
    --out-dir="{out_dir}"
""".format(
        generator = ctx.file._generator.path,
        sv_dir = sv_file.path,
        spec_dir = specs_dir,
        dual_rtl = dual_rtl_file.path,
        out_dir = out_dir.path,
    )

    ctx.actions.write(
        output = script,
        content = content,
        is_executable = True,
    )

    inputs = [
        sv_file,
        dual_rtl_file,
        ctx.file._generator,
    ] + ctx.files.specs

    ctx.actions.run(
        executable = script,
        inputs = inputs,
        outputs = [out_dir],
        mnemonic = "SpecShimsGen",
        progress_message = "Generating Shoumei spec-backed RTL shims (%{label})",
    )

    return [
        DefaultInfo(
            files = depset([out_dir]),
            runfiles = ctx.runfiles(files = [out_dir]),
        ),
    ]

shoumei_spec_rtl = rule(
    implementation = _shoumei_spec_rtl_impl,
    attrs = {
        "sv": attr.label(
            allow_single_file = True,
            mandatory = True,
            doc = "The emitted SystemVerilog directory artifact.",
        ),
        "specs": attr.label_list(
            allow_files = True,
            mandatory = True,
            doc = "The human-authored SystemVerilog spec files in verification/specs/.",
        ),
        "dual_rtl": attr.label(
            allow_single_file = True,
            mandatory = True,
            doc = "The DualRTL.lean registry file.",
        ),
        "_generator": attr.label(
            default = "//:scripts/gen-spec-shims.py",
            allow_single_file = True,
        ),
    },
    doc = "Generates a complete spec-backed SystemVerilog tree containing shims for verified circuits.",
)
