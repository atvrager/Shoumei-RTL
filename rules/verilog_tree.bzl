"""Helper rule to package TreeArtifacts into VerilogInfo."""

load("@rules_verilog//verilog:defs.bzl", "VerilogInfo")

def _verilog_tree_library_impl(ctx):
    all_srcs = []
    for target in ctx.attr.srcs:
        all_srcs.extend(target[DefaultInfo].files.to_list())

    return [
        VerilogInfo(
            srcs = depset(all_srcs),
            top_module = ctx.attr.top_module,
        ),
        DefaultInfo(files = depset(all_srcs)),
    ]

verilog_tree_library = rule(
    implementation = _verilog_tree_library_impl,
    attrs = {
        "srcs": attr.label_list(
            mandatory = True,
            doc = "Targets providing SV directories or files.",
        ),
        "top_module": attr.string(
            mandatory = True,
            doc = "Name of the top-level module.",
        ),
    },
)
