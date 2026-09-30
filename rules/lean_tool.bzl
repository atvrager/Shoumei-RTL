"""Expose the Lean compiler of the registered toolchain as a file.

A test that compiles Lean at run time needs the compiler the build uses.  The
toolchain owns it, so this rule hands the file to the test instead of a probe
of the host PATH.
"""

load("@rules_lean//lean:defs.bzl", "TOOLCHAIN_TYPE")

def _lean_tool_impl(ctx):
    toolchain = ctx.toolchains[TOOLCHAIN_TYPE].lean_toolchain
    return [DefaultInfo(files = depset([toolchain.lean]))]

lean_tool = rule(
    implementation = _lean_tool_impl,
    toolchains = [TOOLCHAIN_TYPE],
    doc = "The `lean` binary of the Lean toolchain.",
)
