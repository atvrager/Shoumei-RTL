"""Randomised co-simulation of one emitted module against its spec.

`spec_equiv_test` runs scripts/spec-equiv.py in a build action.  The script
writes a testbench and copies the spec and the netlist sources into one
directory.  rules_verilator compiles the directory with the Bazel C++
toolchain.  The test runs the model.  The testbench stops with $fatal when the
emitted RTL and the spec differ.
"""

load("@rules_cc//cc:defs.bzl", "cc_test")
load("@rules_verilator//verilator:defs.bzl", "verilator_cc_library")
load("//rules:verilog_tree.bzl", "verilog_tree_library")

def _spec_equiv_tb_impl(ctx):
    out = ctx.actions.declare_directory(ctx.label.name)
    sv = ctx.file.sv
    scripts = [f for f in ctx.files.srcs if f.short_path == "scripts/spec-equiv.py"]
    if len(scripts) != 1:
        fail("srcs must contain scripts/spec-equiv.py")
    args = ctx.actions.args()
    args.add(scripts[0])
    args.add(ctx.attr.module)
    args.add("--cycles", str(ctx.attr.cycles))
    args.add("--sv-dir", sv.path)
    args.add("--out", out.path)
    ctx.actions.run_shell(
        command = "python3 \"$@\"",
        arguments = [args],
        inputs = [sv] + ctx.files.srcs,
        outputs = [out],
        mnemonic = "SpecEquivTb",
        progress_message = "Writing the spec co-simulation of %s" % ctx.attr.module,
    )
    return [DefaultInfo(files = depset([out]))]

_spec_equiv_tb = rule(
    implementation = _spec_equiv_tb_impl,
    attrs = {
        "cycles": attr.int(mandatory = True),
        "module": attr.string(mandatory = True),
        "srcs": attr.label_list(
            allow_files = True,
            doc = "The script, its helper scripts, the specs, and the Lean registry.",
        ),
        "sv": attr.label(allow_single_file = True, mandatory = True),
    },
)

def spec_equiv_test(name, module, cycles, **kwargs):
    """One co-simulation test of `module` against its spec.

    Args:
      name: name of the test.
      module: emitted module name, for example "BusyTable_W2".
      cycles: number of clock cycles to simulate.
      **kwargs: passed to the cc_test.  The intermediate targets get the same
        `tags`, so a "manual" test does not build under //... either.
    """
    tags = kwargs.get("tags", [])
    _spec_equiv_tb(
        name = name + "_tb",
        module = module,
        cycles = cycles,
        sv = "//:sv",
        srcs = [
            "//:root_python_scripts",
            "//lean:shoumei_srcs",
            "//verification:specs",
        ],
        tags = tags,
    )
    verilog_tree_library(
        name = name + "_verilog",
        srcs = [name + "_tb"],
        top_module = "tb_" + module,
        tags = tags,
    )

    # -DSYNTHESIS drops the emitted SVA properties.  They sample as if reset
    # were synchronous, so they misfire under random stimulus.  -O0 is
    # sufficient: the simulation takes almost no time, the C++ build does.
    verilator_cc_library(
        name = name + "_model",
        module = name + "_verilog",
        timing = True,
        copts = ["-O0"],
        vopts = [
            "-DSYNTHESIS",
            "-Wno-fatal",
            "-Wno-WIDTHTRUNC",
            "-Wno-WIDTHEXPAND",
            "-Wno-UNUSEDSIGNAL",
            "-Wno-UNUSEDPARAM",
        ],
        tags = tags,
    )
    cc_test(
        name = name,
        srcs = ["//verification:spec_equiv_main.cpp"],
        copts = [
            "-DVM_PREFIX=Vtb_" + module,
            "-DVM_PREFIX_INCLUDE='\"Vtb_%s.h\"'" % module,
        ],
        deps = [name + "_model"],
        **kwargs
    )
