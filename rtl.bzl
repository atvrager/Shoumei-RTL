"""Rules for generating SystemVerilog and simulation models from Lean."""

def _shoumei_rtl_impl(ctx):
    sv_dir = ctx.actions.declare_directory(ctx.attr.name + "_sv")
    netlist_dir = ctx.actions.declare_directory(ctx.attr.name + "_netlist")
    asap7_dir = ctx.actions.declare_directory(ctx.attr.name + "_asap7")
    gf180_dir = ctx.actions.declare_directory(ctx.attr.name + "_gf180")
    sec_dir = ctx.actions.declare_directory(ctx.attr.name + "_sec")
    cpp_sim_dir = ctx.actions.declare_directory(ctx.attr.name + "_cpp_sim")
    testbench_dir = ctx.actions.declare_directory(ctx.attr.name + "_testbench")
    config_mk = ctx.actions.declare_file(ctx.attr.name + "_config.mk")
    cosim_main = ctx.actions.declare_file(ctx.attr.name + "_cosim_main_tb_cpu.cpp")
    sim_main = ctx.actions.declare_file(ctx.attr.name + "_sim_main_tb_cpu.cpp")
    tb_cpu_sv = ctx.actions.declare_file(ctx.attr.name + "_tb_cpu.sv")

    script = ctx.actions.declare_file(ctx.attr.name + "_run.sh")
    script_content = """#!/usr/bin/env bash
set -euo pipefail

mkdir -p third_party/riscv-opcodes physical testbench/generated viewer/src docs output .codegen-cache

if [ "{instr_dict}" != "third_party/riscv-opcodes/instr_dict.json" ]; then
    cp "{instr_dict}" third_party/riscv-opcodes/instr_dict.json
fi

for f in {synth_wrappers}; do
    if [ -f "$f" ] && [ "$(dirname "$f")" != "physical" ]; then
        cp "$f" physical/
    fi
done

"{generator}" --force

mkdir -p "{sv_dir}" "{netlist_dir}" "{asap7_dir}" "{gf180_dir}" "{sec_dir}" "{cpp_sim_dir}" "{testbench_dir}"
cp -a output/sv-from-lean/. "{sv_dir}/"
cp -a output/sv-netlist/. "{netlist_dir}/"
cp -a output/sv-asap7/. "{asap7_dir}/"
cp -a output/sv-gf180/. "{gf180_dir}/"
cp -a output/sv-sec/. "{sec_dir}/"
cp -a output/cpp_sim/. "{cpp_sim_dir}/"
cp -a testbench/generated/. "{testbench_dir}/"
cp output/config.mk "{config_mk}"
cp testbench/generated/cosim_main_tb_cpu.cpp "{cosim_main}"
cp testbench/generated/sim_main_tb_cpu.cpp "{sim_main}"
cp testbench/generated/tb_cpu.sv "{tb_cpu_sv}"
""".format(
        instr_dict = ctx.file.instr_dict.path,
        synth_wrappers = " ".join([f.path for f in ctx.files.synth_wrappers]),
        generator = ctx.executable.generator.path,
        sv_dir = sv_dir.path,
        netlist_dir = netlist_dir.path,
        asap7_dir = asap7_dir.path,
        gf180_dir = gf180_dir.path,
        sec_dir = sec_dir.path,
        cpp_sim_dir = cpp_sim_dir.path,
        testbench_dir = testbench_dir.path,
        config_mk = config_mk.path,
        cosim_main = cosim_main.path,
        sim_main = sim_main.path,
        tb_cpu_sv = tb_cpu_sv.path,
    )

    ctx.actions.write(
        output = script,
        content = script_content,
        is_executable = True,
    )

    inputs = [
        ctx.file.instr_dict,
    ] + ctx.files.synth_wrappers

    outputs = [
        sv_dir,
        netlist_dir,
        asap7_dir,
        gf180_dir,
        sec_dir,
        cpp_sim_dir,
        testbench_dir,
        config_mk,
        cosim_main,
        sim_main,
        tb_cpu_sv,
    ]

    ctx.actions.run(
        executable = script,
        inputs = inputs,
        outputs = outputs,
        tools = [ctx.executable.generator],
        mnemonic = "LeanRtlGen",
        progress_message = "Generating Shoumei RTL from Lean (%{label})",
    )

    return [
        DefaultInfo(
            files = depset([sv_dir]),
            runfiles = ctx.runfiles(files = outputs),
        ),
        OutputGroupInfo(
            sv = depset([sv_dir]),
            netlist = depset([netlist_dir]),
            asap7 = depset([asap7_dir]),
            gf180 = depset([gf180_dir]),
            sec = depset([sec_dir]),
            cpp_sim = depset([cpp_sim_dir]),
            testbench = depset([testbench_dir]),
            config_mk = depset([config_mk]),
            cosim_main = depset([cosim_main]),
            sim_main = depset([sim_main]),
            tb_cpu_sv = depset([tb_cpu_sv]),
            all = depset(outputs),
        ),
    ]

shoumei_rtl_raw = rule(
    implementation = _shoumei_rtl_impl,
    attrs = {
        "generator": attr.label(
            executable = True,
            cfg = "exec",
            mandatory = True,
            doc = "The lean_binary generator executable (generate_all).",
        ),
        "instr_dict": attr.label(
            allow_single_file = True,
            mandatory = True,
            doc = "The riscv-opcodes instr_dict.json file.",
        ),
        "synth_wrappers": attr.label_list(
            allow_files = True,
            doc = "Physical synthesis wrapper files (*_synth.sv).",
        ),
    },
    doc = "Executes the Lean RTL code generator and produces SystemVerilog and simulation models.",
)

def _output_group_filter_impl(ctx):
    group = ctx.attr.group
    files = getattr(ctx.attr.target[OutputGroupInfo], group)
    return [
        DefaultInfo(
            files = files,
            runfiles = ctx.runfiles(transitive_files = files),
        ),
    ]

_output_group_target = rule(
    implementation = _output_group_filter_impl,
    attrs = {
        "group": attr.string(mandatory = True),
        "target": attr.label(mandatory = True),
    },
)

def shoumei_rtl(name, generator = "//generators:generate_all", instr_dict = "//generators:instr_dict", synth_wrappers = None):
    """Macro providing the RTL generation suite with convenient subtargets."""
    if synth_wrappers == None:
        synth_wrappers = native.glob(["physical/*_synth.sv"])

    raw_name = name + "_raw"
    shoumei_rtl_raw(
        name = raw_name,
        generator = generator,
        instr_dict = instr_dict,
        synth_wrappers = synth_wrappers,
    )

    _output_group_target(
        name = "sv",
        target = ":" + raw_name,
        group = "sv",
    )
    _output_group_target(
        name = "sv_netlist",
        target = ":" + raw_name,
        group = "netlist",
    )
    _output_group_target(
        name = "sv_asap7",
        target = ":" + raw_name,
        group = "asap7",
    )
    _output_group_target(
        name = "sv_gf180",
        target = ":" + raw_name,
        group = "gf180",
    )
    _output_group_target(
        name = "sv_sec",
        target = ":" + raw_name,
        group = "sec",
    )
    _output_group_target(
        name = "cpp_sim",
        target = ":" + raw_name,
        group = "cpp_sim",
    )
    _output_group_target(
        name = "testbench",
        target = ":" + raw_name,
        group = "testbench",
    )
    _output_group_target(
        name = "cosim_main",
        target = ":" + raw_name,
        group = "cosim_main",
    )
    _output_group_target(
        name = "sim_main",
        target = ":" + raw_name,
        group = "sim_main",
    )
    _output_group_target(
        name = "tb_cpu_sv",
        target = ":" + raw_name,
        group = "tb_cpu_sv",
    )
    _output_group_target(
        name = name,
        target = ":" + raw_name,
        group = "all",
    )

    structural_lint_test(
        name = "lint_structural_test",
        generator = generator,
        sv = ":sv",
    )

def _structural_lint_test_impl(ctx):
    script = ctx.actions.declare_file(ctx.label.name + ".sh")
    sv_file = ctx.files.sv[0]
    content = """#!/usr/bin/env bash
set -euo pipefail

RUNFILES="${{RUNFILES_DIR:-$0.runfiles}}"
cd "$RUNFILES/{workspace}"

exec "./{generator}" --lint-structural "--sv-dir={sv_dir}"
""".format(
        workspace = ctx.workspace_name,
        generator = ctx.executable.generator.short_path,
        sv_dir = sv_file.short_path,
    )
    ctx.actions.write(
        output = script,
        content = content,
        is_executable = True,
    )
    runfiles = ctx.runfiles(
        files = [ctx.executable.generator],
        transitive_files = ctx.attr.sv[DefaultInfo].files,
    )
    return [DefaultInfo(executable = script, runfiles = runfiles)]

structural_lint_test = rule(
    implementation = _structural_lint_test_impl,
    test = True,
    attrs = {
        "generator": attr.label(
            executable = True,
            cfg = "exec",
            mandatory = True,
            doc = "The generator executable.",
        ),
        "sv": attr.label(
            allow_files = True,
            mandatory = True,
            doc = "The target providing the SystemVerilog directory artifact.",
        ),
    },
    doc = "Runs Lean's native structural linter on emitted SystemVerilog.",
)
