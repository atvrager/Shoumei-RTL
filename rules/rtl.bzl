"""Rules for generating SystemVerilog and simulation models from Lean."""

CIRCUIT_SUBSYSTEMS = [
    "foundation",
    "combinational",
    "sequential",
    "renaming",
    "execution",
    "retirement",
    "memory",
    "control",
    "cpu",
    "soc",
    "decoders",
]

def _shoumei_subsystem_rtl_impl(ctx):
    subsystem = ctx.attr.subsystem
    sv_dir = ctx.actions.declare_directory(ctx.attr.name + "_sv")
    netlist_dir = ctx.actions.declare_directory(ctx.attr.name + "_netlist")
    asap7_dir = ctx.actions.declare_directory(ctx.attr.name + "_asap7")
    gf180_dir = ctx.actions.declare_directory(ctx.attr.name + "_gf180")
    cpp_sim_dir = ctx.actions.declare_directory(ctx.attr.name + "_cpp_sim")

    args = ctx.actions.args()
    args.add("--subsystem=" + subsystem)
    args.add("--out-sv=" + sv_dir.path)
    args.add("--out-netlist=" + netlist_dir.path)
    args.add("--out-asap7=" + asap7_dir.path)
    args.add("--out-gf180=" + gf180_dir.path)
    args.add("--out-cpp-sim=" + cpp_sim_dir.path)
    args.add("--skip-visuals")
    args.add("--skip-testbench")
    args.add("--skip-sec")

    inputs = []
    if ctx.file.instr_dict:
        inputs.append(ctx.file.instr_dict)
        args.add("--instr-dict=" + ctx.file.instr_dict.path)

    outputs = [sv_dir, netlist_dir, asap7_dir, gf180_dir, cpp_sim_dir]

    ctx.actions.run(
        executable = ctx.executable.generator,
        arguments = [args],
        inputs = inputs,
        outputs = outputs,
        mnemonic = "LeanRtlSubsystem",
        progress_message = "Generating Shoumei RTL subsystem %s" % subsystem,
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
            cpp_sim = depset([cpp_sim_dir]),
            all = depset(outputs),
        ),
    ]

shoumei_subsystem_rtl = rule(
    implementation = _shoumei_subsystem_rtl_impl,
    attrs = {
        "subsystem": attr.string(mandatory = True),
        "generator": attr.label(
            executable = True,
            cfg = "exec",
            mandatory = True,
        ),
        "instr_dict": attr.label(
            allow_single_file = True,
        ),
    },
)

def _shoumei_sec_rtl_impl(ctx):
    sec_dir = ctx.actions.declare_directory(ctx.attr.name + "_sec")

    args = ctx.actions.args()
    args.add("--subsystem=sec")
    args.add("--out-sec=" + sec_dir.path)
    args.add("--out-sv=output/sv-from-lean")
    args.add("--skip-visuals")
    args.add("--skip-testbench")
    args.add("--skip-decoders")

    outputs = [sec_dir]

    ctx.actions.run(
        executable = ctx.executable.generator,
        arguments = [args],
        inputs = [],
        outputs = outputs,
        mnemonic = "LeanRtlSec",
        progress_message = "Generating Shoumei RTL SEC miters",
    )

    return [
        DefaultInfo(
            files = depset([sec_dir]),
            runfiles = ctx.runfiles(files = outputs),
        ),
        OutputGroupInfo(
            sec = depset([sec_dir]),
            all = depset(outputs),
        ),
    ]

shoumei_sec_rtl = rule(
    implementation = _shoumei_sec_rtl_impl,
    attrs = {
        "generator": attr.label(
            executable = True,
            cfg = "exec",
            mandatory = True,
        ),
    },
)

def _shoumei_testbench_rtl_impl(ctx):
    testbench_dir = ctx.actions.declare_directory(ctx.attr.name + "_testbench")
    config_mk = ctx.actions.declare_file(ctx.attr.name + "_config.mk")
    cosim_main = ctx.actions.declare_file(ctx.attr.name + "_cosim_main_tb_cpu.cpp")
    sim_main = ctx.actions.declare_file(ctx.attr.name + "_sim_main_tb_cpu.cpp")
    tb_cpu_sv = ctx.actions.declare_file(ctx.attr.name + "_tb_cpu.sv")

    script = ctx.actions.declare_file(ctx.attr.name + "_run.sh")
    script_content = """#!/usr/bin/env bash
set -euo pipefail

"{generator}" \\
    --subsystem=testbench \\
    --out-testbench="{testbench_dir}" \\
    --out-config-mk="{config_mk}" \\
    --skip-visuals \\
    --skip-decoders \\
    --skip-sec

cp "{testbench_dir}/cosim_main_tb_cpu.cpp" "{cosim_main}"
cp "{testbench_dir}/sim_main_tb_cpu.cpp" "{sim_main}"
cp "{testbench_dir}/tb_cpu.sv" "{tb_cpu_sv}"
""".format(
        generator = ctx.executable.generator.path,
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

    outputs = [testbench_dir, config_mk, cosim_main, sim_main, tb_cpu_sv]

    ctx.actions.run(
        executable = script,
        inputs = [],
        outputs = outputs,
        tools = [ctx.executable.generator],
        mnemonic = "LeanRtlTestbench",
        progress_message = "Generating Shoumei RTL testbenches",
    )

    return [
        DefaultInfo(
            files = depset([testbench_dir]),
            runfiles = ctx.runfiles(files = outputs),
        ),
        OutputGroupInfo(
            testbench = depset([testbench_dir]),
            config_mk = depset([config_mk]),
            cosim_main = depset([cosim_main]),
            sim_main = depset([sim_main]),
            tb_cpu_sv = depset([tb_cpu_sv]),
            all = depset(outputs),
        ),
    ]

shoumei_testbench_rtl = rule(
    implementation = _shoumei_testbench_rtl_impl,
    attrs = {
        "generator": attr.label(
            executable = True,
            cfg = "exec",
            mandatory = True,
        ),
    },
)

def _shoumei_merge_dirs_impl(ctx):
    out_dir = ctx.actions.declare_directory(ctx.attr.name)
    group = ctx.attr.group
    ext = ctx.attr.extension

    all_inputs = []
    for t in ctx.attr.targets:
        if group and OutputGroupInfo in t and hasattr(t[OutputGroupInfo], group):
            all_inputs.extend(getattr(t[OutputGroupInfo], group).to_list())
        elif DefaultInfo in t:
            all_inputs.extend(t[DefaultInfo].files.to_list())

    script = ctx.actions.declare_file(ctx.attr.name + "_merge.sh")
    script_content = """#!/usr/bin/env bash
set -euo pipefail

out="{out_dir}"
mkdir -p "$out"

for d in {dirs}; do
    if [ -d "$d" ]; then
        cp -R -f "$d/." "$out/"
        chmod -R u+w "$out" || true
    fi
done

if [ -n "{ext}" ]; then
    find "$out" -maxdepth 1 -name "*{ext}" -exec basename {{}} \\; | sort > "$out/filelist.f"
fi
""".format(
        out_dir = out_dir.path,
        dirs = " ".join([d.path for d in all_inputs]),
        ext = ext,
    )

    ctx.actions.write(
        output = script,
        content = script_content,
        is_executable = True,
    )

    ctx.actions.run(
        executable = script,
        inputs = all_inputs,
        outputs = [out_dir],
        mnemonic = "MergeDirs",
        progress_message = "Merging %{label}",
    )

    return [DefaultInfo(files = depset([out_dir]))]

shoumei_merge_dirs = rule(
    implementation = _shoumei_merge_dirs_impl,
    attrs = {
        "targets": attr.label_list(mandatory = True),
        "group": attr.string(default = ""),
        "extension": attr.string(default = ""),
    },
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

def _shoumei_workspace_sync_impl(ctx):
    script = ctx.actions.declare_file(ctx.attr.name + ".sh")

    content = """#!/usr/bin/env bash
set -euo pipefail

MODE="${{1:---copy}}"

if [ -z "${{BUILD_WORKSPACE_DIRECTORY:-}}" ]; then
    echo "ERROR: BUILD_WORKSPACE_DIRECTORY is not set. Run this target via 'bazel run'." >&2
    exit 1
fi

cd "$BUILD_WORKSPACE_DIRECTORY"

if [ -n "${{RUNFILES_DIR:-}}" ]; then
    RUNFILES="$RUNFILES_DIR"
elif [ -d "$0.runfiles" ]; then
    RUNFILES="$0.runfiles"
else
    RUNFILES="$(cd "$(dirname "$0")" && pwd)"
fi

WS_NAME="{workspace}"
if [ -d "$RUNFILES/$WS_NAME" ]; then
    BASE="$RUNFILES/$WS_NAME"
else
    BASE="$RUNFILES"
fi

SV_DIR="$BASE/{sv_path}"
NETLIST_DIR="$BASE/{netlist_path}"
ASAP7_DIR="$BASE/{asap7_path}"
GF180_DIR="$BASE/{gf180_path}"
SEC_DIR="$BASE/{sec_path}"
CPP_SIM_DIR="$BASE/{cpp_sim_path}"
TB_DIR="$BASE/{tb_path}"
CONFIG_MK="$BASE/{config_mk_path}"

mkdir -p output testbench

sync_dir() {{
    local src="$1"
    local dst="$2"
    if [ "$MODE" = "--copy" ]; then
        if [ -L "$dst" ]; then rm -f "$dst"; fi
        mkdir -p "$dst"
        cp -R -f "$src/." "$dst/"
    else
        rm -rf "$dst"
        ln -sfn "$(readlink -f "$src")" "$dst"
    fi
}}

sync_file() {{
    local src="$1"
    local dst="$2"
    mkdir -p "$(dirname "$dst")"
    if [ "$MODE" = "--copy" ]; then
        if [ -L "$dst" ]; then rm -f "$dst"; fi
        cp -f "$src" "$dst"
    else
        rm -rf "$dst"
        ln -sfn "$(readlink -f "$src")" "$dst"
    fi
}}

sync_dir "$SV_DIR" output/sv-from-lean
sync_dir "$NETLIST_DIR" output/sv-netlist
sync_dir "$ASAP7_DIR" output/sv-asap7
sync_dir "$GF180_DIR" output/sv-gf180
sync_dir "$SEC_DIR" output/sv-sec
sync_dir "$CPP_SIM_DIR" output/cpp_sim
sync_dir "$TB_DIR" testbench/generated
sync_file "$CONFIG_MK" output/config.mk

if [ "$MODE" = "--copy" ]; then
    echo "✓ Synced Shoumei RTL outputs into workspace (copied)"
else
    echo "✓ Synced Shoumei RTL outputs into workspace (symlinked)"
fi
""".format(
        workspace = ctx.workspace_name,
        sv_path = ctx.file.sv.short_path,
        netlist_path = ctx.file.netlist.short_path,
        asap7_path = ctx.file.asap7.short_path,
        gf180_path = ctx.file.gf180.short_path,
        sec_path = ctx.file.sec.short_path,
        cpp_sim_path = ctx.file.cpp_sim.short_path,
        tb_path = ctx.file.testbench.short_path,
        config_mk_path = ctx.file.config_mk.short_path,
    )

    ctx.actions.write(
        output = script,
        content = content,
        is_executable = True,
    )

    runfiles = ctx.runfiles(files = [
        ctx.file.sv,
        ctx.file.netlist,
        ctx.file.asap7,
        ctx.file.gf180,
        ctx.file.sec,
        ctx.file.cpp_sim,
        ctx.file.testbench,
        ctx.file.config_mk,
    ])

    return [DefaultInfo(executable = script, runfiles = runfiles)]

shoumei_workspace_sync = rule(
    implementation = _shoumei_workspace_sync_impl,
    executable = True,
    attrs = {
        "sv": attr.label(mandatory = True, allow_single_file = True),
        "netlist": attr.label(mandatory = True, allow_single_file = True),
        "asap7": attr.label(mandatory = True, allow_single_file = True),
        "gf180": attr.label(mandatory = True, allow_single_file = True),
        "sec": attr.label(mandatory = True, allow_single_file = True),
        "cpp_sim": attr.label(mandatory = True, allow_single_file = True),
        "testbench": attr.label(mandatory = True, allow_single_file = True),
        "config_mk": attr.label(mandatory = True, allow_single_file = True),
    },
)

def _shoumei_aggregate_rtl_impl(ctx):
    script = ctx.actions.declare_file(ctx.label.name)
    content = """#!/usr/bin/env bash
set -euo pipefail

if [ -n "${{RUNFILES_DIR:-}}" ]; then
    RUNFILES="$RUNFILES_DIR"
elif [ -d "$0.runfiles" ]; then
    RUNFILES="$0.runfiles"
else
    RUNFILES="$(cd "$(dirname "$0")" && pwd)"
fi

WS_NAME="{workspace}"
if [ -f "$RUNFILES/$WS_NAME/{sync_script}" ]; then
    EXEC_PATH="$RUNFILES/$WS_NAME/{sync_script}"
elif [ -f "$RUNFILES/{sync_script}" ]; then
    EXEC_PATH="$RUNFILES/{sync_script}"
elif [ -f "$(dirname "$0")/{sync_script}" ]; then
    EXEC_PATH="$(dirname "$0")/{sync_script}"
else
    EXEC_PATH="$(dirname "$0")/{sync_script}"
fi

exec "$EXEC_PATH" "$@"
""".format(
        workspace = ctx.workspace_name,
        sync_script = ctx.executable.sync_script.short_path,
    )
    ctx.actions.write(
        output = script,
        content = content,
        is_executable = True,
    )
    all_files = [
        ctx.file.sv,
        ctx.file.netlist,
        ctx.file.asap7,
        ctx.file.gf180,
        ctx.file.sec,
        ctx.file.cpp_sim,
        ctx.file.testbench,
        ctx.file.config_mk,
        ctx.file.cosim_main,
        ctx.file.sim_main,
        ctx.file.tb_cpu_sv,
    ]
    runfiles = ctx.runfiles(files = [ctx.executable.sync_script]).merge(
        ctx.attr.sync_script[DefaultInfo].default_runfiles,
    )
    return [
        DefaultInfo(
            files = depset(all_files),
            runfiles = runfiles,
            executable = script,
        ),
        OutputGroupInfo(
            sv = depset([ctx.file.sv]),
            netlist = depset([ctx.file.netlist]),
            asap7 = depset([ctx.file.asap7]),
            gf180 = depset([ctx.file.gf180]),
            sec = depset([ctx.file.sec]),
            cpp_sim = depset([ctx.file.cpp_sim]),
            testbench = depset([ctx.file.testbench]),
            config_mk = depset([ctx.file.config_mk]),
            cosim_main = depset([ctx.file.cosim_main]),
            sim_main = depset([ctx.file.sim_main]),
            tb_cpu_sv = depset([ctx.file.tb_cpu_sv]),
            all = depset(all_files),
        ),
    ]

shoumei_aggregate_rtl = rule(
    implementation = _shoumei_aggregate_rtl_impl,
    executable = True,
    attrs = {
        "sv": attr.label(mandatory = True, allow_single_file = True),
        "netlist": attr.label(mandatory = True, allow_single_file = True),
        "asap7": attr.label(mandatory = True, allow_single_file = True),
        "gf180": attr.label(mandatory = True, allow_single_file = True),
        "sec": attr.label(mandatory = True, allow_single_file = True),
        "cpp_sim": attr.label(mandatory = True, allow_single_file = True),
        "testbench": attr.label(mandatory = True, allow_single_file = True),
        "config_mk": attr.label(mandatory = True, allow_single_file = True),
        "cosim_main": attr.label(mandatory = True, allow_single_file = True),
        "sim_main": attr.label(mandatory = True, allow_single_file = True),
        "tb_cpu_sv": attr.label(mandatory = True, allow_single_file = True),
        "sync_script": attr.label(mandatory = True, executable = True, cfg = "exec"),
    },
)

def shoumei_rtl(
        name,
        generator = "//generators:generate_all",
        subsystem_generators = {},
        sec_generator = "//generators:generate_sec",
        testbench_generator = "//generators:gen_testbench",
        structural_lint_tool = "//generators:structural_lint",
        instr_dict = "//generators:instr_dict"):
    """Macro providing granular RTL generation suite with convenient subtargets.

    Args:
      name: name of the generation target.
      generator: the fallback `lean_binary` code generator to run.
      subsystem_generators: optional dictionary mapping subsystem name to generator label.
      sec_generator: generator label for SEC verification miters.
      testbench_generator: generator label for simulation testbenches.
      structural_lint_tool: binary for structural linting.
      instr_dict: the RISC-V instruction dictionary the generator reads.
    """
    effective_subsystem_generators = {
        "decoders": "//generators:generate_decoders",
    }
    effective_subsystem_generators.update(subsystem_generators)

    subsystem_targets = []
    for sub in CIRCUIT_SUBSYSTEMS:
        target_name = name + "_" + sub
        sub_generator = effective_subsystem_generators.get(sub, generator)
        shoumei_subsystem_rtl(
            name = target_name,
            subsystem = sub,
            generator = sub_generator,
            instr_dict = instr_dict,
        )
        subsystem_targets.append(":" + target_name)

    sec_target = name + "_sec"
    shoumei_sec_rtl(
        name = sec_target,
        generator = sec_generator,
    )

    tb_target = name + "_testbench"
    shoumei_testbench_rtl(
        name = tb_target,
        generator = testbench_generator,
    )

    shoumei_merge_dirs(
        name = "sv",
        targets = subsystem_targets,
        group = "sv",
        extension = ".sv",
    )
    shoumei_merge_dirs(
        name = "sv_netlist",
        targets = subsystem_targets,
        group = "netlist",
        extension = ".sv",
    )
    shoumei_merge_dirs(
        name = "sv_asap7",
        targets = subsystem_targets,
        group = "asap7",
        extension = ".sv",
    )
    shoumei_merge_dirs(
        name = "sv_gf180",
        targets = subsystem_targets,
        group = "gf180",
        extension = ".sv",
    )
    shoumei_merge_dirs(
        name = "cpp_sim_dir",
        targets = subsystem_targets,
        group = "cpp_sim",
        extension = ".h",
    )
    native.alias(
        name = "cpp_sim",
        actual = ":cpp_sim_dir",
    )

    _output_group_target(
        name = "sv_sec",
        target = ":" + sec_target,
        group = "sec",
    )
    _output_group_target(
        name = "testbench",
        target = ":" + tb_target,
        group = "testbench",
    )
    _output_group_target(
        name = "config_mk",
        target = ":" + tb_target,
        group = "config_mk",
    )
    _output_group_target(
        name = "cosim_main",
        target = ":" + tb_target,
        group = "cosim_main",
    )
    _output_group_target(
        name = "sim_main",
        target = ":" + tb_target,
        group = "sim_main",
    )
    _output_group_target(
        name = "tb_cpu_sv",
        target = ":" + tb_target,
        group = "tb_cpu_sv",
    )

    sync_name = "sync_" + name
    shoumei_workspace_sync(
        name = sync_name,
        sv = ":sv",
        netlist = ":sv_netlist",
        asap7 = ":sv_asap7",
        gf180 = ":sv_gf180",
        sec = ":sv_sec",
        cpp_sim = ":cpp_sim_dir",
        testbench = ":testbench",
        config_mk = ":config_mk",
    )

    shoumei_aggregate_rtl(
        name = name,
        sv = ":sv",
        netlist = ":sv_netlist",
        asap7 = ":sv_asap7",
        gf180 = ":sv_gf180",
        sec = ":sv_sec",
        cpp_sim = ":cpp_sim_dir",
        testbench = ":testbench",
        config_mk = ":config_mk",
        cosim_main = ":cosim_main",
        sim_main = ":sim_main",
        tb_cpu_sv = ":tb_cpu_sv",
        sync_script = ":" + sync_name,
    )

    structural_lint_test(
        name = "lint_structural_test",
        generator = structural_lint_tool,
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
