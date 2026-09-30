"""Rules for compiling RISC-V ELFs and executing Shoumei simulation tests."""

def _riscv_elf_impl(ctx):
    out_name = ctx.label.name if ctx.label.name.endswith(".elf") else ctx.label.name + ".elf"
    out = ctx.actions.declare_file(out_name)

    inputs = list(ctx.files.srcs)
    if ctx.file.crt0:
        inputs.append(ctx.file.crt0)
    if ctx.file.linker_script:
        inputs.append(ctx.file.linker_script)
    inputs.extend(ctx.files.hdrs)

    cmd = """#!/usr/bin/env bash
set -euo pipefail
CC="$(command -v riscv64-unknown-elf-gcc 2>/dev/null || command -v riscv64-elf-gcc 2>/dev/null || echo riscv64-unknown-elf-gcc)"
"$CC" -march={march} -mabi={mabi} -O2 -nostdlib -nostartfiles -ffreestanding \
  {extra_copts} \
  {linker_flag} \
  -nostdlib -Wl,--no-relax \
  {extra_linkopts} \
  {crt0} \
  {srcs} \
  -o "{out}"
""".format(
        march = ctx.attr.march,
        mabi = ctx.attr.mabi,
        extra_copts = " ".join(ctx.attr.copts),
        linker_flag = "-T " + ctx.file.linker_script.path if ctx.file.linker_script else "",
        extra_linkopts = " ".join(ctx.attr.linkopts),
        crt0 = ctx.file.crt0.path if ctx.file.crt0 else "",
        srcs = " ".join([f.path for f in ctx.files.srcs]),
        out = out.path,
    )

    ctx.actions.run_shell(
        command = cmd,
        inputs = inputs,
        outputs = [out],
        mnemonic = "RiscvElf",
        progress_message = "Compiling RISC-V ELF %{label}",
        use_default_shell_env = True,
    )

    return [DefaultInfo(files = depset([out]), runfiles = ctx.runfiles(files = [out]))]

riscv_elf = rule(
    implementation = _riscv_elf_impl,
    attrs = {
        "srcs": attr.label_list(
            allow_files = [".c", ".S", ".s"],
            mandatory = True,
            doc = "C or assembly source files.",
        ),
        "crt0": attr.label(
            allow_single_file = [".S", ".s"],
            doc = "Optional C runtime startup file (e.g. crt0.S).",
        ),
        "linker_script": attr.label(
            allow_single_file = [".ld"],
            doc = "Linker script.",
        ),
        "hdrs": attr.label_list(
            allow_files = [".h"],
            default = ["//testbench/tests:shoumei.h"],
            doc = "Header files required for compilation.",
        ),
        "march": attr.string(
            default = "rv64im_zicsr_zifencei",
            doc = "RISC-V architecture string.",
        ),
        "mabi": attr.string(
            default = "lp64",
            doc = "RISC-V ABI string.",
        ),
        "copts": attr.string_list(
            doc = "Additional compiler flags.",
        ),
        "linkopts": attr.string_list(
            doc = "Additional linker flags.",
        ),
    },
    doc = "Compiles RISC-V C and assembly source files into an ELF binary.",
)

def _shoumei_sim_test_impl(ctx):
    script = ctx.actions.declare_file(ctx.label.name + ".sh")
    content = """#!/usr/bin/env bash
set -euo pipefail

RUNFILES="${{RUNFILES_DIR:-$0.runfiles}}"
cd "$RUNFILES/{workspace}"

exec "./{sim_bin}" +elf="{elf}" +timeout={timeout_cycles} {extra_args}
""".format(
        workspace = ctx.workspace_name,
        sim_bin = ctx.executable.sim_binary.short_path,
        elf = ctx.file.elf.short_path,
        timeout_cycles = ctx.attr.timeout_cycles,
        extra_args = " ".join(ctx.attr.extra_args),
    )

    ctx.actions.write(
        output = script,
        content = content,
        is_executable = True,
    )

    runfiles = ctx.runfiles(
        files = [ctx.file.elf],
    ).merge(ctx.attr.sim_binary[DefaultInfo].default_runfiles)

    return [DefaultInfo(executable = script, runfiles = runfiles)]

shoumei_sim_test = rule(
    implementation = _shoumei_sim_test_impl,
    test = True,
    attrs = {
        "elf": attr.label(
            allow_single_file = [".elf"],
            mandatory = True,
            doc = "The RISC-V ELF file to simulate.",
        ),
        "sim_binary": attr.label(
            default = "//testbench:sim_shoumei",
            executable = True,
            cfg = "exec",
            doc = "The standalone simulation binary.",
        ),
        "timeout_cycles": attr.int(
            default = 100000,
            doc = "Cycle timeout limit.",
        ),
        "extra_args": attr.string_list(
            doc = "Extra plusargs to pass to the simulator.",
        ),
    },
    doc = "Runs an ELF on the Verilator standalone RTL simulation.",
)

def _shoumei_cosim_test_impl(ctx):
    script = ctx.actions.declare_file(ctx.label.name + ".sh")
    content = """#!/usr/bin/env bash
set -euo pipefail

RUNFILES="${{RUNFILES_DIR:-$0.runfiles}}"
cd "$RUNFILES/{workspace}"

exec "./{cosim_bin}" +elf="{elf}" +timeout={timeout_cycles} {extra_args}
""".format(
        workspace = ctx.workspace_name,
        cosim_bin = ctx.executable.cosim_binary.short_path,
        elf = ctx.file.elf.short_path,
        timeout_cycles = ctx.attr.timeout_cycles,
        extra_args = " ".join(ctx.attr.extra_args),
    )

    ctx.actions.write(
        output = script,
        content = content,
        is_executable = True,
    )

    runfiles = ctx.runfiles(
        files = [ctx.file.elf],
    ).merge(ctx.attr.cosim_binary[DefaultInfo].default_runfiles)

    return [DefaultInfo(executable = script, runfiles = runfiles)]

shoumei_cosim_test = rule(
    implementation = _shoumei_cosim_test_impl,
    test = True,
    attrs = {
        "elf": attr.label(
            allow_single_file = [".elf"],
            mandatory = True,
            doc = "The RISC-V ELF file to cosimulate.",
        ),
        "cosim_binary": attr.label(
            default = "//testbench:cosim_shoumei",
            executable = True,
            cfg = "exec",
            doc = "The Spike lockstep cosimulation binary.",
        ),
        "timeout_cycles": attr.int(
            default = 100000,
            doc = "Cycle timeout limit.",
        ),
        "extra_args": attr.string_list(
            doc = "Extra plusargs to pass to the cosimulator.",
        ),
    },
    doc = "Runs an ELF on the lockstep Spike cosimulator.",
)

def shoumei_elf_test(
        name,
        src,
        is_asm = False,
        is_fp = False,
        timeout_cycles = 100000,
        crt0 = None,
        linker_script = "//testbench/tests:shoumei.ld",
        hdrs = None,
        march = None,
        mabi = None,
        copts = None,
        linkopts = None,
        tags = None,
        **_kwargs):
    """Defines an ELF target, a sim test, a cosim test, and a combined test suite.

    Args:
      name: base name of the generated targets.
      src: the test source file.
      is_asm: True for a hand-written assembly test with no crt0.
      is_fp: True for a floating-point test.
      timeout_cycles: cycle budget passed to the simulation.
      crt0: startup object, when the test needs one.
      linker_script: linker script for the ELF.
      hdrs: extra headers the test includes.
      march: `-march` value for the compiler.
      mabi: `-mabi` value for the compiler.
      copts: extra compiler options.
      linkopts: extra linker options.
      tags: Bazel tags for the generated tests.
      **_kwargs: unused extra attributes.
    """
    elf_target = name + "_elf"
    sim_target = name + "_sim"
    cosim_target = name + "_cosim"
    spec_target = name + "_spec"

    if crt0 == None:
        crt0 = None if is_asm else "//testbench/tests:crt0.S"

    if march == None:
        march = "rv64imafd_zicsr_zifencei" if is_fp else "rv64im_zicsr_zifencei"

    if mabi == None:
        mabi = "lp64d" if is_fp else "lp64"

    riscv_elf(
        name = elf_target,
        srcs = [src],
        crt0 = crt0,
        linker_script = linker_script,
        hdrs = hdrs or ["//testbench/tests:shoumei.h"],
        march = march,
        mabi = mabi,
        copts = copts or [],
        linkopts = linkopts or [],
        tags = tags or [],
    )

    shoumei_sim_test(
        name = sim_target,
        elf = ":" + elf_target,
        timeout_cycles = timeout_cycles,
        tags = tags or [],
    )

    shoumei_cosim_test(
        name = cosim_target,
        elf = ":" + elf_target,
        timeout_cycles = timeout_cycles,
        tags = tags or [],
    )

    shoumei_sim_test(
        name = spec_target,
        elf = ":" + elf_target,
        sim_binary = "//testbench:sim_spec_shoumei",
        timeout_cycles = timeout_cycles,
        tags = tags or [],
    )

    native.test_suite(
        name = name,
        tests = [
            ":" + sim_target,
            ":" + cosim_target,
            ":" + spec_target,
        ],
        tags = tags or [],
    )

def pad4(n):
    """Pads integer n with leading zeros up to 4 digits."""
    s = str(n)
    return "0" * (4 - len(s)) + s
