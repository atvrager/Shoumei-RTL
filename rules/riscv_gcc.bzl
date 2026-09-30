"""The pinned RISC-V bare-metal toolchain, downloaded by Bazel.

The compiler finds its headers, libraries and subprograms relative to its own
executable.  An action that runs it therefore needs the whole archive as input,
which the `files` filegroup provides.
"""

_URL = "https://github.com/xpack-dev-tools/riscv-none-elf-gcc-xpack/releases/download/v15.2.0-1/xpack-riscv-none-elf-gcc-15.2.0-1-linux-x64.tar.gz"
_SHA256 = "aaaa8060c914851a3e5ee1ba82cc3d6f80972f90638a05c6e823a37557a33758"
_PREFIX = "xpack-riscv-none-elf-gcc-15.2.0-1"

_BUILD = """package(default_visibility = ["//visibility:public"])

filegroup(
    name = "gcc",
    srcs = ["bin/riscv-none-elf-gcc"],
)

filegroup(
    name = "files",
    srcs = glob(
        [
            "bin/**",
            "include/**",
            "lib/**",
            "libexec/**",
            "riscv-none-elf/**",
        ],
        allow_empty = True,
    ),
)
"""

def _riscv_gcc_repo_impl(rctx):
    rctx.download_and_extract(
        sha256 = _SHA256,
        stripPrefix = _PREFIX,
        url = _URL,
    )
    rctx.file("BUILD.bazel", _BUILD)

riscv_gcc_repo = repository_rule(implementation = _riscv_gcc_repo_impl)

def _riscv_gcc_ext_impl(_ctx):
    riscv_gcc_repo(name = "riscv_gcc")

riscv_gcc_ext = module_extension(implementation = _riscv_gcc_ext_impl)

def _riscv_toolchain_impl(ctx):
    return [platform_common.ToolchainInfo(
        files = depset(ctx.files.files),
        gcc = ctx.file.gcc,
    )]

riscv_toolchain = rule(
    implementation = _riscv_toolchain_impl,
    attrs = {
        "files": attr.label(allow_files = True, mandatory = True),
        "gcc": attr.label(allow_single_file = True, mandatory = True),
    },
    doc = "The `riscv-none-elf` compiler driver and its support tree.",
)
