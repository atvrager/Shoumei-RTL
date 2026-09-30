"""Prebuilt lint tools.

`ruff` (lint and format), `ty` (type check) and `shellcheck` each ship as one
static binary, so a download and a filegroup are enough.  No pip step, no
system package, and the version is pinned with a checksum.
"""

_SHELLCHECK_VERSION = "0.11.0"
_RUFF_VERSION = "0.16.9"
_TY_VERSION = "0.0.84"
_RELEASES = "https://github.com/astral-sh"

_BUILD_TEMPLATE = """package(default_visibility = ["//visibility:public"])

filegroup(
    name = "bin",
    srcs = ["{tool}"],
)
"""

def _tool_repo_impl(rctx):
    rctx.download_and_extract(
        url = rctx.attr.url,
        sha256 = rctx.attr.sha256,
        stripPrefix = rctx.attr.strip_prefix,
    )
    rctx.file("BUILD.bazel", _BUILD_TEMPLATE.format(tool = rctx.attr.tool))

tool_repository = repository_rule(
    implementation = _tool_repo_impl,
    attrs = {
        "url": attr.string(mandatory = True),
        "sha256": attr.string(mandatory = True),
        "strip_prefix": attr.string(mandatory = True),
        "tool": attr.string(mandatory = True),
    },
)

def _lint_tools_impl(_ctx):
    tool_repository(
        name = "ruff",
        tool = "ruff",
        url = "%s/ruff/releases/download/%s/ruff-x86_64-unknown-linux-musl.tar.gz" % (_RELEASES, _RUFF_VERSION),
        sha256 = "6a561ed4bc860472f7833dfb0f0b8285d3969fa627188c5678ea4ac2c462bbee",
        strip_prefix = "ruff-x86_64-unknown-linux-musl",
    )
    tool_repository(
        name = "shellcheck",
        tool = "shellcheck",
        url = "https://github.com/koalaman/shellcheck/releases/download/v{0}/shellcheck-v{0}.linux.x86_64.tar.gz".format(_SHELLCHECK_VERSION),
        sha256 = "b7af85e41cc99489dcc21d66c6d5f3685138f06d34651e6d34b42ec6d54fe6f6",
        strip_prefix = "shellcheck-v" + _SHELLCHECK_VERSION,
    )
    tool_repository(
        name = "ty",
        tool = "ty",
        url = "%s/ty/releases/download/%s/ty-x86_64-unknown-linux-musl.tar.gz" % (_RELEASES, _TY_VERSION),
        sha256 = "da32bd4cbfe124f1df974e78cc163037c5d4b12ceec532b7ed785b5b74a76cd1",
        strip_prefix = "ty-x86_64-unknown-linux-musl",
    )

lint_tools = module_extension(
    implementation = _lint_tools_impl,
)
