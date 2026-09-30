"""Pinned node and typescript for the viewer bundle.

Node finds its own modules relative to its executable, and the `tsc` entry
point imports the compiler from its package.  Both trees therefore travel
with the tool.
"""

_NODE_URL = "https://nodejs.org/dist/v24.21.0/node-v24.21.0-linux-x64.tar.xz"
_NODE_SHA256 = "fd8e59d5a511510f6a298afb548f18c7d2b1be404d8b4a27d94fbe49f56cb2d6"
_NODE_PREFIX = "node-v24.21.0-linux-x64"

_NODE_BUILD = """package(default_visibility = ["//visibility:public"])

filegroup(
    name = "node",
    srcs = ["bin/node"],
    data = glob(["lib/**"], allow_empty = True),
)
"""

_TYPESCRIPT_URL = "https://registry.npmjs.org/typescript/-/typescript-5.9.3.tgz"
_TYPESCRIPT_SHA256 = "10e108c9cf7d5f2879053dff18515fb405abf2ccef63eaaf017d9c571687a1d3"

_TYPESCRIPT_BUILD = """package(default_visibility = ["//visibility:public"])

filegroup(
    name = "tsc",
    srcs = ["bin/tsc"],
    data = glob(
        [
            "dist/**",
            "lib/**",
        ],
        allow_empty = True,
    ),
)
"""

def _download_repo_impl(rctx):
    rctx.download_and_extract(
        sha256 = rctx.attr.sha256,
        stripPrefix = rctx.attr.strip_prefix,
        url = rctx.attr.url,
    )
    rctx.file("BUILD.bazel", rctx.attr.build_file_content)

_download_repo = repository_rule(
    implementation = _download_repo_impl,
    attrs = {
        "build_file_content": attr.string(mandatory = True),
        "sha256": attr.string(mandatory = True),
        "strip_prefix": attr.string(),
        "url": attr.string(mandatory = True),
    },
)

def _node_tools_ext_impl(_ctx):
    _download_repo(
        name = "node",
        build_file_content = _NODE_BUILD,
        sha256 = _NODE_SHA256,
        strip_prefix = _NODE_PREFIX,
        url = _NODE_URL,
    )
    _download_repo(
        name = "typescript",
        build_file_content = _TYPESCRIPT_BUILD,
        sha256 = _TYPESCRIPT_SHA256,
        strip_prefix = "package",
        url = _TYPESCRIPT_URL,
    )

node_tools_ext = module_extension(implementation = _node_tools_ext_impl)
