"""Repository rule for ORFS PDK liberty files."""

def _orfs_pdk_impl(rctx):
    platforms_src = rctx.path(Label("//:MODULE.bazel")).dirname.get_child("third_party").get_child("orfs").get_child("flow").get_child("platforms")
    rctx.symlink(platforms_src, "platforms")
    rctx.file("BUILD.bazel", """
package(default_visibility = ["//visibility:public"])

filegroup(
    name = "liberty",
    srcs = glob([
        "platforms/asap7/lib/NLDM/*.lib.gz",
        "platforms/asap7/lib/NLDM/*.lib",
        "platforms/gf180/lib/*.lib.gz",
    ]),
)
""")

orfs_pdk_repo = repository_rule(
    implementation = _orfs_pdk_impl,
)

def _pdk_ext_impl(_ctx):
    orfs_pdk_repo(name = "orfs_pdk")

pdk_ext = module_extension(
    implementation = _pdk_ext_impl,
)
