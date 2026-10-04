"""The seed of the generated random tests, as a command line flag.

A `gen_seed` target is an integer build setting.  It also exports the value
as the make variable `GEN_SEED`, so a genrule that lists the target in
`toolchains` can read `$(GEN_SEED)`.

    bazel test //testbench/tests/generated:cosim_tests \\
        --//testbench/tests/generated:seed=1001
"""

def _gen_seed_impl(ctx):
    return [platform_common.TemplateVariableInfo({
        "GEN_SEED": str(ctx.build_setting_value),
    })]

gen_seed = rule(
    implementation = _gen_seed_impl,
    build_setting = config.int(flag = True),
    doc = "An integer flag that sets the make variable GEN_SEED.",
)
