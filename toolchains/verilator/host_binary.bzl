"""Helper rule to expose an executable script as an executable target."""

def _host_binary_impl(ctx):
    out = ctx.actions.declare_file(ctx.label.name)
    ctx.actions.symlink(
        output = out,
        target_file = ctx.file.src,
        is_executable = True,
    )
    return [
        DefaultInfo(
            executable = out,
            runfiles = ctx.runfiles(files = [out, ctx.file.src]),
        ),
    ]

host_binary = rule(
    implementation = _host_binary_impl,
    executable = True,
    attrs = {
        "src": attr.label(allow_single_file = True, mandatory = True),
    },
)
