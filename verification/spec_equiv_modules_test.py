"""Check that SPEC_EQUIV_MODULES equals the spec registry of spec-equiv.py.

The arguments are the module names in verification/spec_equiv_modules.bzl.
"""

import importlib.util
import pathlib
import sys


def main() -> int:
    listed = sorted(sys.argv[1:])
    spec = importlib.util.spec_from_file_location("se", pathlib.Path("scripts/spec-equiv.py"))
    assert spec is not None and spec.loader is not None
    se = importlib.util.module_from_spec(spec)
    sys.argv = sys.argv[:1]
    spec.loader.exec_module(se)
    registry = sorted(se.load_registry())
    missing = sorted(set(registry) - set(listed))
    extra = sorted(set(listed) - set(registry))
    for name in missing:
        print(f"not in spec_equiv_modules.bzl: {name}")
    for name in extra:
        print(f"not in the spec registry: {name}")
    if missing or extra:
        print("Update verification/spec_equiv_modules.bzl.")
        return 1
    print(f"{len(listed)} modules match the spec registry")
    return 0


if __name__ == "__main__":
    sys.exit(main())
