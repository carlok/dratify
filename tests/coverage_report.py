# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Statement coverage over `src/dratify`, with a floor CI enforces.

Uses the standard library's `trace` module rather than coverage.py, because
this package promises zero dependencies and that promise should hold for the
tools that check it too.

The floor exists to stop coverage drifting down quietly. Raise it when the
real number rises; never lower it to make a red build green -- if a change
drops coverage, the change needs tests, not a smaller number.
"""

from __future__ import annotations

import argparse
import dis
import io
import pathlib
import sys
import trace
import unittest

ROOT = pathlib.Path(__file__).resolve().parent.parent
SRC = ROOT / "src" / "dratify"
FLOOR = 80.0


def executable_lines(path: pathlib.Path) -> set[int]:
    """Lines the interpreter can actually reach, via the compiled code object.

    Counting source lines instead would include docstrings, blank lines and
    `def` headers, which `trace` reports inconsistently.
    """
    lines: set[int] = set()
    stack = [compile(path.read_text(), str(path), "exec")]
    while stack:
        code = stack.pop()
        lines.update(ln for _, ln in dis.findlinestarts(code) if ln)
        stack.extend(c for c in code.co_consts if hasattr(c, "co_code"))
    return lines


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--floor", type=float, default=FLOOR)
    args = ap.parse_args()

    sys.path.insert(0, str(ROOT / "src"))
    sys.path.insert(0, str(ROOT / "tests"))

    tracer = trace.Trace(count=1, trace=0, ignoredirs=[sys.prefix])
    result_holder = {}

    def run() -> None:
        suite = unittest.TestLoader().discover(str(ROOT / "tests"),
                                               top_level_dir=str(ROOT / "tests"))
        result_holder["r"] = unittest.TextTestRunner(
            stream=io.StringIO(), verbosity=0).run(suite)

    tracer.runfunc(run)
    counts = tracer.results().counts

    r = result_holder["r"]
    if not r.wasSuccessful():
        print(f"c {len(r.failures)} failures, {len(r.errors)} errors -- "
              f"coverage of a red suite means nothing")
        return 1

    print(f"  {'module':<18}{'stmts':>7}{'covered':>9}{'missed':>8}{'%':>6}")
    total_s = total_h = 0
    for path in sorted(SRC.glob("*.py")):
        exe = executable_lines(path)
        hit = {ln for (fn, ln) in counts if pathlib.Path(fn).name == path.name}
        covered = len(exe & hit)
        total_s += len(exe)
        total_h += covered
        pct = 100 * covered / len(exe) if exe else 100.0
        print(f"  {path.name:<18}{len(exe):>7}{covered:>9}"
              f"{len(exe) - covered:>8}{pct:>5.0f}%")

    pct = 100 * total_h / total_s if total_s else 100.0
    print(f"  {'TOTAL':<18}{total_s:>7}{total_h:>9}{total_s - total_h:>8}"
          f"{pct:>5.0f}%")
    print(f"c {r.testsRun} tests, floor {args.floor:.0f}%")

    if pct + 1e-9 < args.floor:
        print(f"c FAIL: {pct:.1f}% is below the {args.floor:.0f}% floor")
        return 1
    print("c OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
