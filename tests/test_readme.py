# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Every Python example in the README has to run, and print what it says.

The README is the first code a visitor copies, usually from the PyPI page, and
nothing executed it. The PySAT example was broken for the most common input
there is: given a SATLIB benchmark file it failed on its first line, inside
PySAT's parser, on the trailing `%` those files end with. The checker never
ran. It had read that way through five releases.

Each ```python block runs in a fresh namespace inside a temporary directory
that holds a real `problem.cnf` and `proof.drat`, so the examples can stay as
readers see them. A `print(x)  # value` line is an assertion: the printed
value must match the first word of the comment, so an example that runs but
returns the wrong answer fails too.

A block preceded by `<!-- readme-test: skip ... -->` is not executed. That is
for listings that are not programs, and the marker sits in the README where
the next editor will see it.

The PySAT example needs `python-sat`, which this package does not depend on.
It skips without it; a CI job installs it and fails if the test skipped.
"""

from __future__ import annotations

import contextlib
import io
import os
import pathlib
import re
import shutil
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parent.parent
FIXTURES = pathlib.Path(__file__).resolve().parent

SKIP = re.compile(r"<!--\s*readme-test:\s*skip")
EXPECT = re.compile(r"^\s*print\(.*\)\s*#\s*(\S+)")


def blocks(markdown: str) -> list[tuple[int, str, bool]]:
    """(line number, source, skipped) for every ```python block."""
    lines = markdown.splitlines()
    out, i = [], 0
    while i < len(lines):
        if lines[i].strip() == "```python":
            start = i + 1
            skipped = i > 0 and bool(SKIP.search(lines[i - 1]))
            j = start
            while lines[j].strip() != "```":
                j += 1
            out.append((start + 1, "\n".join(lines[start:j]) + "\n", skipped))
            i = j
        i += 1
    return out


def expected_output(source: str) -> list[str]:
    return [m.group(1) for ln in source.splitlines()
            if (m := EXPECT.match(ln))]


def run_block(source: str, workdir: pathlib.Path) -> list[str]:
    """Execute in a fresh namespace from `workdir`; return printed lines."""
    out = io.StringIO()
    here = os.getcwd()
    os.chdir(workdir)
    try:
        with contextlib.redirect_stdout(out):
            exec(compile(source, "README.md", "exec"), {"__name__": "__readme__"})
    finally:
        os.chdir(here)
    return out.getvalue().split()


def has_pysat() -> bool:
    try:
        import pysat.solvers  # noqa: F401
    except ImportError:
        return False
    return True


class TestReadmeExamples(unittest.TestCase):
    def setUp(self):
        self.dir = pathlib.Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, self.dir)
        # A real refutation, not a stub: the examples check a genuine proof.
        shutil.copy(FIXTURES / "php32.cnf", self.dir / "problem.cnf")
        shutil.copy(FIXTURES / "php32.drat", self.dir / "proof.drat")
        self.all = blocks((ROOT / "README.md").read_text(encoding="utf-8"))

    def test_the_readme_has_examples_to_test(self):
        """Guards the extractor: a regex that matches nothing passes everything."""
        self.assertGreaterEqual(len(self.all), 3)
        self.assertTrue(any(skipped for _, _, skipped in self.all),
                        "the skip marker was not recognised")

    def _check(self, lineno: int, source: str):
        want = expected_output(source)
        got = run_block(source, self.dir)
        self.assertEqual(
            got, want,
            f"README.md:{lineno} printed {got}, but its comments promise "
            f"{want}")

    def test_every_example_runs_and_prints_what_it_promises(self):
        ran = 0
        for lineno, source, skipped in self.all:
            if skipped or "pysat" in source:
                continue
            with self.subTest(line=lineno):
                self._check(lineno, source)
                ran += 1
        self.assertGreater(ran, 0, "no dependency-free example was run")

    @unittest.skipUnless(has_pysat(), "python-sat not installed; CI installs it")
    def test_the_pysat_example(self):
        pysat_blocks = [(n, s) for n, s, skipped in self.all
                        if not skipped and "pysat" in s]
        self.assertTrue(pysat_blocks, "the README no longer has a PySAT example")
        for lineno, source in pysat_blocks:
            with self.subTest(line=lineno):
                self._check(lineno, source)

    @unittest.skipUnless(has_pysat(), "python-sat not installed; CI installs it")
    def test_the_pysat_example_reads_a_satlib_file_as_distributed(self):
        """The input that broke it: a SATLIB file ending in `%` and `0`."""
        text = (self.dir / "problem.cnf").read_text().rstrip("\n")
        (self.dir / "problem.cnf").write_text(text + "\n%\n0\n\n")
        for lineno, source, skipped in self.all:
            if not skipped and "pysat" in source:
                with self.subTest(line=lineno):
                    self._check(lineno, source)


if __name__ == "__main__":
    unittest.main()
