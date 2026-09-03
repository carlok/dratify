# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""The package metadata has to agree with the package.

This package states its version in three places that nothing connects:
`pyproject.toml`, `rust/Cargo.toml`, and `__init__.__version__`. They have
agreed so far because a human kept them in step. The release workflow does not
help -- it compares the git tag against the built sdist filename, so a tag can
match a Python version that the crate disagrees with, and both halves publish.

That matters more here than in most packages. The Python checker and the Rust
crate are two implementations of the same rules, and the whole claim this
project makes is that they agree with each other. A version that cannot say
which pair you are holding makes the claim uncheckable.
"""

from __future__ import annotations

import pathlib
import re
import unittest

ROOT = pathlib.Path(__file__).resolve().parent.parent


def _read(rel: str) -> str:
    return (ROOT / rel).read_text(encoding="utf-8")


def _toml_version(rel: str) -> str:
    """The first `version = "..."` in a TOML file's own package table."""
    m = re.search(r'^version = "([^"]+)"', _read(rel), re.M)
    assert m is not None, f"no version in {rel}"
    return m.group(1)


class TestVersions(unittest.TestCase):
    def test_python_and_rust_versions_agree(self):
        import dratify

        self.assertEqual(
            dratify.__version__, _toml_version("rust/Cargo.toml"),
            "src/dratify/__init__.py and rust/Cargo.toml disagree on the "
            "version. They are two implementations of one checker; if they "
            "cannot be identified as a matching pair, 'the two agree' is not "
            "a statement anyone can verify.")

    def test_pyproject_and_python_versions_agree(self):
        import dratify

        self.assertEqual(
            dratify.__version__, _toml_version("pyproject.toml"),
            "pyproject.toml and src/dratify/__version__ disagree. The wheel "
            "would install under a version the code does not report.")

    def test_version_is_a_release_number(self):
        import dratify

        self.assertRegex(dratify.__version__, r"^\d+\.\d+\.\d+([.-]\w+)?$")


class TestLicence(unittest.TestCase):
    """PEP 639 metadata, and the build backend that can actually emit it."""

    def test_package_metadata_declares_apache(self):
        self.assertRegex(_read("pyproject.toml"),
                         r'(?m)^\s*license\s*=\s*"Apache-2\.0"')

    def test_crate_declares_apache(self):
        self.assertIn('license = "Apache-2.0"', _read("rust/Cargo.toml"))

    def test_a_licence_file_is_present_and_is_apache(self):
        text = _read("LICENSE")
        self.assertIn("Apache License", text)
        self.assertIn("Version 2.0", text)

    def test_the_build_backend_is_new_enough_for_pep_639(self):
        """`license = "..."` as an SPDX string needs setuptools >= 77.

        Declared with an older floor, the build succeeds on a modern machine
        and fails on whatever pins an older setuptools -- the kind of break
        that only ever shows up in someone else's environment.
        """
        text = _read("pyproject.toml")
        if not re.search(r'(?m)^\s*license\s*=\s*"', text):
            self.skipTest("no PEP 639 licence expression")
        floor = re.search(r"setuptools\s*>=\s*(\d+)", text)
        self.assertIsNotNone(floor, "build-system does not pin setuptools")
        self.assertGreaterEqual(
            int(floor.group(1)), 77,
            "pyproject.toml uses the PEP 639 `license` expression, which "
            "setuptools only supports from 77. The declared floor is lower, "
            "so a build on an older setuptools emits wrong metadata or fails.")


class TestMetadata(unittest.TestCase):
    def test_the_urls_a_reader_needs_are_declared(self):
        text = _read("pyproject.toml")
        for key in ("Issues", "Changelog", "Source"):
            self.assertIn(f'{key} =', text,
                          f"[project.urls] has no {key} entry")

    def test_urls_into_this_repo_name_files_that_exist(self):
        """A metadata link to a file we never wrote is a dead link on PyPI.

        This is the failure that motivated the round: cdclkit's CHANGELOG
        pointed at `COPYRIGHT` and `docs/LICENSING.md`, neither of which was
        ever created, and nothing noticed because nothing followed the link.
        """
        blob = re.compile(
            r'= "https://github\.com/carlok/dratify/blob/main/([^"]+)"')
        targets = blob.findall(_read("pyproject.toml"))
        self.assertTrue(targets, "no in-repo file URLs to check")
        for rel in targets:
            with self.subTest(rel):
                self.assertTrue((ROOT / rel).exists(),
                                f"[project.urls] links {rel}, which does not "
                                f"exist in the repository")


if __name__ == "__main__":
    unittest.main()
