# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Community and security policy files stay present and consistent."""

from __future__ import annotations

import pathlib
import unittest

ROOT = pathlib.Path(__file__).resolve().parent.parent

ADVISORY_URL = "https://github.com/carlok/dratify/security/advisories/new"

REQUIRED_PATHS = [
    "CODE_OF_CONDUCT.md",
    "CONTRIBUTING.md",
    "LICENSE",
    "README.md",
    "SECURITY.md",
    ".github/dependabot.yml",
    ".github/workflows/ci.yml",
    ".github/ISSUE_TEMPLATE/config.yml",
    ".github/ISSUE_TEMPLATE/bug_report.yml",
    ".github/ISSUE_TEMPLATE/feature_request.yml",
    ".github/PULL_REQUEST_TEMPLATE.md",
]


class TestCommunityFiles(unittest.TestCase):
    def test_required_files_exist(self):
        missing = [p for p in REQUIRED_PATHS if not (ROOT / p).is_file()]
        self.assertEqual(missing, [], f"missing community files: {missing}")

    def test_security_md_points_to_private_advisory_reporting(self):
        text = (ROOT / "SECURITY.md").read_text(encoding="utf-8")
        self.assertIn(ADVISORY_URL, text)


if __name__ == "__main__":
    unittest.main()