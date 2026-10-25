# SPDX-License-Identifier: Apache-2.0
"""A tautology in the file still counts towards the header's clause count."""

from __future__ import annotations

import unittest

from dratify import parse_dimacs

TEXT = "p cnf 2 2\n1 -1 0\n1 2 0\n"


class TestTautologyHeaderCount(unittest.TestCase):
    def test_strict_accepts_tautology(self):
        f = parse_dimacs(TEXT, strict=True)
        self.assertEqual(len(f.clauses), 1)
        self.assertIsNone(f.header_mismatch)

    def test_lenient_no_mismatch(self):
        self.assertIsNone(parse_dimacs(TEXT).header_mismatch)

    def test_unterminated_tautology_counts(self):
        f = parse_dimacs("p cnf 2 2\n1 2 0\n1 -1\n")
        self.assertIsNone(f.header_mismatch)

    def test_real_mismatch_still_reported(self):
        f = parse_dimacs("p cnf 2 3\n1 -1 0\n1 2 0\n")
        self.assertEqual(f.header_mismatch, (3, 2))
        with self.assertRaises(ValueError):
            parse_dimacs("p cnf 2 3\n1 -1 0\n1 2 0\n", strict=True)


if __name__ == "__main__":
    unittest.main()
