# SPDX-License-Identifier: Apache-2.0
"""A literal in a clause body must be bounded like the header's count."""

from __future__ import annotations

import unittest

from dratify import parse_dimacs
from dratify.cnf import HEADER_VARS_FLOOR


class TestLiteralBound(unittest.TestCase):
    def test_huge_literal_is_rejected(self):
        with self.assertRaises(ValueError):
            parse_dimacs("1 4000000000 0\n")

    def test_huge_negative_literal_is_rejected(self):
        with self.assertRaises(ValueError):
            parse_dimacs("-%d 0\n" % (HEADER_VARS_FLOOR + 1))

    def test_literal_just_above_floor_is_rejected_in_short_file(self):
        with self.assertRaises(ValueError):
            parse_dimacs("1 3000000 0\n")

    def test_ordinary_literals_still_parse(self):
        f = parse_dimacs("p cnf 1000 2\n1 -1000 0\n2 0\n")
        self.assertEqual(f.nvars, 1000)
        self.assertEqual(len(f.clauses), 2)

    def test_literal_at_floor_is_accepted(self):
        f = parse_dimacs("1 %d 0\n" % HEADER_VARS_FLOOR)
        self.assertEqual(f.nvars, HEADER_VARS_FLOOR)


if __name__ == "__main__":
    unittest.main()
