# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""A text proof is a stream of 0-terminated clauses; line breaks are whitespace.

The parser used to read a proof one line at a time, stop at the line's first
``0``, and ignore whatever followed it. Two consequences:

* **A step could hide from the checker.** In ``1 2 0 3 0`` only ``(1 2)`` was
  read, so an invalid ``(3)`` was never checked, and a proof containing it was
  reported as "every step verified". The verdict was still right -- the steps
  that were read refute the formula on their own -- but a forward checker's
  promise is to check every step the solver wrote.
* **A valid proof was rejected.** ``1 0 0`` lost its empty clause.

drat-trim reads proofs with ``fscanf(" %i ")``, to which a line break is just
whitespace: several clauses may share a line and one clause may span lines.
This parser now reads the same way, and raises on anything it cannot place in
a clause instead of skipping it.
"""

from __future__ import annotations

import unittest

from dratify import check_proof, parse_dimacs, parse_proof, register_native
from dratify.lits import from_dimacs

try:
    from tests.test_root_units import _native
except ImportError:            # discover -s tests puts tests/ on the path
    from test_root_units import _native

SQUARE = "p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n"

# SQUARE on 1, 2 plus (3 4) (-3 -4). Refuted by (1) and the empty clause;
# (3) is neither RUP nor RAT here.
WITH_BAD_THREE = ("p cnf 4 6\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n"
                  "3 4 0\n-3 -4 0\n")


def a(*dimacs):
    return ("a", tuple(from_dimacs(l) for l in dimacs))


def d(*dimacs):
    return ("d", tuple(from_dimacs(l) for l in dimacs))


class TestParsing(unittest.TestCase):
    def test_several_clauses_on_one_line(self):
        self.assertEqual(parse_proof("1 0 -2 3 0\n"), [a(1), a(-2, 3)])

    def test_a_deletion_after_an_addition_on_one_line(self):
        self.assertEqual(parse_proof("1 0 d 1 2 0\n"), [a(1), d(1, 2)])

    def test_the_kind_resets_after_each_clause(self):
        self.assertEqual(parse_proof("d 1 2 0 3 0\n"), [d(1, 2), a(3)])

    def test_the_empty_clause_on_the_same_line(self):
        self.assertEqual(parse_proof("1 0 0\n"), [a(1), a()])

    def test_a_clause_may_span_lines(self):
        self.assertEqual(parse_proof("1 2\n-3 0\n"), [a(1, 2, -3)])
        self.assertEqual(parse_proof("d\n1 2 0\n"), [d(1, 2)])

    def test_comment_lines_are_skipped_even_inside_a_clause(self):
        self.assertEqual(parse_proof("c x\n1\nc y\n2 0\n"), [a(1, 2)])

    def test_joining_lines_does_not_change_the_proof(self):
        text = "-1 2 0\nd 1 -2 3 0\n4 0\n0\n"
        self.assertEqual(parse_proof(text), parse_proof(text.replace("\n", " ")))

    def test_the_d_prefix_without_a_space_is_still_accepted(self):
        self.assertEqual(parse_proof("d1 2 0\n"), [d(1, 2)])


class TestNothingIsSkipped(unittest.TestCase):
    """Text that is not part of a clause raises; it used to be ignored."""

    def assertRefused(self, text, *fragments):
        with self.assertRaises(ValueError) as cm:
            parse_proof(text)
        for frag in fragments:
            self.assertIn(frag, str(cm.exception))

    def test_text_after_a_zero(self):
        self.assertRefused("1 0 junk\n", "line 1", "'junk'")
        self.assertRefused("1 0 c note\n", "line 1", "'c'")

    def test_a_clause_left_open_at_the_end(self):
        self.assertRefused("1 0\n2\n", "line 2", "not terminated")
        self.assertRefused("1 0\n\n3 4\n", "line 3", "not terminated")

    def test_a_dangling_d(self):
        self.assertRefused("1 0 d\n", "not terminated")
        self.assertRefused("d\n", "not terminated")

    def test_d_inside_a_clause(self):
        self.assertRefused("1 d 2 0\n", "line 1", "inside a clause")
        self.assertRefused("d d 1 0\n", "inside a clause")

    def test_a_bad_token_names_its_line(self):
        self.assertRefused("1 0\n2 0\n3 x 0\n", "line 3", "'x'")


class TestChecking(unittest.TestCase):
    engine = "python"

    def check(self, formula, proof):
        return check_proof(parse_dimacs(formula), proof, engine=self.engine)

    def test_a_step_after_a_zero_is_checked(self):
        """The case that mattered: the invalid (3) used to be skipped."""
        for proof in ("1 2 0\n3 0\n1 0\n0\n", "1 2 0 3 0\n1 0\n0\n",
                      "1 2 0 3 0 1 0 0\n"):
            with self.subTest(proof=proof):
                r = self.check(WITH_BAD_THREE, proof)
                self.assertFalse(r.ok)
                self.assertEqual(r.failed_step, 2)
                self.assertEqual(r.failed_clause, (from_dimacs(3),))

    def test_without_the_bad_step_the_same_proof_verifies(self):
        r = self.check(WITH_BAD_THREE, "1 2 0 1 0 0\n")
        self.assertTrue(r.ok, r.reason)
        self.assertEqual(r.steps, 3)

    def test_the_empty_clause_on_the_same_line_is_reached(self):
        for proof in ("1 0\n0\n", "1 0 0\n", "1\n0\n0\n"):
            with self.subTest(proof=proof):
                r = self.check(SQUARE, proof)
                self.assertTrue(r.ok, r.reason)
                self.assertEqual(r.steps, 2)

    def test_a_deletion_on_the_same_line_is_applied(self):
        r = self.check("p cnf 2 2\n1 2 0\n-1 2 0\n", "2 0 d 1 2 0\n")
        self.assertEqual((r.deletions, r.ignored_deletions), (1, 0))


@unittest.skipIf(_native() is None,
                 "no native checker installed; CI installs cdclkit-native")
class TestCheckingNative(TestChecking):
    engine = "native"

    @classmethod
    def setUpClass(cls):
        register_native(_native())

    @classmethod
    def tearDownClass(cls):
        register_native(None)


if __name__ == "__main__":
    unittest.main()
