# SPDX-License-Identifier: Apache-2.0
"""A literal in a clause body must be bounded like the header's count."""

from __future__ import annotations

import unittest

from dratify import (DRATChecker, MemoryProof, check_proof, from_dimacs,
                     parse_dimacs, parse_proof, register_native)
from dratify.cnf import HEADER_VARS_FLOOR
from dratify.proof import _MAX_VARS, _literal_limit

try:
    from tests.test_root_units import _native
except ImportError:            # discover -s tests puts tests/ on the path
    from test_root_units import _native


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


class TestAProofLiteralBound(unittest.TestCase):
    """A hostile literal must be refused, and nothing else may decide that.

    The bound was the formula's count plus the larger of the literal occurrences
    and the text's length, on the argument that a proof can only introduce the
    variables it mentions. That counts how many it can introduce and not what they
    may be numbered: `50 0` is vacuously RAT, and nothing obliges a proof to use 3
    to 49. So `7 0` raised, and raised no more once a comment made the text longer,
    and a list of steps got a tighter bound than the same proof as text.
    """

    engine = "python"
    SQUARE = "p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n"

    def check(self, formula, proof):
        return check_proof(parse_dimacs(formula), proof, engine=self.engine)

    def test_a_fresh_variable_may_leave_a_gap(self):
        for var in (3, 50, 99, 1000):
            with self.subTest(var=var):
                r = self.check(self.SQUARE, f"{var} 0\n1 0\n0\n")
                self.assertTrue(r.ok, r.reason)
                self.assertEqual(r.rat_steps, 1)

    def test_the_shape_of_the_proof_does_not_decide_it(self):
        memory = MemoryProof()
        memory.add((from_dimacs(5),))
        for proof in ("5 0\n", "5 0", [("a", (from_dimacs(5),))], memory,
                      memory.to_text(), parse_proof("5 0\n")):
            with self.subTest(proof=proof):
                r = self.check("p cnf 2 1\n1 2 0\n", proof)
                self.assertEqual((r.rat_steps, r.failed_step), (1, -1))

    def test_nor_does_a_comment_or_padding(self):
        for proof in ("7 0\n", "c pad pad pad\n7 0\n", "7 0\n" + " " * 5000,
                      "5000 0\n", "c " + "x" * 5000 + "\n5000 0\n"):
            with self.subTest(proof=proof[:12]):
                r = self.check("p cnf 2 1\n1 2 0\n", proof)
                self.assertEqual((r.rat_steps, r.failed_step), (1, -1))

    def test_the_guard_does_not_read_the_layout_either(self):
        var = 2 + HEADER_VARS_FLOOR + 1
        for proof in (f"{var} 0\n", "c " + "x" * (2 * var) + f"\n{var} 0\n",
                      [("a", (from_dimacs(var),))]):
            with self.subTest(proof=str(proof)[:12]):
                with self.assertRaises(ValueError) as cm:
                    self.check("p cnf 2 1\n1 2 0\n", proof)
                self.assertIn(str(var), str(cm.exception))

    def test_the_rule(self):
        self.assertEqual(_literal_limit(2, 0), 2 + HEADER_VARS_FLOOR)
        self.assertEqual(_literal_limit(5_000_000, 3), 5_000_000 + HEADER_VARS_FLOOR)
        many = HEADER_VARS_FLOOR * 3
        self.assertEqual(_literal_limit(2, many), 2 + many,
                         "every proof the occurrence bound accepted is still fine")
        self.assertEqual(_literal_limit(1 << 40, 0), _MAX_VARS)


@unittest.skipIf(_native() is None,
                 "no native checker installed; CI installs cdclkit-native")
class TestAProofLiteralBoundNative(TestAProofLiteralBound):
    engine = "native"

    @classmethod
    def setUpClass(cls):
        register_native(_native())

    @classmethod
    def tearDownClass(cls):
        register_native(None)


class TestTheBoundOnTheClass(unittest.TestCase):
    """`DRATChecker` used directly sizes its arrays from a literal just the same."""

    def test_a_huge_literal_is_refused_one_step_at_a_time(self):
        c = DRATChecker(parse_dimacs("p cnf 1 1\n1 0\n"))
        with self.assertRaises(ValueError):
            c.check_step("a", (2 * 10 ** 11,))
        with self.assertRaises(ValueError):
            c.check([("a", (2 * 10 ** 11,))])

    def test_a_fresh_variable_with_a_gap_is_not(self):
        c = DRATChecker(parse_dimacs("p cnf 1 1\n1 0\n"))
        self.assertTrue(c.check_step("a", (from_dimacs(5000),)))


if __name__ == "__main__":
    unittest.main()
