# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Once the clause set is refuted at the root, the question is settled.

Unit propagation at the root reaching a conflict is a refutation of the clauses
present, and nothing after it is looked at very hard: later deletions cannot
undo it and every later addition passes. So after ``1 0`` on the square, ``d -1
-2 0`` and then ``0`` is accepted, though ``0`` would not be RUP on what remains.

That is sound. Every step up to the conflict preserved satisfiability and a
deletion can only weaken a formula, so a satisfiable input cannot get there.
drat-trim's operational reading agrees: the proof is over at that point. It is
pinned here because it is a real exception to "checked against the clauses
present", and the same goes for an input propagation refutes on its own.
"""

from __future__ import annotations

import unittest

from dratify import check_proof, parse_dimacs, register_native

try:
    from tests.test_root_units import _native
except ImportError:            # discover -s tests puts tests/ on the path
    from test_root_units import _native

SQUARE = "p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n"
REFUTED = "p cnf 2 2\n1 0\n-1 0\n"


class TestARefutationIsFinal(unittest.TestCase):
    engine = "python"

    def check(self, formula, proof):
        return check_proof(parse_dimacs(formula), proof, engine=self.engine)

    def test_a_deletion_does_not_undo_it(self):
        for proof in ("1 0\nd -1 -2 0\n0\n", "1 0\nd -1 2 0\n0\n",
                      "1 0\nd 1 2 0\nd 1 -2 0\nd -1 2 0\nd -1 -2 0\n0\n"):
            with self.subTest(proof=proof):
                r = self.check(SQUARE, proof)
                self.assertTrue(r.ok, r.reason)
                self.assertTrue(r.reached_empty)
                self.assertEqual(r.rup_steps, 2)
                self.assertEqual(r.deletions, 0, "none of them was applied")
                self.assertEqual(r.ignored_deletions, proof.count("d"))

    def test_every_later_addition_passes(self):
        r = self.check(SQUARE, "1 0\n-1 0\n7 8 0\n0\n")
        self.assertTrue(r.ok, r.reason)
        self.assertEqual((r.rup_steps, r.rat_steps), (4, 0))

    def test_it_still_takes_an_empty_clause_in_the_proof(self):
        """A conflict from the proof's own steps does not stand in for its `0`."""
        r = self.check(SQUARE, "1 0\n")
        self.assertFalse(r.ok)
        self.assertFalse(r.reached_empty)

    def test_an_input_propagation_refutes_needs_no_proof_at_all(self):
        """The one way reached_empty is True with no empty clause derived."""
        for proof in ("", "2 0\n", "d 1 0\n"):
            with self.subTest(proof=proof):
                r = self.check(REFUTED, proof)
                self.assertTrue(r.ok)
                self.assertTrue(r.reached_empty)
                self.assertEqual(r.steps, 0)
                self.assertIn("unit propagation alone", r.reason)

    def test_text_that_cannot_be_parsed_still_raises_first(self):
        with self.assertRaises(ValueError):
            self.check(REFUTED, "x 0\n")


@unittest.skipIf(_native() is None,
                 "no native checker installed; CI installs cdclkit-native")
class TestARefutationIsFinalNative(TestARefutationIsFinal):
    engine = "native"

    @classmethod
    def setUpClass(cls):
        register_native(_native())

    @classmethod
    def tearDownClass(cls):
        register_native(None)


if __name__ == "__main__":
    unittest.main()
