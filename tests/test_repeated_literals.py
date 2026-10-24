# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""A proof step that repeats a literal is the same clause without the repeat.

A clause is a set, so `1 1 0` is the clause (1). Both checkers counted
occurrences instead, with two consequences:

* **A valid proof was rejected.** A lemma whose only non-false literal was
  written twice looked like it had two free literals, so it never became unit
  at the root. A later step that needed that implication failed: `1 0` then
  `0` was accepted, and `1 1 0` then `0` was not.
* **A unit could be deleted.** Unit deletions are ignored, the way every
  mainstream checker ignores them, but the rule tested the step's length, so
  `d 1 1 0` got past it and removed the unit `1 0`.

Formulas were never affected: `CNF.add` already drops repeated literals. Both
implementations shared the mistake, so comparing them could not find it, and
neither could `tests/naive.py`, which made the same one. The naive reference
now treats clauses as sets, and the property tests generate repeated literals.
"""

from __future__ import annotations

import unittest

from dratify import check_proof, parse_dimacs, register_native

try:
    from tests.test_root_units import _native
except ImportError:            # discover -s tests puts tests/ on the path
    from test_root_units import _native

# Refuted by (1) and then the empty clause; nothing shorter works.
NEEDS_UNIT_ONE = "p cnf 3 4\n1 2 0\n1 -2 0\n-1 3 0\n-1 -3 0\n"


class TestRepeatedLiterals(unittest.TestCase):
    engine = "python"

    def check(self, formula, proof, **kw):
        return check_proof(parse_dimacs(formula), proof, engine=self.engine, **kw)

    def test_a_repeated_literal_is_the_same_lemma(self):
        for lemma in ("1", "1 1", "1 1 1"):
            with self.subTest(lemma=lemma):
                r = self.check(NEEDS_UNIT_ONE, f"{lemma} 0\n0\n")
                self.assertTrue(r.ok, r.reason)
                self.assertEqual(r.rup_steps, 2)

    def test_a_repeated_literal_among_root_false_ones(self):
        # -1 is false once (1) is in; (-1 3 3) is then unit and gives 3
        formula = "p cnf 3 4\n1 2 0\n1 -2 0\n-1 3 0\n-3 -1 0\n"
        r = self.check(formula, "1 0\n-1 3 3 0\n0\n")
        self.assertTrue(r.ok, r.reason)

    def test_a_repeated_false_literal_is_still_rejected(self):
        """Removing repeats must not make a non-RUP lemma pass."""
        # against (1 2), (-1) is neither RUP nor RAT however it is written
        for lemma in ("-1", "-1 -1"):
            with self.subTest(lemma=lemma):
                r = self.check("p cnf 2 1\n1 2 0\n", f"{lemma} 0\n0\n")
                self.assertFalse(r.ok)
                self.assertEqual(r.failed_step, 1)

    def test_a_repeated_literal_does_not_make_a_unit_deletable(self):
        formula = "p cnf 2 2\n1 0\n-1 2 0\n"
        for proof in ("d 1 0\n", "d 1 1 0\n"):
            with self.subTest(proof=proof):
                r = self.check(formula, proof)
                self.assertEqual((r.deletions, r.ignored_deletions), (0, 1))

    def test_a_clause_deleted_with_a_repeat_is_deleted(self):
        formula = "p cnf 2 2\n1 2 0\n-1 2 0\n"
        r = self.check(formula, "d 2 1 2 0\n")
        self.assertEqual((r.deletions, r.ignored_deletions), (1, 0))

    def test_the_rat_pivot_is_the_first_literal_still(self):
        # F = { -1 2, 2 3 }: (1 -2) is not RUP. It is RAT on 1 (the only
        # resolvent is a tautology) but not on -2 (the resolvent with (2 3) is
        # (1 -2 3), which is not RUP). So the pivot decides the answer, and it
        # must stay the step's first literal when repeats are removed.
        formula = "p cnf 3 2\n-1 2 0\n2 3 0\n"
        r = self.check(formula, "1 1 -2 0\n")
        self.assertEqual(r.failed_step, -1, r.reason)
        self.assertEqual(r.rat_steps, 1)
        r = self.check(formula, "-2 1 -2 0\n")
        self.assertEqual(r.failed_step, 1, "pivot -2 must not be RAT")


@unittest.skipIf(_native() is None,
                 "no native checker installed; CI installs cdclkit-native")
class TestRepeatedLiteralsNative(TestRepeatedLiterals):
    engine = "native"

    @classmethod
    def setUpClass(cls):
        register_native(_native())

    @classmethod
    def tearDownClass(cls):
        register_native(None)


if __name__ == "__main__":
    unittest.main()
