# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""A deletion cannot take away the clause a root literal rests on.

Both checkers accepted a refutation of a satisfiable formula. Take ``(1)`` and
``(-1 2)``, satisfied by making both variables true, and the proof::

    d -1 2 0
    -2 0
    0

Propagation puts 1 and then 2 on the root trail, with ``(-1 2)`` as the reason
for 2. The deletion removed that clause, and only the clause: the clause store
shrinks on deletion and the root assignment never does. So 2 stayed true with
nothing behind it. ``(-2)`` then passed as vacuously RAT, because no clause
contained 2 any more, was found false at the root, and set the root conflict,
and the ``0`` passed on that.

The rule that closes it: a deletion is ignored when the clause, as a set, is
unit under the root assignment, meaning exactly one literal true and all the
others false. Every reason clause has that shape for as long as the assignment
stands, so every root literal stays supported by a live clause. Ignoring a
deletion is always sound, since it only leaves more clauses to satisfy.

Found by the soundness campaign (root-1 and its duplicates, deletion-2).
"""

from __future__ import annotations

import itertools
import unittest

from dratify import CNF, check_proof, parse_dimacs, register_native
from dratify.lits import from_dimacs

try:
    from tests.test_root_units import _native
except ImportError:            # discover -s tests puts tests/ on the path
    from test_root_units import _native


def satisfiable(clauses, nvars):
    """By enumeration, so that this shares nothing with what it judges."""
    for bits in itertools.product((False, True), repeat=nvars):
        if all(any(bits[abs(l) - 1] == (l > 0) for l in c) for c in clauses):
            return True
    return False


class TestADeletedReason(unittest.TestCase):
    engine = "python"

    def check(self, formula, proof, **kw):
        return check_proof(parse_dimacs(formula), proof, engine=self.engine, **kw)

    def test_the_false_refutation_is_refused_where_it_starts(self):
        r = self.check("p cnf 2 2\n1 0\n-1 2 0\n", "d -1 2 0\n-2 0\n0\n")
        self.assertFalse(r.ok, "1 and 2 true satisfies this formula")
        self.assertFalse(r.reached_empty)
        self.assertEqual(r.failed_step, 2)
        self.assertEqual(r.failed_clause, (from_dimacs(-2),))
        self.assertEqual((r.deletions, r.ignored_deletions), (0, 1))

    def test_the_longer_forms_of_it(self):
        for name, formula, proof, failed, ignored in (
                ("two lemmas", "p cnf 3 2\n1 0\n-1 2 0\n",
                 "d -1 2 0\n-2 3 0\n-2 -3 0\n0\n", 2, 1),
                ("a chain", "p cnf 3 3\n1 0\n-1 2 0\n-2 3 0\n",
                 "d -1 2 0\nd -2 3 0\n-3 0\n0\n", 3, 2)):
            with self.subTest(name):
                r = self.check(formula, proof)
                self.assertFalse(r.ok, "every one of these is satisfiable")
                self.assertEqual(r.failed_step, failed)
                self.assertEqual((r.deletions, r.ignored_deletions),
                                 (0, ignored))

    def test_what_a_kept_reason_implies_is_still_usable(self):
        """Not a deleted clause's ghost: the clause is there, so this is RUP."""
        r = self.check("p cnf 3 3\n1 0\n-1 2 0\n-2 3 0\n", "d -1 2 0\n2 0\n")
        self.assertEqual(r.failed_step, -1, r.reason)
        self.assertEqual((r.rup_steps, r.rat_steps), (1, 0))
        self.assertEqual((r.deletions, r.ignored_deletions), (0, 1))

    def test_and_it_needs_no_rat_to_be_counted_honestly(self):
        """The clause that makes this step look unimplied is still present."""
        formula = ("p cnf 4 6\n1 0\n-1 2 0\n-2 3 4 0\n-2 3 -4 0\n"
                   "-2 -3 4 0\n-2 -3 -4 0\n")
        r = self.check(formula, "d -1 2 0\n2 0\n")
        self.assertEqual(r.failed_step, -1, r.reason)
        self.assertEqual(r.rup_steps, 1)
        self.assertEqual((r.deletions, r.ignored_deletions), (0, 1))

    def test_a_clause_is_a_set_here_too(self):
        formula = "p cnf 2 2\n1 0\n-1 2 0\n"
        for proof in ("d 2 -1 2 0\n-2 0\n0\n", "d -1 -1 2 0\n-2 0\n0\n"):
            with self.subTest(proof=proof):
                r = self.check(formula, proof)
                self.assertEqual(r.failed_step, 2)
                self.assertEqual((r.deletions, r.ignored_deletions), (0, 1))

    def test_the_rule_is_the_assignment_not_the_length(self):
        for name, formula, proof in (
                ("no literal assigned", "p cnf 2 1\n1 2 0\n", "d 1 2 0\n"),
                ("true and unassigned", "p cnf 2 2\n1 0\n1 2 0\n", "d 1 2 0\n"),
                ("two true", "p cnf 2 3\n1 0\n2 0\n1 2 0\n", "d 1 2 0\n"),
                ("false and unassigned", "p cnf 3 2\n1 0\n-1 2 3 0\n",
                 "d -1 2 3 0\n")):
            with self.subTest(name):
                r = self.check(formula, proof)
                self.assertEqual((r.deletions, r.ignored_deletions), (1, 0))
        r = self.check("p cnf 3 4\n1 0\n-3 0\n-1 2 0\n-1 -3 2 0\n",
                       "d -1 -3 2 0\n")
        self.assertEqual((r.deletions, r.ignored_deletions), (1, 0),
                         "2 and -3 are both true")
        r = self.check("p cnf 3 4\n1 0\n3 0\n-1 2 0\n-1 -3 2 0\n",
                       "d -1 -3 2 0\n")
        self.assertEqual((r.deletions, r.ignored_deletions), (0, 1),
                         "one true, two false: unit at the root, not a reason")

    def test_a_deleted_clause_that_is_not_a_reason_is_gone_for_rat(self):
        """The RAT candidates still shrink for every other deletion."""
        # (-1 2) blocks the RAT step (1) until it goes, and nothing is assigned
        formula = "p cnf 3 2\n-1 2 0\n-2 3 0\n"
        self.assertEqual(self.check(formula, "1 0\n").failed_step, 1)
        r = self.check(formula, "d -1 2 0\n1 0\n")
        self.assertEqual(r.failed_step, -1, r.reason)
        self.assertEqual((r.rat_steps, r.deletions), (1, 1))

    def test_apply_deletions_false_counts_what_it_always_counted(self):
        r = self.check("p cnf 2 2\n1 0\n-1 2 0\n", "d -1 2 0\n-2 0\n0\n",
                       apply_deletions=False)
        self.assertEqual(r.failed_step, 2)
        self.assertEqual((r.deletions, r.ignored_deletions), (0, 0))
        r = self.check("p cnf 2 2\n1 0\n-1 2 0\n", "d 1 0\n",
                       apply_deletions=False)
        self.assertEqual((r.deletions, r.ignored_deletions), (0, 1))

    def test_a_conflict_at_the_root_leaves_nothing_to_delete(self):
        """Past a conflict the assignment is whatever propagation had reached,
        which depends on watch order, so the rule must not read it: the two
        engines ordered their watches differently and would disagree."""
        square = "p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n"
        for proof in ("2 0\nd 1 -2 0\n0\n", "2 0\nd 1 2 0\n0\n",
                      "1 0\nd -1 -2 0\n0\n"):
            with self.subTest(proof=proof):
                r = self.check(square, proof)
                self.assertTrue(r.ok, r.reason)
                self.assertEqual((r.deletions, r.ignored_deletions), (0, 1))

    def test_no_refutation_of_a_satisfiable_formula(self):
        """Every formula of up to two clauses on two variables, and every proof
        of two additions or deletions from the same clauses and then ``0``."""
        pool = [(1,), (-1,), (2,), (-2,), (1, 2), (1, -2), (-1, 2), (-1, -2)]
        moves = [(kind, tuple(from_dimacs(l) for l in c))
                 for kind in "ad" for c in pool]
        formulas = [c for n in range(3)
                    for c in itertools.combinations(pool, n)]
        accepted = 0
        for clauses in formulas:
            f = CNF(2)
            for c in clauses:
                f.add_dimacs(c)
            sat = satisfiable(clauses, 2)
            for first, second in itertools.product(moves, repeat=2):
                r = check_proof(f, [first, second, ("a", ())], engine=self.engine)
                if r.ok:
                    accepted += 1
                    self.assertFalse(sat, f"{clauses} refuted by "
                                          f"{first}, {second}, 0")
        self.assertGreater(accepted, 0, "nothing here was ever refuted")


@unittest.skipIf(_native() is None,
                 "no native checker installed; CI installs cdclkit-native")
class TestADeletedReasonNative(TestADeletedReason):
    engine = "native"

    @classmethod
    def setUpClass(cls):
        register_native(_native())

    @classmethod
    def tearDownClass(cls):
        register_native(None)


if __name__ == "__main__":
    unittest.main()
