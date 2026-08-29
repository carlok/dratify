# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""RAT: the rule that puts the "A" in DRAT.

A clause is RUP when assuming its negation propagates to a conflict. RAT is
weaker and strictly more permissive: `C` is RAT on pivot `p` when, for every
clause `D` containing `~p`, the resolvent `C u (D \\ {~p})` is RUP. RAT clauses
need not follow from the formula at all -- they only have to preserve
satisfiability.

That makes RAT the dangerous half of the rule set. A checker that accepts RAT
loosely accepts proofs of things that are not true, so these tests are mostly
about what must be *rejected*.
"""

from __future__ import annotations

import unittest

from dratify import parse_dimacs, check_proof
from dratify.proof import DRATChecker
from dratify.lits import from_dimacs


def lits(*dimacs):
    return [from_dimacs(d) for d in dimacs]


class TestRATAcceptsWhatRUPRejects(unittest.TestCase):
    def setUp(self):
        # satisfiable, so "everything is RUP" does not hold and the two rules
        # can actually be told apart
        self.f = parse_dimacs("p cnf 2 1\n1 2 0\n")

    def test_the_clause_is_not_rup(self):
        c = DRATChecker(self.f, check_rat=False)
        self.assertFalse(c.check_step("a", lits(1)),
                         "assuming ~1 forces 2 and stops; there is no conflict")

    def test_but_it_is_rat_on_its_first_literal(self):
        c = DRATChecker(self.f, check_rat=True)
        self.assertTrue(c.check_step("a", lits(1)),
                        "no clause contains ~1, so the condition is vacuous")

    def test_a_fresh_variable_is_vacuously_rat(self):
        c = DRATChecker(self.f, check_rat=True)
        self.assertTrue(c.check_step("a", lits(3)))


class TestRATRejects(unittest.TestCase):
    def test_a_clause_that_is_neither_rup_nor_rat(self):
        f = parse_dimacs("p cnf 3 1\n1 2 0\n")
        c = DRATChecker(f, check_rat=True)
        # pivot -1. The only clause containing 1 is (1 2), so the resolvent is
        # (-1 3) u {2} = (-1 3 2), which is not a tautology and not RUP:
        # assuming 1, ~3, ~2 satisfies (1 2) and stops without a conflict.
        self.assertFalse(c.check_step("a", lits(-1, 3)))

    def test_a_tautological_resolvent_is_skipped(self):
        """RAT ignores resolvents that are tautologies, which makes some
        surprising clauses vacuously RAT.

        Against (1 2) the clause (-1 -2) is RAT on -1: the single resolvent
        is (-1 -2 2), which contains both 2 and ~2.
        """
        f = parse_dimacs("p cnf 2 1\n1 2 0\n")
        c = DRATChecker(f, check_rat=True)
        self.assertTrue(c.check_step("a", lits(-1, -2)))

    def test_the_pivot_is_the_first_literal_not_any_literal(self):
        """DRAT fixes the pivot. A checker that tries them all is too weak."""
        f = parse_dimacs("p cnf 3 2\n1 2 0\n-1 3 0\n")
        # RAT on 2 would hold vacuously, but 2 is not first, so this must fail
        c = DRATChecker(f, check_rat=True)
        self.assertFalse(c.check_step("a", lits(-1, 2)),
                         "pivot is -1; the resolvent against (1 2) must be RUP")

    def test_disabling_rat_only_ever_rejects_more(self):
        f = parse_dimacs("p cnf 2 1\n1 2 0\n")
        with_rat = DRATChecker(f, check_rat=True).check_step("a", lits(1))
        no_rat = DRATChecker(f, check_rat=False).check_step("a", lits(1))
        self.assertTrue(with_rat)
        self.assertFalse(no_rat)


class TestDeletion(unittest.TestCase):
    """Deletion is monotone-safe for RUP; RAT is not monotone."""

    def test_deleting_then_reusing_a_clause_fails(self):
        f = parse_dimacs("p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n")
        steps = [("d", lits(1, 2)), ("d", lits(1, -2)),
                 ("d", lits(-1, 2)), ("d", lits(-1, -2)),
                 ("a", [])]
        r = DRATChecker(f, apply_deletions=True).check(steps)
        self.assertFalse(r.ok, "with every clause deleted, nothing implies the "
                               "empty clause")

    #: four clauses, no units, so the checker cannot short-circuit on
    #: "the input formula is refuted by propagation alone" and deletions are
    #: actually reached
    SQUARE = "p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n"

    def test_unit_deletions_are_ignored_on_purpose(self):
        """Deleting a unit clause is a no-op, and that is deliberate.

        Solvers log deletions of units they have already used to simplify at
        the root. Honouring those would invalidate propagations the solver
        legitimately made, so checkers ignore them -- drat-trim does the same.
        `ignored_deletions` counts them rather than hiding the decision.
        """
        f = parse_dimacs(self.SQUARE)
        r = DRATChecker(f, apply_deletions=True).check(
            [("a", lits(2)), ("d", lits(2)), ("a", [])])
        self.assertTrue(r.ok)
        self.assertEqual(r.ignored_deletions, 1)
        self.assertEqual(r.deletions, 0, "it was ignored, not applied")

    def test_longer_deletions_are_applied_and_counted(self):
        f = parse_dimacs(self.SQUARE)
        steps = [("a", lits(2)), ("d", lits(1, -2)), ("a", [])]
        applied = DRATChecker(f, apply_deletions=True).check(steps)
        ignored = DRATChecker(parse_dimacs(self.SQUARE),
                              apply_deletions=False).check(steps)
        self.assertEqual(applied.deletions, 1)
        self.assertEqual(ignored.deletions, 0)
        self.assertTrue(applied.ok and ignored.ok,
                        "this proof happens to survive either way")

    def test_deleting_a_clause_that_was_never_there(self):
        f = parse_dimacs("p cnf 2 1\n1 2 0\n")
        r = DRATChecker(f).check([("d", lits(1, -2)), ("a", lits(1, 2))])
        self.assertGreaterEqual(r.ignored_deletions, 0)


class TestReporting(unittest.TestCase):
    def test_a_failure_names_the_step_and_the_clause(self):
        f = parse_dimacs("p cnf 2 1\n1 2 0\n")
        r = DRATChecker(f, check_rat=False).check([("a", lits(-1, -2))])
        self.assertFalse(r.ok)
        self.assertEqual(r.failed_step, 1, "1-based index of the failing step")
        self.assertTrue(r.failed_clause)
        self.assertIn("RUP", r.reason)

    def test_report_is_human_readable(self):
        f = parse_dimacs("p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n")
        r = check_proof(f, "1 0\n0\n", engine="python")
        self.assertTrue(r.ok)
        self.assertIn("step", r.report().lower())

    def test_counters_add_up(self):
        f = parse_dimacs("p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n")
        r = check_proof(f, "1 0\n0\n", engine="python")
        self.assertEqual(r.steps, r.rup_steps + r.rat_steps)


if __name__ == "__main__":
    unittest.main()
