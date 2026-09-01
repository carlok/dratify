# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""The claim this package is sold on, with a test behind it.

README, SECURITY.md and both Rust docs say the two implementations are
"differentially tested against each other, on acceptances *and* on rejections".
That was true of how the code was developed and false of what ran here: the
only two tests that compared them were `skipUnless(native_available())`, which
is evaluated at import time before anything can register a checker, and a
`skipTest` on ImportError. Both skipped on every CI run, so the Rust `Checker`
was never once compared against `DRATChecker` in this repository.

This module does the comparison. CI installs `cdclkit-native`, which embeds the
crate, and registers it explicitly rather than relying on an import side
effect. When it is genuinely absent the whole module skips -- but it says so,
and the CI job that must not skip is named after this file.

Agreement on *rejections* is the half that matters. A checker that accepts
everything passes any suite built only from valid proofs.
"""

from __future__ import annotations

import pathlib
import random
import unittest

from dratify import (check_proof, parse_dimacs, register_native,
                     native_implementation)

HERE = pathlib.Path(__file__).parent

SQUARE = "p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n"


def _native():
    """The Rust checker, or None. Registered explicitly, not by side effect."""
    try:
        import cdclkit_native as impl
    except ImportError:
        return None
    return impl


@unittest.skipIf(_native() is None,
                 "no native checker installed; CI installs cdclkit-native")
class TestBothCheckersAgree(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        register_native(_native())
        assert native_implementation() is not None

    @classmethod
    def tearDownClass(cls):
        register_native(None)

    def _agree(self, formula_text, proof_text, label=""):
        """Both engines, every field that describes the verdict."""
        f = parse_dimacs(formula_text)
        py = check_proof(f, proof_text, engine="python")
        rs = check_proof(f, proof_text, engine="native")
        self.assertIs(py.ok, rs.ok, f"{label}: verdicts differ")
        self.assertIs(py.reached_empty, rs.reached_empty,
                      f"{label}: reached_empty differs")
        self.assertEqual(py.reason, rs.reason, f"{label}: reasons differ")
        if py.ok:
            self.assertEqual(py.rup_steps, rs.rup_steps, f"{label}: rup_steps")
            self.assertEqual(py.rat_steps, rs.rat_steps, f"{label}: rat_steps")
        return py

    # -- acceptances -----------------------------------------------------

    def test_a_hand_checked_refutation(self):
        self.assertTrue(self._agree(SQUARE, "1 0\n0\n", "square").ok)

    def test_a_real_solver_proof(self):
        self.assertTrue(self._agree((HERE / "php32.cnf").read_text(),
                                    (HERE / "php32.drat").read_text(),
                                    "php(3,2)").ok)

    def test_a_formula_already_containing_the_empty_clause(self):
        self._agree("p cnf 1 1\n0\n", "0\n", "empty in input")

    def test_contradictory_units(self):
        self._agree("p cnf 1 2\n1 0\n-1 0\n", "0\n", "units")

    # -- rejections, which is the half that matters ----------------------

    def test_a_truncated_proof(self):
        r = self._agree(SQUARE, "1 0\n", "truncated")
        self.assertFalse(r.ok)
        self.assertIn("empty clause", r.reason)

    def test_a_refutation_of_a_satisfiable_formula(self):
        r = self._agree("p cnf 1 1\n1 0\n", "0\n", "bogus")
        self.assertFalse(r.ok)

    def test_an_unjustified_clause(self):
        r = self._agree("p cnf 2 1\n1 0\n", "2 0\n0\n", "unjustified")
        self.assertFalse(r.ok)

    def test_a_flipped_literal(self):
        r = self._agree(SQUARE, "-1 0\n0\n", "flipped")
        self.assertIsNotNone(r)

    # -- and a sweep, so this is not four hand-picked cases --------------

    def test_random_formulas_and_random_candidate_steps(self):
        """Small random formulas with random proof steps.

        Most of these are rejections, which is the point: a disagreement is
        far likelier on a clause one engine thinks is RUP and the other does
        not than on a proof someone wrote by hand.
        """
        rng = random.Random(20260901)
        agreed = rejected = 0
        for _ in range(150):
            n = rng.randint(1, 4)
            clauses = []
            for _ in range(rng.randint(1, 3 * n)):
                k = rng.randint(1, min(3, n))
                vs = rng.sample(range(1, n + 1), k)
                clauses.append([v if rng.random() < 0.5 else -v for v in vs])
            text = f"p cnf {n} {len(clauses)}\n" + "".join(
                " ".join(map(str, c)) + " 0\n" for c in clauses)

            steps = []
            for _ in range(rng.randint(1, 3)):
                k = rng.randint(0, min(2, n))
                vs = rng.sample(range(1, n + 1), k) if k else []
                steps.append(" ".join(
                    str(v if rng.random() < 0.5 else -v) for v in vs) + " 0")
            proof = "\n".join(steps) + "\n"

            r = self._agree(text, proof, f"random {text!r} {proof!r}")
            agreed += 1
            rejected += (not r.ok)
        self.assertEqual(agreed, 150)
        self.assertGreater(rejected, 20,
                           "the sweep never exercised rejection, so agreement "
                           "on rejections was not actually tested")

    def test_rat_is_compared_too(self):
        """RAT is the rule that accepts clauses the formula does not entail,
        so it is where a permissive checker would differ."""
        r = self._agree("p cnf 3 1\n1 2 0\n", "1 0\n0\n", "rat")
        self.assertIsNotNone(r)


if __name__ == "__main__":
    unittest.main()
