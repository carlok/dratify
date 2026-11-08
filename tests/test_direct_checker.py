# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""`DRATChecker` is exported, so it has to validate what it is handed.

0.1.7 closed a soundness hole: a negative literal indexed Python's arrays from
the end, and `[("a", (-5,)), ("a", ())]` refuted a satisfiable formula. The
validation went into `check_proof`, so the same list through the exported class
still got ok=True, and so did the same mistake on `CNF.clauses` through
`check_proof` itself, while the native engine answered with a bare OverflowError.

Validation now lives in the checker, so no route reaches `val` or `_occ` with a
raw value, and `check_proof` looks at the formula before either engine runs.
"""

from __future__ import annotations

import unittest

from dratify import (CNF, DRATChecker, check_proof, parse_dimacs,
                     register_native)

try:
    from tests.test_root_units import _native
except ImportError:            # discover -s tests puts tests/ on the path
    from test_root_units import _native

SAT = "p cnf 3 2\n1 2 0\n-2 3 0\n"
ONE = "p cnf 1 1\n1 0\n"


class TestTheClassValidatesSteps(unittest.TestCase):
    def test_a_negative_literal_cannot_buy_a_refutation(self):
        for formula, steps in ((ONE, [("a", (-1,)), ("a", ())]),
                               (SAT, [("a", (-5,)), ("a", ())])):
            with self.subTest(steps=steps):
                c = DRATChecker(parse_dimacs(formula))
                with self.assertRaises(ValueError) as cm:
                    c.check(steps)
                self.assertIn("from_dimacs", str(cm.exception))
                self.assertFalse(c.result.ok)

    def test_nor_one_step_at_a_time(self):
        for kind in ("a", "d"):
            with self.subTest(kind=kind):
                c = DRATChecker(parse_dimacs(ONE))
                with self.assertRaises(ValueError) as cm:
                    c.check_step(kind, (-1,))
                self.assertIn("from_dimacs", str(cm.exception))

    def test_a_generator_of_steps_is_checked_too(self):
        with self.assertRaises(ValueError):
            DRATChecker(parse_dimacs(ONE)).check(
                s for s in [("a", (-1,)), ("a", ())])

    def test_an_unknown_kind_is_not_an_addition(self):
        with self.assertRaises(ValueError) as cm:
            DRATChecker(parse_dimacs("p cnf 2 1\n1 2 0\n")).check_step("x", (0, 2))
        self.assertIn("'x'", str(cm.exception))

    def test_what_is_not_an_integer_is_refused(self):
        for lit in (1.0, "1", True, None):
            with self.subTest(lit=lit), self.assertRaises(ValueError):
                DRATChecker(parse_dimacs(ONE)).check_step("a", (lit,))

    def test_well_formed_steps_still_work(self):
        c = DRATChecker(parse_dimacs("p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n"))
        self.assertTrue(c.check_step("a", (0,)))
        self.assertTrue(c.check_step("a", ()))
        self.assertTrue(c.result.reached_empty)

    def test_a_fresh_variable_still_grows_the_arrays(self):
        c = DRATChecker(parse_dimacs(ONE))
        self.assertTrue(c.check_step("a", (10,)))


class TestTheClassValidatesTheFormula(unittest.TestCase):
    def test_a_negative_literal_on_the_clauses(self):
        f = CNF(3)
        f.clauses = [(-1,), (-2,), (3,)]
        with self.assertRaises(ValueError) as cm:
            DRATChecker(f)
        self.assertIn("from_dimacs", str(cm.exception))

    def test_something_else_on_the_clauses(self):
        for bad in (1.0, "1", True):
            with self.subTest(bad=bad):
                f = CNF(3)
                f.clauses = [(bad,)]
                with self.assertRaises(ValueError):
                    DRATChecker(f)


class TestCheckProofValidatesTheFormula(unittest.TestCase):
    engine = "python"

    def check(self, f, proof="0\n"):
        return check_proof(f, proof, engine=self.engine)

    def test_a_negative_literal_is_a_value_error(self):
        f = CNF(3)
        f.clauses = [(-1,), (-2,), (3,)]
        with self.assertRaises(ValueError) as cm:
            self.check(f)
        self.assertIn("from_dimacs", str(cm.exception))
        self.assertIn("clause 1", str(cm.exception))

    def test_a_literal_past_what_either_engine_can_hold(self):
        f = CNF(1)
        f.clauses = [(1 << 33,)]
        with self.assertRaises(ValueError):
            self.check(f)

    def test_a_step_past_what_either_engine_can_hold(self):
        f = CNF(1 << 40)
        with self.assertRaises(ValueError):
            self.check(f, [("a", (1 << 33,))])

    def test_a_repeat_on_the_clauses_is_the_same_clause(self):
        """`CNF.add` drops repeats, so only a direct write can get here."""
        f = CNF(1)
        f.clauses = [(0, 0), (1, 1)]
        r = self.check(f)
        self.assertTrue(r.ok, r.reason)
        self.assertIn("unit propagation alone", r.reason)

    def test_a_variable_count_past_u32_is_one_answer(self):
        """The checkers size by the variables used, not by this count."""
        f = CNF(1 << 32)
        f.add_dimacs([1])
        r = self.check(f, "")
        self.assertFalse(r.ok)
        self.assertEqual(r.steps, 0)
        self.assertIn("never derives the empty clause", r.reason)


@unittest.skipIf(_native() is None,
                 "no native checker installed; CI installs cdclkit-native")
class TestCheckProofValidatesTheFormulaNative(TestCheckProofValidatesTheFormula):
    engine = "native"

    @classmethod
    def setUpClass(cls):
        register_native(_native())

    @classmethod
    def tearDownClass(cls):
        register_native(None)


if __name__ == "__main__":
    unittest.main()
