# SPDX-License-Identifier: Apache-2.0
"""What a proof checker has to get right, in both directions.

A checker that never rejects passes every positive test, so the negative cases
below carry most of the weight: a truncated proof, and a "refutation" of a
formula that is actually satisfiable.
"""

from __future__ import annotations

import pathlib
import unittest

from dratify import (CNF, check_proof, native_available, parse_dimacs,
                     register_native)

HERE = pathlib.Path(__file__).parent

# (a v b) (a v ~b) (~a v b) (~a v ~b) -- unsatisfiable, and small enough to
# verify the proof below by hand.
SQUARE = "p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n"
# "1 0" is RUP: assume ~a, then (~a v b) forces b and (~a v ~b) forces ~b.
# "0" is then RUP: unit a, and (~a v b) / (~a v ~b) conflict.
SQUARE_PROOF = "1 0\n0\n"


class TestAcceptsHonestProofs(unittest.TestCase):
    def test_hand_checked_proof(self):
        self.assertTrue(check_proof(parse_dimacs(SQUARE), SQUARE_PROOF).ok)

    def test_real_solver_proof(self):
        f = parse_dimacs((HERE / "php32.cnf").read_text())
        proof = (HERE / "php32.drat").read_text()
        self.assertTrue(check_proof(f, proof).ok)


class TestRejectsDishonestProofs(unittest.TestCase):
    """The half that matters. A checker that always says yes is worthless."""

    def test_truncated_proof_is_rejected(self):
        # every step is valid; the empty clause is simply never reached
        r = check_proof(parse_dimacs(SQUARE), "1 0\n")
        self.assertFalse(r.ok)
        self.assertIn("empty clause", r.reason)

    def test_refutation_of_a_satisfiable_formula_is_rejected(self):
        # "a" alone is satisfiable, so no proof of the empty clause can exist
        r = check_proof(parse_dimacs("p cnf 1 1\n1 0\n"), "0\n")
        self.assertFalse(r.ok)

    def test_unjustified_clause_is_rejected(self):
        # "2 0" is neither RUP nor RAT here
        r = check_proof(parse_dimacs("p cnf 2 1\n1 0\n"), "2 0\n0\n")
        self.assertFalse(r.ok)


class TestEngines(unittest.TestCase):
    def test_unknown_engine_raises(self):
        with self.assertRaises(ValueError):
            check_proof(parse_dimacs(SQUARE), SQUARE_PROOF, engine="banana")

    def test_python_engine_always_works(self):
        self.assertTrue(
            check_proof(parse_dimacs(SQUARE), SQUARE_PROOF, engine="python").ok)

    # The engine-agreement tests used to live here behind
    # `skipUnless(native_available())`, which is evaluated at import time --
    # before anything can register a checker -- so they never ran. They are now
    # tests/test_differential.py, which registers explicitly and which CI
    # installs a native checker for.

    def test_native_requested_but_absent_explains_itself(self):
        if native_available():
            self.skipTest("native is installed")
        with self.assertRaises(RuntimeError) as cm:
            check_proof(parse_dimacs(SQUARE), SQUARE_PROOF, engine="native")
        self.assertIn("engine=", str(cm.exception))


class TestNativeRegistration(unittest.TestCase):
    """A second implementation can be offered from outside this package.

    This package does not ship Python bindings for its Rust checker yet.
    Something that already embeds the same crate can hand one over, rather than
    letting `engine="auto"` silently fall back to the pure-Python checker --
    which is correct, but ~18x slower on large proofs.
    """

    def tearDown(self):
        register_native(None)

    def test_a_module_without_check_proof_is_refused(self):
        class NotAChecker:
            pass
        with self.assertRaises(TypeError):
            register_native(NotAChecker())

    def test_registering_none_unregisters(self):
        register_native(None)
        self.assertFalse(native_available())

    def test_registering_a_checker_makes_it_available(self):
        """The seam itself. Whether the two agree is test_differential.py."""
        class Stub:
            @staticmethod
            def check_proof(*a):
                return (True, "stub", 1, 1, 0, 0, 0, 0, -1, True)

        register_native(Stub())
        self.assertTrue(native_available())
        register_native(None)
        self.assertFalse(native_available())


if __name__ == "__main__":
    unittest.main()
