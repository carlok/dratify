# SPDX-License-Identifier: Apache-2.0
"""What a proof checker has to get right, in both directions.

A checker that never rejects passes every positive test, so the negative cases
below carry most of the weight: a truncated proof, and a "refutation" of a
formula that is actually satisfiable.
"""

from __future__ import annotations

import pathlib
import unittest

from dratify import CNF, check_proof, native_available, parse_dimacs

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

    @unittest.skipUnless(native_available(), "Rust checker not installed")
    def test_engines_agree(self):
        """Both engines, both verdicts. Agreement is the whole product."""
        cases = [
            (SQUARE, SQUARE_PROOF, True),
            (SQUARE, "1 0\n", False),
            ((HERE / "php32.cnf").read_text(),
             (HERE / "php32.drat").read_text(), True),
        ]
        for text, proof, expected in cases:
            f = parse_dimacs(text)
            py = check_proof(f, proof, engine="python")
            rs = check_proof(f, proof, engine="native")
            self.assertIs(py.ok, expected)
            self.assertIs(rs.ok, py.ok, "engines disagreed")

    def test_native_requested_but_absent_explains_itself(self):
        if native_available():
            self.skipTest("native is installed")
        with self.assertRaises(RuntimeError) as cm:
            check_proof(parse_dimacs(SQUARE), SQUARE_PROOF, engine="native")
        self.assertIn("engine=", str(cm.exception))


if __name__ == "__main__":
    unittest.main()
