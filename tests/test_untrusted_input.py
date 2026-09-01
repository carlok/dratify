# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Formulas, proofs and checkers that arrive from somewhere else.

SECURITY.md rates a crash or unbounded allocation on untrusted input as High,
and everything this package reads is untrusted by construction: a proof is
another program's output, and the formula usually is too.

The allocation tests assert that the input is *rejected*, not that memory
stayed low. A test that allocated to find out would be the bug.
"""

from __future__ import annotations

import io
import time
import unittest

from dratify import (CheckResult, ProofWriter, check_proof, parse_dimacs,
                     parse_proof, register_native, native_implementation)


class TestHostileSizes(unittest.TestCase):
    """`nvars` sizes the checker's arrays, so it is an allocation primitive."""

    def test_a_header_larger_than_the_file_is_rejected(self):
        t0 = time.perf_counter()
        with self.assertRaises(ValueError) as cm:
            parse_dimacs("p cnf 99999999999 0\n")
        self.assertLess(time.perf_counter() - t0, 1.0,
                        "rejection must be immediate, not after allocating")
        self.assertIn("99999999999", str(cm.exception))

    def test_a_negative_count_is_rejected(self):
        with self.assertRaises(ValueError):
            parse_dimacs("p cnf -5 1\n1 0\n")

    def test_a_non_numeric_header_names_the_line(self):
        with self.assertRaises(ValueError) as cm:
            parse_dimacs("p cnf x y\n")
        self.assertIn("line 1", str(cm.exception))

    def test_a_proof_literal_larger_than_the_file_is_rejected(self):
        t0 = time.perf_counter()
        with self.assertRaises(ValueError) as cm:
            parse_proof("99999999999 0\n")
        self.assertLess(time.perf_counter() - t0, 1.0)
        self.assertIn("99999999999", str(cm.exception))

    def test_an_ordinary_formula_still_parses(self):
        """The bound must not reject anything real."""
        f = parse_dimacs("p cnf 3 2\n1 2 0\n-1 3 0\n")
        self.assertEqual(f.nvars, 3)
        self.assertEqual(len(f.clauses), 2)

    def test_a_proof_may_still_introduce_fresh_variables(self):
        """RAT exists to add clauses over new variables; do not break that."""
        steps = parse_proof("4 0\n")
        self.assertEqual(len(steps), 1)


class TestMalformedProofText(unittest.TestCase):
    def test_a_bad_token_names_the_line(self):
        with self.assertRaises(ValueError) as cm:
            parse_proof("1 0\nd 2 x 0\n")
        self.assertIn("line 2", str(cm.exception))
        self.assertIn("'x'", str(cm.exception))


class TestProofWriterAcceptsAnyIterable(unittest.TestCase):
    """The signature says Iterable; a generator has to behave like a list."""

    def test_an_empty_clause_from_a_generator(self):
        out = io.StringIO()
        with ProofWriter(out) as w:
            w.add(x for x in [])
        self.assertEqual(out.getvalue(), "0\n",
                         "a generator is consumed by the join, and testing the "
                         "exhausted object for emptiness is always true")

    def test_a_generator_matches_a_list(self):
        a, b = io.StringIO(), io.StringIO()
        with ProofWriter(a) as w:
            w.add(x for x in (0, 2))
            w.delete(x for x in (0,))
        with ProofWriter(b) as w:
            w.add([0, 2])
            w.delete([0])
        self.assertEqual(a.getvalue(), b.getvalue())

    def test_what_it_writes_still_parses_back(self):
        out = io.StringIO()
        with ProofWriter(out) as w:
            w.add(x for x in (0,))
            w.add(x for x in [])
        self.assertEqual(parse_proof(out.getvalue()), [("a", (0,)), ("a", ())])


class _Stub:
    """A native checker that is wrong in one specific way."""

    def __init__(self, result):
        self._result = result

    def check_proof(self, *args):
        return self._result


class TestNativeCheckerContract(unittest.TestCase):
    """A registered module decides whether proofs are accepted.

    Unpacking whatever it returns turns a version skew into "not enough values
    to unpack" raised from inside a checker -- an exception a caller cannot
    tell apart from a verdict.
    """

    SQUARE = "p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n"
    PROOF = "1 0\n0\n"

    def tearDown(self):
        register_native(None)

    def _check(self):
        return check_proof(parse_dimacs(self.SQUARE), self.PROOF,
                           engine="native")

    def test_a_module_without_check_proof_is_refused_at_registration(self):
        with self.assertRaises(TypeError):
            register_native(object())

    def test_the_wrong_number_of_values_is_a_diagnostic(self):
        register_native(_Stub((True, "ok", 1, 1, 0, 0, 0, 0, -1)))  # 9, not 10
        with self.assertRaises(ValueError) as cm:
            self._check()
        self.assertIn("different version", str(cm.exception))

    def test_a_non_tuple_result_is_a_diagnostic(self):
        register_native(_Stub(True))
        with self.assertRaises(TypeError):
            self._check()

    def test_ok_without_the_empty_clause_is_refused(self):
        """The two cannot both be true, and accepting it would be the worst
        bug this package can have."""
        register_native(_Stub((True, "ok", 1, 1, 0, 0, 0, 0, -1, False)))
        with self.assertRaises(ValueError) as cm:
            self._check()
        self.assertIn("empty clause", str(cm.exception))

    def test_a_well_formed_result_is_accepted(self):
        register_native(_Stub((True, "fine", 2, 2, 0, 0, 0, 0, -1, True)))
        r = self._check()
        self.assertIsInstance(r, CheckResult)
        self.assertTrue(r.ok)
        self.assertEqual(r.reason, "fine")

    def test_which_implementation_is_in_use_is_inspectable(self):
        stub = _Stub((True, "fine", 1, 1, 0, 0, 0, 0, -1, True))
        register_native(stub)
        self.assertIs(native_implementation(), stub)
        register_native(None)
        self.assertIsNone(native_implementation())


if __name__ == "__main__":
    unittest.main()
