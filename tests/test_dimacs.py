# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""DIMACS parsing, and the literal encoding underneath it.

The parser is the first thing a proof checker touches, and a parser that
quietly drops clauses turns a refutation into nonsense. That is not
hypothetical: a SATLIB file declaring 800 clauses once parsed to 396 here, and
every solver agreed on the wrong answer because they were all reading the same
mis-parsed formula. Hence `header_mismatch` and `strict`.
"""

from __future__ import annotations

import io
import unittest

from dratify import CNF, parse_dimacs, to_dimacs, from_dimacs, write_dimacs
from dratify.cnf import parse_dimacs_file, model_to_dimacs
from dratify.lits import (mk_lit, neg, var_of, is_neg, flip, lit_str,
                          clause_str, T, F, U)


class TestLiteralEncoding(unittest.TestCase):
    """Variable v is 2v positive, 2v+1 negated. Negation is one XOR."""

    def test_round_trip_through_dimacs(self):
        for d in (1, -1, 2, -2, 17, -17):
            self.assertEqual(to_dimacs(from_dimacs(d)), d)

    def test_negation_is_an_involution(self):
        for d in (1, -1, 5, -5):
            l = from_dimacs(d)
            self.assertEqual(neg(neg(l)), l)
            self.assertNotEqual(neg(l), l)

    def test_var_and_sign(self):
        pos, negl = from_dimacs(3), from_dimacs(-3)
        self.assertEqual(var_of(pos), var_of(negl))
        self.assertFalse(is_neg(pos))
        self.assertTrue(is_neg(negl))

    def test_mk_lit_matches_from_dimacs(self):
        self.assertEqual(mk_lit(2, False), from_dimacs(3))
        self.assertEqual(mk_lit(2, True), from_dimacs(-3))

    def test_printing_uses_internal_numbering(self):
        """`lit_str` shows the internal 0-based variable, not the DIMACS one.

        DIMACS 4 is internal variable 3. Worth pinning down: a debug print
        that silently renumbers is a confusing thing to chase.
        """
        self.assertEqual(lit_str(from_dimacs(4)), "x3")
        self.assertEqual(lit_str(from_dimacs(-4)), "~x3")
        self.assertIn("x3", clause_str([from_dimacs(4)]))


class TestTruthValues(unittest.TestCase):
    """`flip` negates a three-valued truth value, not a literal."""

    def test_flip_swaps_true_and_false(self):
        self.assertEqual(flip(T), F)
        self.assertEqual(flip(F), T)

    def test_undefined_flips_to_itself(self):
        self.assertEqual(flip(U), U)

    def test_the_three_values_are_distinct(self):
        self.assertEqual(len({T, F, U}), 3)


class TestParsing(unittest.TestCase):
    def test_a_plain_formula(self):
        f = parse_dimacs("p cnf 2 2\n1 2 0\n-1 -2 0\n")
        self.assertEqual(f.nvars, 2)
        self.assertEqual(len(f.clauses), 2)
        self.assertFalse(f.header_mismatch)

    def test_comments_and_blank_lines(self):
        f = parse_dimacs("c a comment\n\np cnf 1 1\nc another\n1 0\n\n")
        self.assertEqual(len(f.clauses), 1)

    def test_clause_spanning_several_lines(self):
        f = parse_dimacs("p cnf 3 1\n1 2\n3 0\n")
        self.assertEqual(len(f.clauses), 1)
        self.assertEqual(len(f.clauses[0]), 3)

    def test_satlib_trailing_percent(self):
        """SATLIB files end with a % and a 0. PySAT rejects these; we do not."""
        f = parse_dimacs("p cnf 1 1\n1 0\n%\n0\n")
        self.assertEqual(len(f.clauses), 1)

    def test_header_mismatch_is_reported_not_hidden(self):
        f = parse_dimacs("p cnf 2 5\n1 2 0\n")
        self.assertTrue(f.header_mismatch,
                        "a formula with fewer clauses than its header claims "
                        "must say so -- silently parsing half a file is how a "
                        "refutation becomes meaningless")

    def test_strict_mode_raises_on_a_bad_token(self):
        with self.assertRaises(ValueError):
            parse_dimacs("p cnf 1 1\nx 0\n", strict=True)

    def test_variables_beyond_the_header(self):
        f = parse_dimacs("p cnf 1 1\n1 5 0\n")
        self.assertGreaterEqual(f.nvars, 5)

    def test_empty_clause_in_the_input(self):
        f = parse_dimacs("p cnf 1 1\n0\n")
        self.assertEqual(len(f.clauses), 1)
        self.assertEqual(len(f.clauses[0]), 0, "the empty clause")

    def test_missing_header(self):
        f = parse_dimacs("1 2 0\n-1 0\n")
        self.assertEqual(len(f.clauses), 2)

    def test_file_round_trip(self):
        import tempfile, pathlib
        src = "p cnf 2 2\n1 2 0\n-1 -2 0\n"
        with tempfile.TemporaryDirectory() as d:
            p = pathlib.Path(d) / "f.cnf"
            p.write_text(src)
            f = parse_dimacs_file(str(p))
            self.assertEqual(len(f.clauses), 2)
            out = io.StringIO()
            write_dimacs(f, out)
            self.assertEqual(len(parse_dimacs(out.getvalue()).clauses), 2)


class TestCNF(unittest.TestCase):
    def test_add_rejects_signed_literals(self):
        f = CNF()
        f.new_vars(2)
        with self.assertRaises(ValueError):
            f.add([-1])

    def test_tautologies_are_dropped(self):
        f = CNF()
        f.new_vars(1)
        l = from_dimacs(1)
        self.assertFalse(f.add([l, neg(l)]), "a tautology adds nothing")

    def test_add_dimacs_accepts_signed(self):
        f = CNF()
        f.add_dimacs([1, -2])
        self.assertEqual(len(f.clauses), 1)

    def test_model_checking(self):
        f = parse_dimacs("p cnf 2 2\n1 0\n2 0\n")
        self.assertTrue(f.is_satisfied_by([True, True]))
        self.assertFalse(f.is_satisfied_by([True, False]))
        self.assertEqual(len(f.falsified_clauses([True, False])), 1)

    def test_copy_is_independent(self):
        f = parse_dimacs("p cnf 1 1\n1 0\n")
        g = f.copy()
        g.add_dimacs([-1])
        self.assertNotEqual(len(f.clauses), len(g.clauses))

    def test_stats_and_occurrences(self):
        f = parse_dimacs("p cnf 2 2\n1 2 0\n1 -2 0\n")
        self.assertIn("clauses", f.stats())
        self.assertEqual(sum(f.occurrence_counts()), 4)

    def test_variable_names_are_optional_labels(self):
        f = CNF()
        f.new_vars(2)
        f.set_name(0, "x")
        self.assertEqual(f.name(0), "x")

    def test_extend(self):
        f = CNF()
        f.new_vars(2)
        f.extend([[from_dimacs(1)], [from_dimacs(2)]])
        self.assertEqual(len(f.clauses), 2)

    def test_model_to_dimacs(self):
        self.assertEqual(model_to_dimacs([True, False]), [1, -2])


if __name__ == "__main__":
    unittest.main()
