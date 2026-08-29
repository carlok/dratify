# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Writing proofs, reading them back, and the shapes check_proof accepts.

A proof that cannot survive a round trip through text is not much use: the
whole point is that another program, possibly in another language, picks it up
from a file.
"""

from __future__ import annotations

import io
import pathlib
import tempfile
import unittest

from dratify import CNF, MemoryProof, ProofWriter, check_proof, parse_dimacs
from dratify.proof import NullProof, parse_proof
from dratify.lits import from_dimacs


def lits(*d):
    return [from_dimacs(x) for x in d]


SQUARE = "p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n"
PROOF = "1 0\n0\n"


class TestMemoryProof(unittest.TestCase):
    def test_counts_and_text(self):
        p = MemoryProof()
        p.add(lits(1))
        p.delete(lits(2))
        p.add([])
        self.assertEqual(p.n_add, 2)
        self.assertEqual(p.n_del, 1)
        text = p.to_text()
        self.assertIn("d ", text)
        self.assertTrue(text.endswith("0\n"))

    def test_steps_round_trip_through_text(self):
        p = MemoryProof()
        p.add(lits(1))
        p.add([])
        self.assertEqual(list(p.steps), parse_proof(p.to_text()))

    def test_close_is_idempotent(self):
        p = MemoryProof()
        p.close()
        p.close()


class TestProofWriter(unittest.TestCase):
    def test_writes_to_a_stream(self):
        out = io.StringIO()
        with ProofWriter(out) as w:
            w.add(lits(1))
            w.add([])
        self.assertEqual(parse_proof(out.getvalue()),
                         [("a", (from_dimacs(1),)), ("a", ())])

    def test_writes_to_a_path(self):
        with tempfile.TemporaryDirectory() as d:
            path = pathlib.Path(d) / "p.drat"
            with ProofWriter(str(path)) as w:
                w.add(lits(1))
                w.delete(lits(1))
            text = path.read_text()
        self.assertIn("d ", text)

    def test_unbuffered_writes_immediately(self):
        out = io.StringIO()
        w = ProofWriter(out, buffered=False)
        w.add(lits(1))
        self.assertTrue(out.getvalue(), "nothing was written before flush")
        w.close()

    def test_flush_then_more(self):
        out = io.StringIO()
        w = ProofWriter(out)
        w.add(lits(1))
        w.flush()
        w.add([])
        w.close()
        self.assertEqual(len(parse_proof(out.getvalue())), 2)

    def test_a_written_proof_still_verifies(self):
        out = io.StringIO()
        with ProofWriter(out) as w:
            w.add(lits(1))
            w.add([])
        self.assertTrue(check_proof(parse_dimacs(SQUARE), out.getvalue()).ok)


class TestNullProof(unittest.TestCase):
    def test_accepts_everything_and_records_nothing(self):
        p = NullProof()
        p.add(lits(1))
        p.delete(lits(1))
        p.close()


class TestParseProof(unittest.TestCase):
    def test_additions_deletions_and_the_empty_clause(self):
        steps = parse_proof("1 2 0\nd 1 0\n0\n")
        self.assertEqual([k for k, _ in steps], ["a", "d", "a"])
        self.assertEqual(steps[-1][1], ())

    def test_blank_lines_and_whitespace(self):
        self.assertEqual(len(parse_proof("\n  1 0  \n\n0\n")), 2)

    def test_a_missing_terminator_is_tolerated(self):
        self.assertEqual(len(parse_proof("1 0\n0")), 2)


class TestCheckProofInputShapes(unittest.TestCase):
    def setUp(self):
        self.f = parse_dimacs(SQUARE)

    def test_accepts_text(self):
        self.assertTrue(check_proof(self.f, PROOF).ok)

    def test_accepts_a_memory_proof(self):
        p = MemoryProof()
        p.add(lits(1))
        p.add([])
        self.assertTrue(check_proof(self.f, p).ok)

    def test_accepts_a_list_of_steps(self):
        self.assertTrue(check_proof(self.f, parse_proof(PROOF)).ok)

    def test_an_unknown_engine_is_rejected(self):
        with self.assertRaises(ValueError):
            check_proof(self.f, PROOF, engine="banana")

    def test_rat_can_be_turned_off(self):
        self.assertTrue(check_proof(self.f, PROOF, check_rat=False).ok)

    def test_an_empty_proof_proves_nothing(self):
        r = check_proof(self.f, "")
        self.assertFalse(r.ok)
        self.assertFalse(r.reached_empty)


if __name__ == "__main__":
    unittest.main()
