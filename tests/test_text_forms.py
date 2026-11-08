# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""What a line is, what a header is and what a token is, in both parsers.

These were whatever Python's `str` methods said they were, and Python knows more
line breaks and more digits than a DIMACS file does.

The case that mattered: `str.splitlines` ends a line at a form feed, so in ::

    p cnf 1 1
    c<FF>p cnf 1 2
    1 0
    c<FF>-1 0

a comment ended early and its remainder was read as a header and a clause. This
file has one clause, and minisat, cadical and kissat all call it satisfiable.
dratify read two and accepted the proof ``0``, even with ``strict=True``. A DIMACS
reader ends a comment at a newline; so does this now.
"""

from __future__ import annotations

import pathlib
import tempfile
import unittest

from dratify import (check_proof, parse_dimacs, parse_dimacs_file, parse_proof,
                     register_native)
from dratify.lits import from_dimacs

try:
    from tests.test_root_units import _native
except ImportError:            # discover -s tests puts tests/ on the path
    from test_root_units import _native

#: `str.splitlines` breaks on all of these, and a DIMACS reader on none of them
BREAKS = "\r\x0b\x0c\x1c\x1d\x1e\x85  "
ONE = (from_dimacs(1),)


def in_a_file(data: bytes):
    d = tempfile.TemporaryDirectory()
    p = pathlib.Path(d.name) / "f.cnf"
    p.write_bytes(data)
    return d, str(p)


class TestAHiddenRefutation(unittest.TestCase):
    engine = "python"

    def test_a_comment_cannot_add_a_clause_and_a_header(self):
        text = "p cnf 1 1\nc\x0cp cnf 1 2\n1 0\nc\x0c-1 0\n"
        for strict in (False, True):
            with self.subTest(strict=strict):
                f = parse_dimacs(text, strict=strict)
                self.assertEqual(f.clauses, [ONE])
                self.assertIsNone(f.header_mismatch)
                r = check_proof(f, "0\n", engine=self.engine)
                self.assertFalse(r.ok, "1 true satisfies the file as written")

    def test_nor_before_the_header(self):
        f = parse_dimacs("c\x0c-1 0\np cnf 1 1\n1 0\n", strict=True)
        self.assertEqual(f.clauses, [ONE])
        self.assertFalse(check_proof(f, "0\n", engine=self.engine).ok)


@unittest.skipIf(_native() is None,
                 "no native checker installed; CI installs cdclkit-native")
class TestAHiddenRefutationNative(TestAHiddenRefutation):
    engine = "native"

    @classmethod
    def setUpClass(cls):
        register_native(_native())

    @classmethod
    def tearDownClass(cls):
        register_native(None)


class TestLines(unittest.TestCase):
    def test_every_other_break_stays_in_a_dimacs_comment(self):
        for ch in BREAKS:
            with self.subTest(ch=repr(ch)):
                f = parse_dimacs(f"p cnf 1 1\n1 0\nc x{ch}-1 0\n", strict=True)
                self.assertEqual(f.clauses, [ONE])
                self.assertEqual(f.comments, [f"x{ch}-1 0"])

    def test_and_in_a_proof_comment(self):
        for ch in BREAKS:
            with self.subTest(ch=repr(ch)):
                self.assertEqual(parse_proof(f"c x{ch}d 1 2 0\n"), [])
                self.assertEqual(parse_proof(f"c x{ch}1 0\n2 0\n"),
                                 [("a", (from_dimacs(2),))])

    def test_crlf_still_reads(self):
        f = parse_dimacs("c x\r\np cnf 2 1\r\n1 2 0\r\n", strict=True)
        self.assertEqual(f.comments, ["x"])
        self.assertEqual(len(f.clauses), 1)
        self.assertEqual(parse_proof("c x\r\n1 2 0\r\nd 1 2 0\r\n0\r\n"),
                         [("a", (0, 2)), ("d", (0, 2)), ("a", ())])

    def test_the_file_reader_keeps_a_stray_cr(self):
        """Universal newlines would turn it into a line break before the parser."""
        d, path = in_a_file(b"p cnf 1 1\n1 0\nc x\r-1 0\n")
        with d:
            self.assertEqual(parse_dimacs_file(path, strict=True).clauses, [ONE])

    def test_the_file_reader_keeps_crlf_working(self):
        d, path = in_a_file(b"c x\r\np cnf 1 1\r\n1 0\r\n")
        with d:
            self.assertEqual(parse_dimacs_file(path, strict=True).clauses, [ONE])

    def test_cr_only_files_are_refused(self):
        for text in ("p cnf 1 1\r1 0\r", "c x\rp cnf 1 1\r1 0\r", "1 0\r2 0\r"):
            with self.subTest(text=text):
                with self.assertRaises(ValueError) as cm:
                    parse_dimacs(text)
                self.assertIn("CR-only", str(cm.exception))
                d, path = in_a_file(text.encode())
                with d, self.assertRaises(ValueError):
                    parse_dimacs_file(path)
        for text in ("1 0\r0\r", "c x\r1 0\r"):
            with self.subTest(text=text), self.assertRaises(ValueError) as cm:
                parse_proof(text)
            self.assertIn("CR-only", str(cm.exception))

    def test_a_cr_between_tokens_is_refused_and_named(self):
        with self.assertRaises(ValueError) as cm:
            parse_dimacs("p cnf 2 2\n1 0\n2 0\r-1 0\n")
        self.assertIn("line 3", str(cm.exception))
        with self.assertRaises(ValueError) as cm:
            parse_proof("1 0\n2 0\r3 0\n")
        self.assertIn("line 2", str(cm.exception))
        with self.assertRaises(ValueError):
            parse_dimacs("1 0\r\r\n")

    def test_a_form_feed_between_tokens_is_only_a_separator(self):
        self.assertEqual(parse_dimacs("1\x0b2\x0c0\n").clauses, [(0, 2)])
        self.assertEqual(parse_proof("1\x0b2\x0c0\n"), [("a", (0, 2))])


class TestOneHeader(unittest.TestCase):
    def test_a_second_header_is_refused(self):
        for strict in (False, True):
            with self.subTest(strict=strict):
                with self.assertRaises(ValueError) as cm:
                    parse_dimacs("p cnf 1 1\n1 0\np cnf 1 2\n-1 0\n", strict=strict)
                self.assertIn("line 3", str(cm.exception))
                self.assertIn("line 1", str(cm.exception))

    def test_even_an_identical_one(self):
        with self.assertRaises(ValueError):
            parse_dimacs("p cnf 1 1\np cnf 1 1\n1 0\n")

    def test_one_header_after_the_clauses_is_still_tolerated(self):
        f = parse_dimacs("1 0\np cnf 1 1\n")
        self.assertEqual(f.clauses, [ONE])
        self.assertIsNone(f.header_mismatch)


if __name__ == "__main__":
    unittest.main()
