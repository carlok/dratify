# parsing-6: `%` ends the formula wherever it appears

**Proposed severity: Note.** It is documented, deliberately: the docstring tolerates "`%` /
trailing `0` terminators from SATLIB files", and README presents reading those files as a
feature. So this is not a bug. The point is how far the tolerance reaches: it drops real
clauses silently, including under `strict=True`, when SATLIB only ever needs it to skip one `0`.

## Minimal case

`p cnf 1 1\n1 0\n%\n-1 0\n`. Removing the `%` makes strict raise on the count.

## Reproducer

```python
from dratify import parse_dimacs, to_dimacs
from campaign import oracle

f = parse_dimacs("p cnf 1 1\n1 0\n%\n-1 0\n", strict=True)
print([[to_dimacs(l) for l in c] for c in f.clauses], f.header_mismatch)
print(oracle.satisfiable([[1]]), oracle.satisfiable([[1], [-1]]))
```

```
[[1]] None
True False
```

Minisat exits 3, and cadical and kissat exit 1: all three refuse the file. Fails closed for the
checker, since fewer clauses make refuting harder, but a solver using this parser answers SAT.

`%` also ends the parse in `1 2\n%\n3 0\n`, where the open clause `(1 2)` is kept in lenient mode.
Strict raises there, correctly.

A related reading trap: the docstring's "trailing `0` terminators" means only the `0` after a
`%`. A bare trailing `0` is an empty clause, `p cnf 1 1\n1 0\n0\n` is unsatisfiable, and
`header_mismatch` is `(1, 2)`. Minisat agrees (exit 20), and `tests/test_dimacs.py` pins this. The
code is right; the sentence could be clearer.

## Suspected cause

`src/dratify/cnf.py:285-286`. A stricter rule, if wanted: under `strict=True`, or always, allow
only blank lines, comments and one `0` after a `%`, and raise on anything else. That keeps every
SATLIB file. Whether to do this is a design choice, so the generator counts it instead of
failing on it (`note_percent_drops_real_clause_under_strict`).

## Proposed test

Only if the stricter rule is chosen:

```python
import unittest

from dratify import parse_dimacs


class TestAfterThePercent(unittest.TestCase):
    def test_satlib_still_reads(self):
        for text in ("p cnf 1 1\n1 0\n%\n0\n", "p cnf 1 1\n1 0\n%\n0\n\n", "p cnf 1 1\n1 0\n%\n"):
            with self.subTest(text=text):
                self.assertEqual(len(parse_dimacs(text, strict=True).clauses), 1)

    def test_a_clause_after_the_percent_is_refused_when_strict(self):
        with self.assertRaises(ValueError):
            parse_dimacs("p cnf 1 1\n1 0\n%\n-1 0\n", strict=True)
```
