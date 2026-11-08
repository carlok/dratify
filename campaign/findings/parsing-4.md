# parsing-4: a second `p cnf` line replaces the first, and defeats `strict=True`

**Proposed severity: Bug.** The docstring says "With `strict=True` a header mismatch raises".
Here the first header disagrees with the clauses and nothing raises. No clause is lost, so
this does not change a verdict alone. It is what lets parsing-1 past `strict=True`.

## Minimal case

`p cnf 1 1\n1 0\np cnf 1 2\n-1 0\n`. Removing the second header makes strict raise, as it
should, since the first header then disagrees.

## Reproducer

```python
from dratify import parse_dimacs, to_dimacs

f = parse_dimacs("p cnf 1 1\n1 0\np cnf 1 2\n-1 0\n", strict=True)
print([[to_dimacs(l) for l in c] for c in f.clauses], f.header_mismatch)
```

```
[[1], [-1]] None
```

Should be: `ValueError` naming line 3. Cadical and kissat exit 1 on this file. Minisat accepts
it and exits 20, so a tolerant reading exists, but a lenient mode that keeps going should at
least set `header_mismatch`, and strict should raise.

The oracle does not settle what a header means. It does show the two readings differ:
`oracle.satisfiable([[1]])` is True, for what the first header declares, and
`oracle.satisfiable([[1], [-1]])` is False.

## Suspected cause

`src/dratify/cnf.py:292-293` overwrites `declared_vars` and `declared_clauses`. Both engines
take this parse. The fix looks clear: raise if a header was already seen. Whether a single
header after clauses should also raise is a separate choice; the generator leaves it
tolerated and says so in `not_checked`.

## Proposed test

```python
import unittest

from dratify import parse_dimacs


class TestOneHeader(unittest.TestCase):
    def test_a_second_header_is_refused(self):
        for strict in (False, True):
            with self.subTest(strict=strict):
                with self.assertRaises(ValueError) as cm:
                    parse_dimacs("p cnf 1 1\n1 0\np cnf 1 2\n-1 0\n", strict=strict)
                self.assertIn("line 3", str(cm.exception))
```
