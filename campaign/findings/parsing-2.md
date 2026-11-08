# parsing-2: tokens after a header's fourth are ignored, and a clause goes with them

**Proposed severity: Bug.** The brief's Bug list has no line for a parser, so this is by
its nearest entries and the corner's rule that a text must not silently parse to something
else. It is not a false acceptance: losing a clause makes refuting harder, not easier. It
can give a wrong SAT answer to anyone using this parser to solve.

## Minimal case

`p cnf 1 1 -1 0\n1 0\n`. Removing the `-1 0` from the header line leaves a correct file. The
second form of the same defect is `pq cnf 1 1\n1 0\n`, a first token that only starts with `p`.

## Reproducer

```python
from dratify import parse_dimacs, to_dimacs

for text in ("p cnf 1 1 -1 0\n1 0\n", "p cnf 1 0 1 0\n", "pq cnf 1 1\n1 0\n"):
    f = parse_dimacs(text, strict=True)
    print(repr(text), [[to_dimacs(l) for l in c] for c in f.clauses], f.header_mismatch)
```

```
'p cnf 1 1 -1 0\n1 0\n' [[1]] None
'p cnf 1 0 1 0\n' [] None
'pq cnf 1 1\n1 0\n' [[1]] None
```

Should be: `ValueError` on all three, as `p cnf 1\n` already does ("malformed header").
No mismatch is reported because the declared counts agree with what is left.

```
$ printf 'p cnf 1 1 -1 0\n1 0\n' > h.cnf
$ minisat -verb=0 h.cnf     # exit 20, UNSATISFIABLE: it reads the clause
$ cadical -q -n h.cnf       # exit 1, parse error
$ kissat -q -n h.cnf        # exit 1, parse error
$ python -m cdclkit solve h.cnf    # s SATISFIABLE, v 1
```

`pq cnf 1 1`: minisat exits 3, and cadical and kissat exit 1. All three refuse it.

The oracle has no parser to ask here; what it shows is that the clause matters:
`oracle.satisfiable([[1], [-1]])` is False and `oracle.satisfiable([[1]])` is True.

## Suspected cause

`src/dratify/cnf.py:287-289`: `head == "p"` looks at one character, and `len(parts) < 4`
sets only a minimum. Both engines take this parse. The fix looks clear:
`parts[0] != "p" or len(parts) != 4 or parts[1] != "cnf"` raises. It also has to land with
parsing-1's fix, which sends CR-only files down this path.

## Proposed test

```python
import unittest

from dratify import parse_dimacs


class TestAHeaderIsExactlyFourTokens(unittest.TestCase):
    def test_tokens_after_the_fourth_are_refused(self):
        for text in ("p cnf 1 1 -1 0\n1 0\n", "p cnf 1 0 1 0\n", "p cnf 1 1 x\n1 0\n"):
            for strict in (False, True):
                with self.subTest(text=text, strict=strict):
                    with self.assertRaises(ValueError) as cm:
                        parse_dimacs(text, strict=strict)
                    self.assertIn("line 1", str(cm.exception))

    def test_the_first_token_is_exactly_p(self):
        with self.assertRaises(ValueError):
            parse_dimacs("pq cnf 1 1\n1 0\n")
```
