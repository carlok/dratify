# parsing-5: `header_mismatch` has gaps

**Proposed severity: Note.** No clause changes and no verdict changes. literals-7 reports the
first case. The field exists so a wrong header is "reported, not hidden" (`tests/test_dimacs.py`),
and these three are where it is not, or is hard to read.

## Minimal cases and reproducer

```python
from dratify import parse_dimacs

# 1. Same clause as a set; strict depends on the literal order.
print(parse_dimacs("p cnf 1 1\n1 -1 2 0\n", strict=True).nvars)
try:
    parse_dimacs("p cnf 1 1\n2 1 -1 0\n", strict=True)
except ValueError as e:
    print("raises:", e)

# 2. copy() drops the field.
f = parse_dimacs("p cnf 2 5\n1 2 0\n")
print(f.header_mismatch, f.copy().header_mismatch)

# 3. A mismatch on variables reports equal clause counts.
print(parse_dimacs("p cnf 1 1\n2 0\n").header_mismatch)
```

```
1
raises: header says 1 vars / 1 clauses, found 2 / 1
(5, 1) None
(1, 1)
```

Should be: case 1 raises both ways, since variable 2 exceeds the declared 1 whichever order
the clause is written in. Case 2 keeps `(5, 1)`. Case 3 is truthy, so a caller testing
truthiness is right, but the field is documented as `(declared_clauses, parsed_clauses)`
and says nothing about variables.

No oracle call applies: a dropped tautology does not change satisfiability, which is why this
is a Note. `oracle.satisfiable([[1, -1, 2]])` and `oracle.satisfiable([])` are both True.

## Suspected cause

1. `src/dratify/cnf.py:157-158`: `CNF.add` returns on the clash, before `nvars` sees the
   literals after it.
2. `cnf.py:238-243`: `copy` does not copy `header_mismatch`. cdclkit's CLI uses `f.copy()` as
   its `original` at `cdclkit/cli.py:105`.
3. `cnf.py:350`.

Both engines take this parse. The fixes for 1 and 2 are clear. Case 3 needs a decision about
the field's shape.

## Proposed test

```python
import unittest

from dratify import parse_dimacs


class TestHeaderMismatchGaps(unittest.TestCase):
    def test_strict_does_not_depend_on_literal_order(self):
        for text in ("p cnf 1 1\n1 -1 2 0\n", "p cnf 1 1\n2 1 -1 0\n"):
            with self.subTest(text=text):
                with self.assertRaises(ValueError):
                    parse_dimacs(text, strict=True)

    def test_copy_keeps_the_mismatch(self):
        f = parse_dimacs("p cnf 2 5\n1 2 0\n")
        self.assertEqual(f.copy().header_mismatch, f.header_mismatch)
```
