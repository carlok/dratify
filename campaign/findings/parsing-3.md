# parsing-3: tokens are whatever Python's `int()` and `str.split()` accept

**Proposed severity: Bug.** Both parsers. literals-6 reports part of this as a Note,
because no verdict goes wrong. I rate it higher for one case it may not cover: a non-breaking
space before `c` turns a clause line into a comment, so a clause is silently dropped, and
that holds under `strict=True` when the header agrees. It is also the corner's rule: this
text has no meaning, every reference solver refuses it, and dratify reads one anyway.

## Minimal cases

Each is one token or one separator; replacing it with its ASCII spelling, or removing it,
makes the text correct.

| text | read as | should be |
|---|---|---|
| `1_0 0` | variable 10 | `ValueError` |
| `٣ 0` (ARABIC-INDIC 3) | variable 3 | `ValueError` |
| `１ 0` (FULLWIDTH 1) | variable 1 | `ValueError` |
| `1 ٠` (ARABIC-INDIC 0) | ends the clause | `ValueError` |
| `1 2 0` (NBSP) | two literals | `ValueError` |
| ` c -1 0` | a comment: the clause is gone | `ValueError` |
| `p cnf 1_0 1` | a header declaring 10 | `ValueError` |

## Reproducer

```python
from dratify import parse_dimacs, parse_proof, to_dimacs

for text in ("p cnf 16 1\n1_0 0\n", "p cnf 3 1\n٣ 0\n", "p cnf 1 1\n1 ٠\n",
             "p cnf 2 1\n1 2 0\n", "p cnf 1 1\n1 0\n c -1 0\n"):
    f = parse_dimacs(text, strict=True)
    print(repr(text), [[to_dimacs(l) for l in c] for c in f.clauses])
for text in ("1_0 0\n", "d1_0 0\n", "٣ 0\n", "1 ٠\n", "1 2 0\n"):
    print(repr(text), [(k, [to_dimacs(l) for l in c]) for k, c in parse_proof(text)])
```

```
'p cnf 16 1\n1_0 0\n' [[10]]
'p cnf 3 1\n٣ 0\n' [[3]]
'p cnf 1 1\n1 ٠\n' [[1]]
'p cnf 2 1\n1\xa02 0\n' [[1, 2]]
'p cnf 1 1\n1 0\n\xa0c -1 0\n' [[1]]
'1_0 0\n' [('a', [10])]
'd1_0 0\n' [('d', [10])]
'٣ 0\n' [('a', [3])]
'1 ٠\n' [('a', [1])]
'1\xa02 0\n' [('a', [1, 2])]
```

Minisat exits 3, and cadical and kissat exit 1, on every one of those I ran: `1_0`, `٣`,
`٠`, `１`, NBSP between literals, and NBSP before `c`.

The oracle shows the hidden clause matters: `oracle.satisfiable([[1], [-1]])` is False and
`oracle.satisfiable([[1]])` is True.

`+1` and `-0` are not part of this. They are ASCII and fscanf reads them the same way, so the
generator accepts them. Cadical and kissat refuse them, and minisat reads them.

## Suspected cause

`int(tok)` at `src/dratify/cnf.py:320` and the two in the header at `cnf.py:292-293`;
`int(num)` at `src/dratify/proof.py:251`; `strip()` and `split()` at `cnf.py:278,288,318` and
`proof.py:236,239`. Both engines take this parse.

The fix looks clear: one helper in `lits.py` that matches `[+-]?[0-9]+` with `re.fullmatch`,
and splitting on ASCII whitespace. `re.fullmatch` needs `[0-9]`, since `\d` matches these
digits too.

## Proposed test

```python
import unittest

from dratify import parse_dimacs, parse_proof


class TestTokensAreAscii(unittest.TestCase):
    def test_dimacs_refuses_them(self):
        for text in ("p cnf 16 1\n1_0 0\n", "p cnf 3 1\n٣ 0\n",
                     "p cnf 1 1\n１ 0\n", "p cnf 1 1\n1 ٠\n",
                     "p cnf 2 1\n1 2 0\n", "p cnf 1 1\n1 0\n c -1 0\n",
                     "p cnf 1_0 1\n1 0\n", "p cnf 2 1\n1\x1f2 0\n"):
            with self.subTest(text=text):
                with self.assertRaises(ValueError):
                    parse_dimacs(text)

    def test_proofs_refuse_them(self):
        for text in ("1_0 0\n", "d1_0 0\n", "٣ 0\n", "d٣ 0\n", "1 ٠\n",
                     "1 2 0\n", " c 1 0\n"):
            with self.subTest(text=text):
                with self.assertRaises(ValueError):
                    parse_proof(text)

    def test_ascii_signs_and_zeros_still_read(self):
        self.assertEqual(len(parse_dimacs("p cnf 2 1\n+1 02 0\n", strict=True).clauses), 1)
```
