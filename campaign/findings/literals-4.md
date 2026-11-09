# literals-4: a DIMACS comment ends at a form feed, so comment text becomes a clause

**Proposed severity: Critical, by the end-to-end question.** `parse_dimacs` then
`check_proof`, the README's own pipeline, returns `ok=True` on a file that minisat, CaDiCaL
and kissat read as satisfiable.

The caveat: the checking is right for the clauses it was given. The misreading is in the
parser, and it needs an unusual byte inside a comment, so it takes a crafted file or bad
luck. If the owner reads "formula" as "what `parse_dimacs` returned", this is a Bug.

Outside this corner's brief, found while testing what a token is. `campaign/gen_parsing.py`
exists and may report it too.

## Minimal case

Bytes, where `\f` is 0x0c:

```
p cnf 1 2\n1 0\nc x\f-1 0\n
```

A comment runs to the newline, so this file has one clause, `(1)`. dratify reads a second
one, `(-1)`, and then the proof `0` refutes it.

## Reproducer

```python
import cdclkit_native
from campaign import oracle
from dratify import check_proof, parse_dimacs, parse_proof, register_native
register_native(cdclkit_native)

text = "p cnf 1 2\n1 0\nc x\f-1 0\n"
for strict in (False, True):
    f = parse_dimacs(text, strict=strict)
    print(strict, f.clauses, f.header_mismatch,
          [check_proof(f, "0\n", engine=e).ok for e in ("python", "native")])
print(oracle.satisfiable([[1]]))
for sep in ("\x0b", "\x0c", "\r", "\x1c", "\x1d", "\x1e", "\x85", " ", " "):
    print(repr(sep), parse_dimacs(f"p cnf 1 2\n1 0\nc x{sep}-1 0\n").clauses,
          parse_proof(f"c x{sep}1 0\n"))
```

Actual output:

```
False [(0,), (1,)] None [True, True]
True [(0,), (1,)] None [True, True]
True
'\x0b' [(0,), (1,)] [('a', (0,))]
'\x0c' [(0,), (1,)] [('a', (0,))]
'\r' [(0,), (1,)] [('a', (0,))]
'\x1c' [(0,), (1,)] [('a', (0,))]
'\x1d' [(0,), (1,)] [('a', (0,))]
'\x1e' [(0,), (1,)] [('a', (0,))]
'\x85' [(0,), (1,)] [('a', (0,))]
' ' [(0,), (1,)] [('a', (0,))]
' ' [(0,), (1,)] [('a', (0,))]
```

Expected: clauses `[(0,)]`, parsed the way the solvers parse it, and `ok=False`. Note that
`header_mismatch` is `None` and `strict=True` passes: the header agrees with the misreading.

The real solvers, run on these bytes:

| file | minisat | cadical | kissat | dratify |
|---|---|---|---|---|
| `p cnf 1 2 ...` | SATISFIABLE | parse error, clause missing | parse error, one clause missing | `ok=True`, `header_mismatch=None`, strict passes |
| `p cnf 1 1 ...` | SATISFIABLE | `s SATISFIABLE` | `s SATISFIABLE` | `ok=True`, `header_mismatch=(1, 2)`; strict raises |

So with a one-clause header all three solvers answer SAT, and dratify's default path says
the file is refuted, recording the disagreement only in a field nobody has to read. With a
two-clause header dratify's strict mode has nothing to report.

In a proof the same split runs a step hidden in a comment. That is not unsound, since the
step is still checked, but `parse_proof` reads something else than the file says.

`\r` is the weakest of these: a CR-only file from an old Mac would want splitting there,
although C readers do not do it. The other eight have no such excuse.

## Cause and engines

- `src/dratify/cnf.py:277` (`text.splitlines()` in `parse_dimacs`).
- `src/dratify/proof.py:235` (the same in `parse_proof`).

`str.splitlines` breaks on all the characters above. Text is parsed once, in Python, so both
engines inherit it.

## Is the fix clear?

Yes. Split on `\n` only and let `strip()` take a trailing `\r`, so `\r\n` files still read:

```python
for lineno, raw in enumerate(text.split("\n"), 1):
```

Decide separately whether CR-only files are worth keeping; if so, normalise `\r\n` and `\r`
explicitly and leave the rest alone. See `literals-6` for the matching tokeniser leniency.

## Reach in this generator

Label `comment-split`, 3704 occurrences; `comment_refuted_satisfiable` 1852, meaning a
formula reference-read as satisfiable got `ok=True`. The reference reader is
`reference_read` in `campaign/gen_literals.py`, which reads as C readers do, and the table
above is why I trust that reading.

## Proposed failing test

```python
class TestCommentsEndAtNewlines(unittest.TestCase):
    def test_a_form_feed_does_not_end_a_comment(self):
        for sep in "\x0b\x0c\x1c\x1d\x1e\x85  ":
            with self.subTest(sep=sep):
                f = parse_dimacs(f"p cnf 1 1\n1 0\nc x{sep}-1 0\n")
                self.assertEqual(f.clauses, [(0,)])
                self.assertFalse(check_proof(f, "0\n", engine="python").ok)

    def test_nor_in_a_proof(self):
        self.assertEqual(parse_proof("c x\f1 0\n"), [])

    def test_crlf_still_reads(self):
        self.assertEqual(parse_dimacs("p cnf 1 1\r\n1 0\r\n").clauses, [(0,)])
```
