# parsing-1: a comment ends at any Unicode line break, so a hidden clause is read

**Proposed severity: Critical.** `ok=True` on a file that minisat, cadical and kissat all
call SATISFIABLE, on both engines, and `strict=True` does not stop it.

literals-4 reports the form feed. This covers the whole class, the header variant that
passes `strict=True`, `parse_proof`, and the file-reading paths.

## Minimal case

```
p cnf 1 1
c<FF>p cnf 1 2
1 0
c<FF>-1 0
```

`<FF>` is the single byte 0x0C. Without the form feed on the last line, `-1 0` stays a comment
and the proof is rejected. Without the one on line 2, `strict=True` raises on the clause
count, but lenient parsing still gives `ok=True`: `p cnf 1 1\n1 0\nc\x0c-1 0\n` is the
shortest form of that, with `header_mismatch` set to `(1, 2)`.

## Reproducer

```python
from dratify import check_proof, parse_dimacs, register_native, to_dimacs
from campaign import oracle
import cdclkit_native
register_native(cdclkit_native)

text = "p cnf 1 1\nc\x0cp cnf 1 2\n1 0\nc\x0c-1 0\n"
f = parse_dimacs(text, strict=True)
print([[to_dimacs(l) for l in c] for c in f.clauses], f.header_mismatch)
for engine in ("python", "native"):
    print(engine, check_proof(f, "0\n", engine=engine).ok)
print(oracle.satisfiable([[1]]))  # the formula once comments end at \n
```

```
[[1], [-1]] None
python True
native True
True
```

Should be: the clauses `[[1]]`, and `ok=False`. The oracle says the file's formula is
satisfiable. The solvers read the same file the same way:

```
$ printf 'p cnf 1 1\nc\fp cnf 1 2\n1 0\nc\f-1 0\n' > s.cnf
$ minisat -verb=0 s.cnf; cadical -q -n s.cnf; kissat -q -n s.cnf   # exit 10, 10, 10
$ python -m cdclkit solve --self-check s.cnf                       # s UNSATISFIABLE, s VERIFIED
```

So cdclkit disagrees with all three on this file and its self-check passes, because its CLI
parses with this code. That is the cdclkit half of the Critical definition too: a wrong
UNSAT that passes its own self-check, for the file.

## The class

Every separator `str.splitlines` honours except `\n` does this: `\r`, `\x0b`, `\x0c`,
`\x1c`, `\x1d`, `\x1e`, `\x85`, ` `, ` `. The generator reaches all nine.
Minisat, cadical and kissat gave exit 10 on `p cnf 1 1\n1 0\nc x<ch>-1 0\n` for the six
tried (`\r \x0b \x0c \x1c \x85  `).

`parse_proof` has the same defect: `c note\x0cd 1 2 0\n` parses to one deletion. Added
steps there are still checked, so this one is not a false acceptance on its own, but the
proof read is not the proof written.

## Why Critical, and the case against

The case against: the `CNF` in memory really is unsatisfiable, so `check_proof` is correct
about what it was given, and with an honest single header lenient mode sets
`header_mismatch`. But README's first example is `parse_dimacs(Path(...).read_text())` then
`check_proof`, `check_proof` does not look at `header_mismatch`, a hidden second header
clears it, and `SECURITY.md` rates accepting a proof of a satisfiable formula as the worst
bug and says these files arrive from elsewhere. The end-to-end question has the wrong
answer, for the file.

## Suspected cause

`text.splitlines()`: `src/dratify/cnf.py:277` and `src/dratify/proof.py:235`. Both engines:
text is parsed once, in Python. The Rust crate has no parser.

The fix looks clear in the parsers, `text.split("\n")` with `strip()` removing a CRLF's
`\r`, but it has three edges:

- A bare `\r` also needs the callers changed. `parse_dimacs_file` (`cnf.py:355`) and
  README's `read_text()` open in universal-newline mode, which turns `\r` into `\n` before
  the parser sees it. `parse_dimacs_file` needs `newline=""`, and README's path cannot be
  fixed from inside the parser.
- A CR-only file becomes one long line. That has to raise, which relies on fixing
  parsing-2: today `p cnf 1 1\r1 0\r` would then silently lose its clause.
- `str.split()` still treats `\x85` and friends as whitespace: parsing-3.

## Proposed test

```python
import unittest

from dratify import check_proof, parse_dimacs, parse_proof


class TestACommentEndsAtNewlineOnly(unittest.TestCase):
    BREAKS = "\r\x0b\x0c\x1c\x1d\x1e\x85  "

    def test_a_clause_after_a_line_separator_stays_in_the_comment(self):
        for ch in self.BREAKS:
            with self.subTest(ch=repr(ch)):
                f = parse_dimacs(f"p cnf 1 1\n1 0\nc x{ch}-1 0\n", strict=True)
                self.assertEqual(len(f.clauses), 1)

    def test_a_hidden_refutation_of_a_satisfiable_file_is_not_accepted(self):
        f = parse_dimacs("p cnf 1 1\nc\x0cp cnf 1 2\n1 0\nc\x0c-1 0\n")
        self.assertFalse(check_proof(f, "0\n", engine="python").ok)

    def test_a_proof_comment_ends_at_newline_only(self):
        for ch in self.BREAKS:
            with self.subTest(ch=repr(ch)):
                self.assertEqual(parse_proof(f"c x{ch}d 1 2 0\n"), [])

    def test_crlf_still_works(self):
        f = parse_dimacs("c x\r\np cnf 2 1\r\n1 2 0\r\n", strict=True)
        self.assertEqual(len(f.clauses), 1)
```
