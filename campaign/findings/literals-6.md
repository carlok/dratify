# literals-6: `1_0`, non-ASCII digits and NBSP are read as DIMACS

**Proposed severity: Note.** Nothing here reaches a wrong verdict on its own, because what
was parsed is what gets checked. It matters as a difference between the file dratify checks
and the file a solver read. `parse_proof`'s docstring says "anything that is not a clause
now raises", and these are not clauses in any DIMACS reader.

## Minimal case and reproducer

```python
from dratify import parse_dimacs, parse_proof
for t in ("1_0 0\n", "٣ 0\n", "１ 0\n", "1\xa02 0\n", "1 ٠ 2 0\n"):
    print(ascii(t), parse_dimacs(t).clauses, parse_proof(t))
```

Actual output:

```
'1_0 0\n' [(18,)] [('a', (18,))]
'٣ 0\n' [(4,)] [('a', (4,))]
'１ 0\n' [(0,)] [('a', (0,))]
'1\xa02 0\n' [(0, 2)] [('a', (0, 2))]
'1 ٠ 2 0\n' [(0,), (2,)] [('a', (0,)), ('a', (2,))]
```

Expected: `ValueError` naming the token, as `0x1`, `1e1` and `--1` already get. The last line
is the sharpest: ARABIC-INDIC DIGIT ZERO ends a clause, so one clause reads as two.

Spellings that remain fine, and that the generator confirms: `-0`, `+0`, `00`, `-00` as
terminators, and `+1`, `01`, `-01` as literals. These match `fscanf("%i")` for the zeros and
signs. I did not run drat-trim: it is not installed here. Note `%i` would read `010` as
octal 8 where `int()` reads 10; the generator does not test that.

## Cause and engines

`int(tok)` and `line.split()` at `src/dratify/cnf.py:318-320` and `src/dratify/proof.py:239-251`.
`int` accepts underscores and every Unicode decimal digit, and `str.split` splits on Unicode
spaces. Text is parsed once, in Python, so both engines inherit it.

## Is the fix clear?

Yes: match tokens against `[+-]?[0-9]+` before `int`, and split on ASCII whitespace.

## Proposed failing test

```python
class TestWhatATokenIs(unittest.TestCase):
    def test_python_int_syntax_is_not_dimacs(self):
        for text in ("1_0 0\n", "٣ 0\n", "1\xa02 0\n", "1 ٠ 2 0\n"):
            with self.subTest(text=ascii(text)):
                with self.assertRaises(ValueError):
                    parse_dimacs(text)
                with self.assertRaises(ValueError):
                    parse_proof(text)

    def test_the_spellings_of_zero_stay_terminators(self):
        for zero in ("-0", "+0", "00", "-00"):
            self.assertEqual(parse_dimacs(f"1 {zero}\n").clauses, [(0,)])
            self.assertEqual(parse_proof(f"1 {zero}\n"), [("a", (0,))])
```
