# literals-7: `nvars` depends on literal order in a dropped tautology

**Proposed severity: Note.** The docstring is contradicted but no verdict changes: a dropped
clause adds nothing to check. The one observable effect beyond the count is that
`parse_dimacs(strict=True)` gives different answers for the same clause written in a
different order. The severity table has no row for this, and I would not call it a Bug.

## Minimal case and reproducer

```python
from dratify import parse_dimacs
for t in ("1 -1 2 0\n", "2 1 -1 0\n", "-1 1 4 0\n"):
    print(repr(t), parse_dimacs(t).nvars)
for t in ("p cnf 1 1\n1 -1 2 0\n", "p cnf 1 1\n2 1 -1 0\n"):
    try:
        f = parse_dimacs(t, strict=True); print(repr(t), "strict ok", f.nvars, f.clauses)
    except ValueError as ex:
        print(repr(t), "strict ValueError:", ex)
```

Actual output:

```
'1 -1 2 0\n' 1
'2 1 -1 0\n' 2
'-1 1 4 0\n' 1
'p cnf 1 1\n1 -1 2 0\n' strict ok 1 []
'p cnf 1 1\n2 1 -1 0\n' strict ValueError: header says 1 vars / 1 clauses, found 2 / 1
```

Expected: `CNF.add`'s docstring says "the variable count grows to cover every literal seen",
so `nvars` should be 2, 2 and 4, and both strict parses should agree. They should either both
raise, if a header must cover a dropped clause's variables, or both pass.

## Cause and engines

`src/dratify/cnf.py:155-163` (`CNF.add`). The loop returns at the first complement, before it
reaches the later literals, and it grows `nvars` as it goes, so the literals before the
complement count and those after do not. Parsing is in Python, so both engines see the same
`nvars`.

The effect on checking is small: `nvars` feeds the literal bound in `_validate_steps` and the
native `Checker::new` size, and a proof may still use the variable.

## Is the fix clear?

Yes: scan the whole clause for the maximum variable before returning, or grow `nvars` in a
first pass.

## Proposed failing test

Add to `tests/test_tautology_header.py`:

```python
    def test_a_dropped_tautology_still_counts_its_variables(self):
        for text in ("1 -1 2 0\n", "2 1 -1 0\n"):
            with self.subTest(text=text):
                f = parse_dimacs(text)
                self.assertEqual(f.clauses, [])
                self.assertEqual(f.nvars, 2)
```
