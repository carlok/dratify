# parsing-8: a comment or trailing spaces change whether a proof literal is allowed

**Proposed severity: Note here**, because the bound is documented in `_validate_steps` and
CHANGELOG. api-4, engines-3 and literals-3 report the rejection itself and propose Bug; this adds
only the parsing angle. `tests/fuzz.py` property 5 says re-flowing whitespace must not change what
a proof parses to. It does not change the parse, but it does change the outcome, and so does a comment.

## Minimal case

`p cnf 2 1\n1 2 0\n` with the proof `5000 0\n`, then the same with 5000 spaces after it.

## Reproducer

```python
from dratify import check_proof, parse_dimacs, register_native
from dratify.lits import from_dimacs
from campaign import oracle
import cdclkit_native
register_native(cdclkit_native)

f = parse_dimacs("p cnf 2 1\n1 2 0\n")
for proof in ("5000 0\n", "c " + "x" * 5000 + "\n5000 0\n", "5000 0\n" + " " * 5000):
    for engine in ("python", "native"):
        try:
            r = check_proof(f, proof, engine=engine)
            print(len(proof), engine, "rat_steps", r.rat_steps, "failed_step", r.failed_step)
        except ValueError as e:
            print(len(proof), engine, "ValueError", str(e)[:44])
print(oracle.rat([[1, 2]], [5000], 5000))

# text and a list differ too
g = parse_dimacs("\n")
print(check_proof(g, "3 0\n0\n", engine="python").failed_step)
try:
    check_proof(g, [("a", (from_dimacs(3),)), ("a", ())], engine="python")
except ValueError as e:
    print("list: ValueError", str(e)[:44])
```

```
7 python ValueError proof step 1: literal 5000 names variable 50
7 native ValueError proof step 1: literal 5000 names variable 50
5010 python rat_steps 1 failed_step -1
5010 native rat_steps 1 failed_step -1
5007 python rat_steps 1 failed_step -1
5007 native rat_steps 1 failed_step -1
True
2
list: ValueError proof step 1: literal 3 names variable 3, bu
```

The oracle says `(5000)` is RAT on its first literal. Nothing unsound happens either way: it raises,
or checks the step correctly.

## Suspected cause

`limit = formula.nvars + max(occurrences, text_len)` at `src/dratify/proof.py:736`. The comment's
"a proof can only introduce variables it mentions, so the largest index is at most..." assumes
dense numbering, which DRAT does not require. Both engines: this is checked before either runs.

A clear fix: add the floor the DIMACS parser already has, `max(..., HEADER_VARS_FLOOR)`, so that
any literal up to 2^20 is accepted whatever the text's length. A hostile literal is still refused
quickly, and a million variables is what `HEADER_VARS_FLOOR` already calls affordable.

## Proposed test

```python
import unittest

from dratify import check_proof, parse_dimacs


class TestTheBoundDoesNotReadTheLayout(unittest.TestCase):
    def test_padding_does_not_change_the_outcome(self):
        f = parse_dimacs("p cnf 2 1\n1 2 0\n")
        bare = check_proof(f, "5000 0\n", engine="python")
        padded = check_proof(f, "5000 0\n" + " " * 5000, engine="python")
        self.assertEqual(bare.rat_steps, padded.rat_steps)

    def test_a_hostile_literal_is_still_refused(self):
        with self.assertRaises(ValueError):
            check_proof(parse_dimacs("p cnf 1 0\n"), "99999999999 0\n", engine="python")
```
