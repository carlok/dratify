# drat_trim-4: `rate`'s backward modes verify a proof with an invalid unused lemma

**Proposed severity: Note.** This is the difference the README documents for drat-trim,
seen here with `rate` 0.3.0's backward modes. `drat-trim` was not run.

## Minimal case

Formula `(1 2) (-1 2) (1 -2) (-1 -2) (-3 4)`, which is unsatisfiable. Proof:

```
-4 0
1 0
0
```

`-4` is neither RUP nor RAT on its first literal, and nothing needs it. `(-3 4)` is there to
stop `-4` being vacuously RAT: without that clause, or without that lemma, all four `rate`
modes verify, and the forward modes no longer disagree with the backward ones.

## Reproducer and output

```python
from dratify import parse_dimacs, check_proof
from campaign import oracle

cnf = "p cnf 4 5\n1 2 0\n-1 2 0\n1 -2 0\n-1 -2 0\n-3 4 0\n"
r = check_proof(parse_dimacs(cnf), "-4 0\n1 0\n0\n", engine="python")
print(r.ok, r.failed_step)      # False 1
F = [[1, 2], [-1, 2], [1, -2], [-1, -2], [-3, 4]]
print(oracle.replay(F, [("a", (-4,))], "length-one")[0][0].acceptable)   # False
print(oracle.satisfiable(F))    # False
```

The native engine returns the same. `rate`:

| flags | `rate` says |
|---|---|
| `-f -p` | `s NOT VERIFIED` |
| `-f -p -d` | `s NOT VERIFIED` |
| `-p` | `s VERIFIED` |
| `-p -d` | `s VERIFIED` |

## Why it is not a bug

The README ("What 'skip work' means") and `AGENTS.md` ("Checking is forward, not backward")
both state that a backward checker never examines an unused lemma and that dratify rejects
at the corrupted step. `rate`'s own forward mode agrees with dratify, which is what the
generator requires before it uses this explanation. The formula must also be unsatisfiable:
a backward checker that verifies a satisfiable formula is flagged, not explained.

The oracle brief's limit applies: `acceptable == False` does not mean every checker must
reject.

## Counts

Seed 1: 4 proofs in each of `-p` and `-p -d`, none in the forward modes.

## Suspected cause, and test

Forward checking by design. A test that pins it:

```python
import unittest

from dratify import check_proof, parse_dimacs


class TestUnusedInvalidLemma(unittest.TestCase):
    def test_forward_checking_rejects_it_where_it_stands(self):
        cnf = "p cnf 4 5\n1 2 0\n-1 2 0\n1 -2 0\n-1 -2 0\n-3 4 0\n"
        r = check_proof(parse_dimacs(cnf), "-4 0\n1 0\n0\n", engine="python")
        self.assertFalse(r.ok)
        self.assertEqual(r.failed_step, 1)
```
