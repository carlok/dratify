# drat_trim-2: `rate` honouring a unit deletion rejects a proof dratify accepts

**Proposed severity: Note.** The two flavours of DRAT part here, and dratify is on the
documented side. The checker compared is `rate` 0.3.0. `drat-trim` was not run.

## Minimal case

Formula `(1) (-1 2 3) (-1 2 -3) (-1 -2 3) (-1 -2 -3)`, which is unsatisfiable. Proof:

```
d 1 0
2 0
0
```

Removing any one clause makes both dratify and every `rate` mode reject.

## Reproducer and output

```python
from dratify import parse_dimacs, check_proof
from campaign import oracle

cnf = "p cnf 3 5\n1 0\n-1 2 3 0\n-1 2 -3 0\n-1 -2 3 0\n-1 -2 -3 0\n"
r = check_proof(parse_dimacs(cnf), "d 1 0\n2 0\n0\n", engine="python")
print(r.ok, r.deletions, r.ignored_deletions)            # True 0 1
F = [[1], [-1, 2, 3], [-1, 2, -3], [-1, -2, 3], [-1, -2, -3]]
print(oracle.satisfiable(F))                              # False
steps = [("d", (1,)), ("a", (2,)), ("a", ())]
for flavour in oracle.FLAVOURS:
    print(flavour, [s.acceptable for s in oracle.replay(F, steps, flavour)[0]])
# specified   [True, True, False]
# operational [True, True, True]
# length-one  [True, True, True]
```

The native engine returns the same. `rate`:

| flags | `rate` says |
|---|---|
| `-f -p` | `s NOT VERIFIED` |
| `-p` | `s NOT VERIFIED` |
| `-f -p -d` | `s VERIFIED` |
| `-p -d` | `s VERIFIED` |

## Why it is not a bug

dratify documents ignoring unit deletions (`CHANGELOG.md` 0.1.0,
`tests/test_rat.py::test_unit_deletions_are_ignored_on_purpose`), and reports the decision
in `ignored_deletions`. The formula is unsatisfiable, so `ok=True` is right.

`rate`'s help gives `-d` as "Ignore deletion of unit clauses (drat-trim compatibility)". In
practice `-d` skips any clause unit at the root, not only clauses of one literal, as the
`d -1 2 0` case in `drat_trim-1` shows ("skipped deletions: 1"). So dratify's rule sits
between `rate`'s two readings. Where they differ on a longer reason clause, today's result
is `drat_trim-1`.

## Counts

Seed 1, per `rate` mode: `-f -p` 33 and `-p` 33 of these. `-f -p -d` and `-p -d` have none.
That is not only because `drat_trim-1` hides them under `follows_dratify_mismatch`: with the
oracle's `length-one` semantics standing in for dratify, on the same seed, those two modes
still show none. So none was observed, which does not show that none can exist.

## Suspected cause, and test

No cause to fix: `src/dratify/proof.py:619-621`, `rust/src/checker.rs:444-450`, as
documented. A test that pins the behaviour:

```python
import unittest

from dratify import check_proof, parse_dimacs


class TestUnitDeletionFlavour(unittest.TestCase):
    def test_an_ignored_unit_deletion_leaves_the_refutation_valid(self):
        cnf = "p cnf 3 5\n1 0\n-1 2 3 0\n-1 2 -3 0\n-1 -2 3 0\n-1 -2 -3 0\n"
        r = check_proof(parse_dimacs(cnf), "d 1 0\n2 0\n0\n", engine="python")
        self.assertTrue(r.ok)
        self.assertEqual((r.deletions, r.ignored_deletions), (0, 1))
```
