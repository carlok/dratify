# drat_trim-5: a refutation stays refuted after a deletion undoes the propagation conflict

**Proposed severity: Note.** Sound, and `rate` 0.3.0 agrees with dratify on the verdict. It
is recorded because dratify's result differs from a literal replay of the clauses present.
`drat-trim` was not run.

## Minimal case

Formula `(1 2) (-1 2) (1 -2) (-1 -2)`, which is unsatisfiable. Proof:

```
1 0
d -1 -2 0
0
```

After `1`, propagation conflicts. Deleting `(-1 -2)` removes the conflict from the clauses
present, so `0` is not RUP on what remains.

## Reproducer and output

```python
from dratify import parse_dimacs, check_proof
from campaign import oracle

cnf = "p cnf 2 4\n1 2 0\n-1 2 0\n1 -2 0\n-1 -2 0\n"
r = check_proof(parse_dimacs(cnf), "1 0\nd -1 -2 0\n0\n", engine="python")
print(r.ok, r.rup_steps, r.deletions)       # True 2 1
F = [[1, 2], [-1, 2], [1, -2], [-1, -2]]
steps = [("a", (1,)), ("d", (-1, -2)), ("a", ())]
for flavour in oracle.FLAVOURS:
    print(flavour, oracle.replay(F, steps, flavour)[0][-1].acceptable)
# specified False
# operational True
# length-one False
```

The native engine returns the same. `rate` says `s VERIFIED` in all four modes.

## Why it is not a bug

The clause set was refuted by unit propagation at step 1. Every step up to there preserves
satisfiability, so the input is unsatisfiable, and `oracle.satisfiable(F)` confirms it. No
later deletion can change that, so `ok=True` is correct. The oracle's `operational` reading
treats this the same way: "every deletion is ignored once top-level propagation conflicts,
because the proof is over".

It does differ from the literal `length-one` reading, and `deletions=1` reports a deletion
that had no effect on the outcome. The README says nothing about this case. A sentence
there would settle it. Any fix of `drat_trim-1` should keep it in mind, since
`_root_conflict` (`src/dratify/proof.py:495`, 550-551) is what produces this behaviour.

## Counts

`note_sticky_refutation`, seeds 1, 2, 3: 4, 11, 9. The generator counts this once for the
oracle comparison and once per `rate` mode that disagrees.

## Test

A test that pins it:

```python
import unittest

from dratify import check_proof, parse_dimacs


class TestRefutationIsFinal(unittest.TestCase):
    def test_a_deletion_after_the_conflict_does_not_undo_it(self):
        cnf = "p cnf 2 4\n1 2 0\n-1 2 0\n1 -2 0\n-1 -2 0\n"
        r = check_proof(parse_dimacs(cnf), "1 0\nd -1 -2 0\n0\n", engine="python")
        self.assertTrue(r.ok)
```
