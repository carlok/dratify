# drat_trim-7: backward, drat-trim skips a RAT candidate not yet marked, so it accepts a used lemma

**Proposed severity: Note.** Forward against backward checking, in a form the README does not
spell out: drat_trim-4 is a lemma nothing uses, and this one is used. dratify and drat-trim's own
`-f` reject it. Checked with drat-trim at commit 2e3b2dc0ecf938addbd779d42877b6ed69d9a985.

## Minimal case

Formula `(-1 3) (2 3 4) (2 3 -4) (-2 5) (-2 -5) (-3 6) (-3 -6) (-1 7)`, which is unsatisfiable.
Proof:

```
1 2 0
3 0
0
```

`(3)` is RUP only through `(1 2)`. `(1 2)` is not RUP, is not RAT on 2, and is not RAT on 1, because
of the candidate `(-1 7)`: the resolvent `(2 7)` is not RUP. Nothing else uses `(-1 7)`. Remove that
clause and every checker here accepts the proof.

## Reproducer and output

```python
from dratify import parse_dimacs, check_proof
from campaign import oracle

cnf = ("p cnf 7 8\n-1 3 0\n2 3 4 0\n2 3 -4 0\n-2 5 0\n-2 -5 0\n-3 6 0\n-3 -6 0\n-1 7 0\n")
r = check_proof(parse_dimacs(cnf), "1 2 0\n3 0\n0\n", engine="python")
print(r.ok, r.failed_step)       # False 1
F = [[-1, 3], [2, 3, 4], [2, 3, -4], [-2, 5], [-2, -5], [-3, 6], [-3, -6], [-1, 7]]
print(oracle.rat(F, [1, 2], 1), oracle.rat(F, [1, 2], 2), oracle.satisfiable(F))
# False False False
print(check_proof(parse_dimacs(cnf), "d -1 7 0\n1 2 0\n3 0\n0\n", engine="python").ok)  # True
```

The native engine returns the same. drat-trim says `s VERIFIED` in its default mode and
`s NOT VERIFIED` in `-f`, at proof line 1.

## Why it is not a bug

`src/dratify/proof.py` says a RAT step is checked against the clauses present, and `(-1 7)` is
present. drat-trim.c 565-567 skips any candidate not marked active when it is in backward mode, so
only the clauses already used by later steps count. That is sound for the proof it trims, since an
unmarked clause can be deleted just before the lemma without touching anything that was checked.
Which is the test the generator applies: it inserts the deletion of each failing candidate before
the lemma, and counts the disagreement here only if dratify then accepts the proof and drat-trim's
verdict stays.

## Counts

Default mode: seed 1 1, seed 2
1, seed 3 0. None in
`-f`, as the source says. `--self-test` pins the example above.

## Suspected cause, and test

Forward checking by design. A test that pins it:

```python
import unittest

from dratify import check_proof, parse_dimacs


class TestRatSeesEveryCandidate(unittest.TestCase):
    CNF = "p cnf 7 8\n-1 3 0\n2 3 4 0\n2 3 -4 0\n-2 5 0\n-2 -5 0\n-3 6 0\n-3 -6 0\n-1 7 0\n"

    def test_an_unused_candidate_still_counts(self):
        r = check_proof(parse_dimacs(self.CNF), "1 2 0\n3 0\n0\n", engine="python")
        self.assertEqual((r.ok, r.failed_step), (False, 1))

    def test_deleting_it_first_is_enough(self):
        r = check_proof(parse_dimacs(self.CNF), "d -1 7 0\n1 2 0\n3 0\n0\n", engine="python")
        self.assertTrue(r.ok)
```
