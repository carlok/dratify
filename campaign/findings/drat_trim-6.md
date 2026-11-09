# drat_trim-6: drat-trim tries every literal as the RAT pivot; dratify has only the first

**Proposed severity: Note.** dratify documents the first literal as the pivot, and the lemma
below is not RAT on it, so rejecting it is what dratify says it does. Checked with drat-trim at
commit 2e3b2dc0ecf938addbd779d42877b6ed69d9a985.

## Minimal case

Formula `(1 2) (-1 2) (1 -2) (-1 -2) (-3 5)`, which is unsatisfiable. Proof:

```
3 4 0
1 0
0
```

`(3 4)` is not RUP and is not RAT on 3, because the resolvent with `(-3 5)` is `(4 5)`. It is
vacuously RAT on 4, since nothing contains `-4`.

## Reproducer and output

```python
from dratify import parse_dimacs, check_proof
from campaign import oracle

cnf = "p cnf 5 5\n1 2 0\n-1 2 0\n1 -2 0\n-1 -2 0\n-3 5 0\n"
r = check_proof(parse_dimacs(cnf), "3 4 0\n1 0\n0\n", engine="python")
print(r.ok, r.failed_step)       # False 1
F = [[1, 2], [-1, 2], [1, -2], [-1, -2], [-3, 5]]
print(oracle.rup(F, [3, 4]), oracle.rat(F, [3, 4], 3), oracle.rat(F, [3, 4], 4))
# False False True
print(check_proof(parse_dimacs(cnf), "4 3 0\n1 0\n0\n", engine="python").ok)   # True
```

The native engine returns the same. drat-trim says `s VERIFIED` in its default mode and in `-f`,
and prints `c WARNING: RAT check on proof pivot failed : ... 3 4 0` in `-f`.

## Why it is not a bug

`src/dratify/proof.py` and the README state the first literal. The same proof with `4` written
first passes both checkers. So does what the generator checks on every such disagreement: it moves
the literal to the front, and only if dratify then accepts and drat-trim's verdict stays is the
disagreement counted here. `rate -p` rejects this proof in forward mode too, since `-p` asks it for
the first literal.

## The fallback is weaker than its message says

drat-trim.c 679-683 tries the other literals after the first fails. But when `checkRAT` fails it
resets `assigned` (608-610) and not `processed`, which `propagate` had moved on, so the next attempt
starts propagating past the literals it just assumed. A lemma that is RAT on its second literal can
then be refused:

```
p cnf 6 7                 2 1 0
-1 3 0                    3 0
2 3 4 0                   0
2 3 -4 0
-2 5 0
-2 -5 0
-3 6 0
-3 -6 0
```

`(2 1)` is RAT on 1, and written `1 2 0` both checkers accept the proof. As written, drat-trim says
`s NOT VERIFIED` in both modes with "RAT check failed on all possible pivots", and dratify rejects
step 1. They agree, for different reasons. In a scratch copy with `S->processed = S->forced;` added
in that branch, this says `s VERIFIED` in both modes, which confirms the cause. This only makes
drat-trim stricter, so it does not bear on soundness.

## Counts

Seed 1: 3 proofs in the default mode and 3 in `-f`. Seed 2: 2 and 3. Seed 3: 0 and 0, so
`--self-test` pins this example rather than the run requiring the category. A disagreement in the default mode that `-f` refused is counted under
drat_trim-4 instead, since then the fallback did not save the lemma.

## Suspected cause, and test

As documented on dratify's side. A test that pins it:

```python
import unittest

from dratify import check_proof, parse_dimacs


class TestPivotIsTheFirstLiteral(unittest.TestCase):
    CNF = "p cnf 5 5\n1 2 0\n-1 2 0\n1 -2 0\n-1 -2 0\n-3 5 0\n"

    def test_another_literal_is_not_tried(self):
        r = check_proof(parse_dimacs(self.CNF), "3 4 0\n1 0\n0\n", engine="python")
        self.assertEqual((r.ok, r.failed_step), (False, 1))

    def test_written_first_it_passes(self):
        r = check_proof(parse_dimacs(self.CNF), "4 3 0\n1 0\n0\n", engine="python")
        self.assertTrue(r.ok)
```
