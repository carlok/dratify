# ok_empty-3: a top-level conflict survives the deletion of the clauses behind it

**Proposed severity: Note.** A difference between flavours of DRAT with no wrong verdict:
every formula it was seen on is unsatisfiable. It is not the same as ok_empty-1, where
the conflict exists only because of a deleted reason.

## Minimal case

```
formula            proof
p cnf 2 4          1 0
1 2 0              d -1 2 0
1 -2 0             0
-1 2 0
-1 -2 0
```

The four clauses are the smallest unsatisfiable formula on two variables that unit
propagation alone does not refute. Dropping a clause makes it satisfiable and the proof
is rejected. Dropping the deletion makes the proof valid under every flavour.

## Reproducer

Run from the repo root, with `cdclkit_native` installed:

```python
from dratify import parse_dimacs, check_proof, register_native
import cdclkit_native
from campaign import oracle

register_native(cdclkit_native)
F = [[1, 2], [1, -2], [-1, 2], [-1, -2]]
S = [("a", (1,)), ("d", (-1, 2)), ("a", ())]
f = parse_dimacs("p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n")
for engine in ("python", "native"):
    r = check_proof(f, "1 0\nd -1 2 0\n0\n", engine=engine)
    print(engine, r.ok, r.reached_empty, r.steps, r.deletions)
print("satisfiable", oracle.satisfiable(F))
for flavour in oracle.FLAVOURS:
    steps, _ = oracle.replay(F, S, flavour)
    print(flavour, [(s.clause, s.acceptable) for s in steps])
```

Actual output:

```
python True True 3 1
native True True 3 1
satisfiable False
specified [((1,), True), ((-1, 2), True), ((), False)]
operational [((1,), True), ((-1, 2), True), ((), True)]
length-one [((1,), True), ((-1, 2), True), ((), False)]
```

So dratify agrees with `operational` here and not with `length-one`, the rule it
documents. It counts the deletion as applied (`deletions=1`) although it no longer has any
effect on the conflict. `ok=True` is correct: the clauses were refuted before the deletion,
and a deletion only weakens a formula, so the input is unsatisfiable.

## Cause

`_root_conflict` is set once and `_is_rup` returns True from then on
(`src/dratify/proof.py:550`, `rust/src/checker.rs:362`).

## What to do

Nothing is needed for soundness. If ok_empty-1 is fixed with the operational rule, this
becomes consistent, and README can say so. If it is fixed with the specified rule, this
has to change with it.

## Proposed test

This passes today, and pins the current behaviour. It stays right if ok_empty-1 is fixed
with the operational rule, except that `deletions` may need revisiting. Under the specified
rule, the verdict becomes `assertFalse`.

```python
import unittest

from dratify import check_proof, parse_dimacs


class TestAConflictOutlivesItsClauses(unittest.TestCase):
    def test_the_empty_clause_passes_after_a_deletion(self):
        f = parse_dimacs("p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n")
        r = check_proof(f, "1 0\nd -1 2 0\n0\n", engine="python")
        self.assertTrue(r.ok)
        self.assertEqual(r.deletions, 1)


if __name__ == "__main__":
    unittest.main()
```
