# root-1: a deleted reason clause leaves its literal assigned, and a satisfiable formula is "refuted"

**Proposed severity: Critical.** `ok=True` on a satisfiable formula, both engines.

## Minimal case

Formula `(1) (-1 2)`, model `1 2`. Proof:

```
d -1 2 0
-2 0
0
```

Removing anything makes it pass: without the deletion `-2` is rejected at step 1,
without `-2` the `0` is rejected at step 2, without the `0` the result is
`ok=False` ("never derives"), and without either input clause the `0` is rejected
at step 3.

## Reproducer

```python
import cdclkit_native
from dratify import check_proof, parse_dimacs, register_native
from campaign import oracle
register_native(cdclkit_native)

cnf, proof = "p cnf 2 2\n1 0\n-1 2 0\n", "d -1 2 0\n-2 0\n0\n"
for e in ("python", "native"):
    r = check_proof(parse_dimacs(cnf), proof, engine=e)
    print(e, r.ok, r.reached_empty, r.rup_steps, r.rat_steps, r.deletions, r.reason)

F, S = [[1], [-1, 2]], [("d", [-1, 2]), ("a", [-2]), ("a", [])]
print(oracle.satisfiable(F))
for flavour in oracle.FLAVOURS:
    steps, cur = oracle.replay(F, S, flavour)
    print(flavour, [(s.index, s.acceptable) for s in steps], cur)
```

## Actual

```
python True True 1 1 1 empty clause derived and every step verified
native True True 1 1 1 empty clause derived and every step verified
```

## What the oracle says

```
True                                              # satisfiable(F)
specified   [(1, True), (2, True), (3, False)]  [[1], [-2]]
operational [(1, True), (2, False)]             [[1], [-1, 2]]
length-one  [(1, True), (2, True), (3, False)]  [[1], [-2]]
```

No flavour accepts the proof. Under `specified` and `length-one`, which is what
dratify documents, `-2` is RAT and the `0` is not RUP against `(1) (-2)`:
`preserves_sat` is False for it. Under `operational` the deletion is ignored, and
`-2` is rejected at step 2.

## The same cause, without a false refutation

An accepted step that does not preserve satisfiability, on the satisfiable
`(2) (4 3) (-4 -2) (-3 1)`, proof `d -3 1 0`, `-1 0`, `4 0`. The oracle under
`length-one` says `(4)` is neither RUP nor RAT against `(2) (4 3) (-4 -2) (-1)` and
`preserves_sat` is False. dratify accepts it (`failed_step=-1`, on both engines), by
RUP, because the root is already marked conflicting after `-1`.

A correct answer can also be reached by an invalid proof: instance 9854 is an
unsatisfiable formula whose proof dratify accepts with a step the oracle rejects.

The harness labels 1,055 further mismatches `stale-root:counts-differ`: the verdict
agrees and a step is counted as RUP where the oracle says RAT. These are harmless
alone. They are the same stale assignment.

## How often

Seed 20261108 and the exhaustive pass: 425 false refutations. All 425 had a reason
deletion earlier in the proof. Every one is in the default mode (`check_rat=True`,
`apply_deletions=True`): it takes RAT and deletion together. With either off, the
minimal case is rejected at step 2.

Measured in the random sweep alone: 377 false refutations in the default mode and
none in the other three modes. The label is reported once when both engines return
the same verdict, and `engine_comparisons` confirms they do.

The exhaustive pass over at most 3 clauses on 2 variables found 48 such
(formula, proof) pairs.

## Suspected cause

The root assignment is never retracted, and the clause store is. A deletion of two
or more literals removes the clause from the watches and the occurrence lists and
leaves the literals it implied on the trail.

| | Python `src/dratify/proof.py` | Rust `rust/src/checker.rs` |
|---|---|---|
| the deletion removes the clause, not its implication | 622-626 | 451-457 |
| RAT sees only live clauses, so `-2` is vacuously RAT | 578-581 | 397-401 |
| the lemma is false under the stale root, so "refuted outright" | 675-677 | 518 |
| everything passes from then on, including `0` | 550-551 | 362-364 |

The rule that protects unit deletions (`len(lits) <= 1`, proof.py:619) does not
reach this: `(-1 2)` has two literals, and it is a reason exactly as `(1)` is. The
Rust comment at checker.rs:445-447 states the reason for that rule ("cannot be
cleanly retracted"), which applies to any clause the root rests on. And "Safe
because RUP is monotone" does not extend to RAT, as README.md's "RAT is not
monotone, so RAT steps are checked against exactly the clauses present" says: here
the candidates are the present clauses, and the root assignment is not.

Not bisected. RUP-only checking is unaffected in verdict, since everything accepted
is implied by the input.

## Whether the fix looks clear

The direction is clear and there are two options. It is the orchestrator's call.

1. **Ignore a deletion of a clause that is unit at the root**, as drat-trim does: if
   the clause has one true literal and the rest false, count it in
   `ignored_deletions` and keep it, so RAT sees it as a candidate and `-2` is
   rejected. It is small, and the same in both engines. It over-approximates the
   reason test, which keeps more clauses: the safe direction for soundness, but it
   can reject a proof valid under `specified`.
2. Retract and recompute the root on deleting a true reason. That matches the
   documented rule exactly, and costs more.

Option 1 was tried as a test subclass, not in the source
(`IgnoresPseudoUnitDeletions` in `campaign/gen_root.py`, which also ignores deletions
after a root conflict): the Python checker with it gives **zero mismatches** over the
default 30,000 instances and the exhaustive pass. Either choice should be documented
in README.md's "What it checks", which says only that deletion is applied.

## Proposed failing test

Passes under either fix, and fails now on both engines (confirmed by running it).

```python
# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Deleting a clause does not retract what it implied at the root."""

from __future__ import annotations

import unittest

from dratify import check_proof, parse_dimacs, register_native


def _native():
    try:
        import cdclkit_native as impl
    except ImportError:
        return None
    return impl


class TestDeletedReason(unittest.TestCase):
    engine = "python"

    def test_a_satisfiable_formula_is_not_refuted_through_a_deleted_reason(self):
        f = parse_dimacs("p cnf 2 2\n1 0\n-1 2 0\n")     # 1, 2 is a model
        r = check_proof(f, "d -1 2 0\n-2 0\n0\n", engine=self.engine)
        self.assertFalse(r.ok, r.reason)
        self.assertFalse(r.reached_empty)

    def test_a_step_that_is_not_satisfiability_preserving_is_rejected(self):
        f = parse_dimacs("p cnf 4 4\n2 0\n4 3 0\n-4 -2 0\n-3 1 0\n")
        r = check_proof(f, "d -3 1 0\n-1 0\n4 0\n", engine=self.engine)
        self.assertIn(r.failed_step, (2, 3), r.reason)


@unittest.skipIf(_native() is None,
                 "no native checker installed; CI installs cdclkit-native")
class TestDeletedReasonNative(TestDeletedReason):
    engine = "native"

    @classmethod
    def setUpClass(cls):
        register_native(_native())

    @classmethod
    def tearDownClass(cls):
        register_native(None)


if __name__ == "__main__":
    unittest.main()
```
