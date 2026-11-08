# engines-1: ok=True on a satisfiable formula, on both engines

**Proposed severity: Critical.** dratify returns `ok=True` on a satisfiable formula.
The same defect as `deletion-1` and `root-1`, reached independently. It is reported
here because this corner's question is whether the two engines catch it: they do not,
because they agree.

## Minimal case

```
p cnf 2 2
1 0
-1 2 0
```

```
d -1 2 0
-2 0
0
```

Each of these makes both engines return `ok=False`: leaving out the deletion, leaving
out `-2 0`, leaving out `0`, leaving out the input clause `1`, or leaving out the input
clause `-1 2`.

## Reproducer

From the repo root:

```python
import cdclkit_native
from dratify import parse_dimacs, check_proof, register_native
from campaign import oracle

register_native(cdclkit_native)
f = parse_dimacs("p cnf 2 2\n1 0\n-1 2 0\n")
proof = "d -1 2 0\n-2 0\n0\n"
for engine in ("python", "native"):
    print(engine, check_proof(f, proof, engine=engine))

F = [[1], [-1, 2]]
S = [("d", [-1, 2]), ("a", [-2]), ("a", [])]
print(oracle.satisfiable(F))
for flavour in oracle.FLAVOURS:
    walk, _ = oracle.replay(F, S, flavour)
    print(flavour, [(s.clause, s.acceptable, s.preserves_sat) for s in walk])
```

## Actual output

```
python <CheckResult VERIFIED: empty clause derived and every step verified>
native <CheckResult VERIFIED: empty clause derived and every step verified>
```

Both report `steps=3, rup_steps=1, rat_steps=1, deletions=1, resolvents_checked=0`.

## What the oracle says

```
True
specified   [((-1, 2), True, None), ((-2,), True, True), ((), False, False)]
operational [((-1, 2), True, None), ((-2,), False, False)]
length-one  [((-1, 2), True, None), ((-2,), True, True), ((), False, False)]
```

`satisfiable(F)` is True: 1 and 2 true. No flavour accepts this proof.

- Under `length-one`, which is what dratify documents, the deletion happens and `-2` is
  vacuously RAT. The empty clause then fails: `{(1), (-2), ...}` is satisfiable, and
  `preserves_sat` is False. dratify should reject at step 3.
- Under `operational`, the deletion is ignored, `-2` is not RAT, and the walk stops at
  step 2. drat-trim follows this reading; it is not on PATH here, so that is the oracle's
  flavour and not a run of drat-trim.

## Reached under which flags

| check_rat | apply_deletions | python | native |
|---|---|---|---|
| True | True | ok=True | ok=True |
| True | False | ok=False | ok=False |
| False | True | ok=False | ok=False |
| False | False | ok=False | ok=False |

The sweep agrees: `sat-accepted` only under `check_rat=True, apply_deletions=True`, 1539
times per engine in the default run. That is the default for `check_proof`.

Under `check_rat=False, apply_deletions=True` the retained literal still accepts clauses
that are not RUP on the clauses present (1056 runs per engine). With RAT off every clause
follows from the input, so this should be harmless, and the sweep accepted no satisfiable
formula there.

## Suspected cause

Deletion removes a clause from the watches and from the RAT occurrence lists, but its
consequences stay in the root assignment, which is never undone. So RUP sees the literal
and RAT no longer sees the clause that implied it.

1. The deletion is applied: `src/dratify/proof.py:622-626`, `rust/src/checker.rs:451-457`.
   Only clauses with at most one distinct literal are spared.
2. RAT finds no candidate containing `2`, so `-2` is vacuously RAT:
   `src/dratify/proof.py:578`, `rust/src/checker.rs:397`.
3. The lemma is falsified by the literal that outlived its reason, which sets
   `_root_conflict`, after which everything is RUP: `src/dratify/proof.py:675-677` and
   `550-551`, `rust/src/checker.rs:518` and `362-364`.

The docstring argues "Ignoring a deletion is always sound" and that RUP is monotone. Both
are true, but the unsound case is the opposite one: the deletion was honoured for RAT and
not for the assignment. RUP alone cannot exploit that, since the retained literal is
implied by the input, which is why it takes RAT to get here.

Every run where an engine differed from the documented reference was reproduced exactly
by a second reference that keeps root literals past their reasons. 0 unexplained.

## Engines affected

Both, with identical results on every field. Comparing the engines cannot find this.

## Fix

Looks clear, and it needs the same change at the same place in both engines: ignore the
deletion of a clause that is the reason for a root literal, as drat-trim does. Testing for
exactly one true literal and the rest false at the root covers every reason clause, since
a reason has that shape, and a false positive only keeps an extra clause, which makes RAT
stricter and not looser.

This changes what `ignored_deletions` counts and what the documentation says about which
deletions are ignored. Undoing and re-propagating the root on deletion would be the other
reading, and is more work.

## Proposed test

Run against the current tree: `test_a_reason_cannot_be_deleted_and_then_denied` fails on
both engines with `True is not false`, and the other test passes.

```python
import unittest

from dratify import check_proof, parse_dimacs, register_native


class TestDeletingAReason(unittest.TestCase):
    FORMULA = "p cnf 2 2\n1 0\n-1 2 0\n"

    @classmethod
    def setUpClass(cls):
        cls.engines = ["python"]
        try:
            import cdclkit_native
        except ImportError:
            return
        register_native(cdclkit_native)
        cls.engines.append("native")

    @classmethod
    def tearDownClass(cls):
        register_native(None)

    def test_a_reason_cannot_be_deleted_and_then_denied(self):
        """1 and 2 satisfy this. Deleting (-1 2) must not leave 2 true for RUP
        while hiding it from RAT, or `-2` is vacuously RAT and falsified."""
        f = parse_dimacs(self.FORMULA)
        for engine in self.engines:
            with self.subTest(engine=engine):
                r = check_proof(f, "d -1 2 0\n-2 0\n0\n", engine=engine)
                self.assertFalse(r.ok)
                self.assertFalse(r.reached_empty)

    def test_the_same_proof_without_the_deletion_was_always_rejected(self):
        f = parse_dimacs(self.FORMULA)
        for engine in self.engines:
            with self.subTest(engine=engine):
                self.assertFalse(check_proof(f, "-2 0\n0\n", engine=engine).ok)
```
