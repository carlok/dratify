# literals-1: a deleted reason's root assignment survives, and refutes a satisfiable formula

**Proposed severity: Critical.** `ok=True` on a satisfiable formula, both engines.

The same root cause appears in this campaign's other result files: `api-2`,
`deletion-1`, `engines-1`, `root-1`. This corner reached it independently; expect one fix.

## Minimal case

```
formula: p cnf 2 2 / 1 2 0 / -2 0
proof:   d 1 2 0 / -1 0 / 0
```

Satisfiable: x1=true, x2=false. Removing any line makes it pass. Without `-2 0` there
is no root literal to go stale. Without the deletion, `-1` is not RAT. Without `-1 0`,
the empty clause is not RUP.

## Reproducer

```python
import cdclkit_native
from campaign import oracle
from dratify import check_proof, parse_dimacs, register_native
register_native(cdclkit_native)

f = parse_dimacs("p cnf 2 2\n1 2 0\n-2 0\n")
for e in ("python", "native"):
    r = check_proof(f, "d 1 2 0\n-1 0\n0\n", engine=e)
    print(e, r.ok, r.rup_steps, r.rat_steps, r.deletions, r.reason)

F = [[1, 2], [-2]]
print(oracle.satisfiable(F))
steps = [("d", [1, 2]), ("a", [-1]), ("a", [])]
for fl in oracle.FLAVOURS:
    s, cur = oracle.replay(F, steps, fl, stop_at_unacceptable=True)
    print(fl, [(x.kind, x.applied if x.kind == "d" else x.acceptable) for x in s], cur)
```

Actual output:

```
python True 1 1 1 empty clause derived and every step verified
native True 1 1 1 empty clause derived and every step verified
True
specified [('d', True), ('a', True), ('a', False)] [[-2], [-1]]
operational [('d', False), ('a', False)] [[1, 2], [-2]]
length-one [('d', True), ('a', True), ('a', False)] [[-2], [-1]]
```

Expected: `ok=False`. No flavour reaches the empty clause:

- `specified` and `length-one` (the rule dratify documents) accept `-1` and then
  reject `0`, because `{-2, -1}` is satisfiable.
- `operational` (drat-trim's reading) ignores the deletion and rejects `-1`.

dratify's behaviour matches none of the three: it applies the deletion to the clause
store and ignores it in the root assignment.

## Why

1. `-2 0` is a unit, and propagating it assigns x1 true at the root. `(1 2)` is the reason.
2. `d 1 2 0` has two literals, so it is not a unit deletion. It is erased from the store,
   but x1 stays true: the root trail is never retracted.
3. `-1 0` is not RUP. It is RAT on -1, vacuously, because the only clause containing x1
   has gone. So it is accepted.
4. `_add_lemma` sees every literal of `(-1)` false under the stale root and sets
   `_root_conflict`. From then on every clause is RUP, including the empty one.

The module docstring's safety argument is that keeping more clauses is safe because RUP
is monotone, and that RAT "is checked against exactly the clauses present". Here the two
halves meet: RAT's candidates come from the smaller multiset, and its verdict lands on the
larger assignment.

## Cause and engines

- `src/dratify/proof.py:622-626` (`check_step`, the erase) and `:667-682` (`_add_lemma`).
- `rust/src/checker.rs:451-457` and `:500-530`, the same two places.
- Both engines are affected and agree, so differential testing cannot see it.

## Is the fix clear?

The direction is clear, the choice is the author's:

- **Ignore the deletion when the clause is the reason for a root literal**, as drat-trim
  does in operational mode, and count it in `ignored_deletions`. This is small, and it
  rejects the proof at `-1 0`. It changes what the docs say about which deletions are
  ignored.
- **Recompute the root assignment after such a deletion**, which gives the `length-one`
  reading exactly. It is correct by the oracle but costs a re-propagation on each one.

Either way the module docstring and README's "Deletion" paragraph need the rule stated.
A RUP lemma accepted only through a stale literal (`deletion-2`) goes away with either fix.

## Reach in this generator

Label `stale-root`, 1054 occurrences on seeds 1, 2, 3, from the `strand` action and also
from ordinary random deletions. Repeated literals do not change it: `d 2 1 1 0` is the
same deletion.

## Proposed failing test

```python
class TestDeletedReason(unittest.TestCase):
    engine = "python"

    def test_a_deleted_reason_does_not_leave_its_literal_behind(self):
        # x1=true, x2=false satisfies this, so no proof may refute it
        f = parse_dimacs("p cnf 2 2\n1 2 0\n-2 0\n")
        r = check_proof(f, "d 1 2 0\n-1 0\n0\n", engine=self.engine)
        self.assertFalse(r.ok, r.reason)
        self.assertFalse(r.reached_empty)
```

Run it on both engines, in the style of `tests/test_repeated_literals.py`.
