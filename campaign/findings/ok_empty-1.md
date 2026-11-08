# ok_empty-1: `ok=True` on a satisfiable formula, by deleting a reason clause

**Proposed severity: Critical.** "dratify returns `ok=True` on a satisfiable
formula". Both engines, with default arguments, on text input.

## Minimal case

```
formula            proof
p cnf 2 2          d 1 2 0
-2 0               -1 0
1 2 0              0
```

The formula is satisfied by `1 -2`. Removing any one clause, literal or step makes
the result correct on both engines; each removal was run and judged by the oracle.

## Reproducer

Run from the repo root, with `cdclkit_native` installed:

```python
from dratify import parse_dimacs, check_proof, register_native
import cdclkit_native
from campaign import oracle

register_native(cdclkit_native)
F = [[-2], [1, 2]]
S = [("d", (1, 2)), ("a", (-1,)), ("a", ())]
formula = parse_dimacs("p cnf 2 2\n-2 0\n1 2 0\n")
for engine in ("python", "native"):
    r = check_proof(formula, "d 1 2 0\n-1 0\n0\n", engine=engine)
    print(engine, r.ok, r.reached_empty, repr(r.reason), r.rup_steps, r.rat_steps, r.deletions)
print("satisfiable", oracle.satisfiable(F))
for flavour in oracle.FLAVOURS:
    steps, final = oracle.replay(F, S, flavour)
    print(flavour, [(s.clause, s.acceptable) for s in steps], final)
```

Actual output:

```
python True True 'empty clause derived and every step verified' 1 1 1
native True True 'empty clause derived and every step verified' 1 1 1
satisfiable True
specified [((1, 2), True), ((-1,), True), ((), False)] [[-2], [-1]]
operational [((1, 2), True), ((-1,), False)] [[-2], [1, 2]]
length-one [((1, 2), True), ((-1,), True), ((), False)] [[-2], [-1]]
```

Expected: `ok=False`, `reached_empty=False`. No flavour of DRAT accepts the whole
proof. `specified` and `length-one` (dratify's documented rule) take the deletion
and the RAT step, then refuse `0`, because `-2, -1` does not propagate to a
conflict. `operational` keeps the clause and refuses `-1`. dratify takes the
permissive half of each: it removes the clause for the RAT check and keeps what
the clause implied for the RUP check.

## Suspected cause

The root assignment is never revisited (the docstring of `_add_lemma` says so), and
deleting a clause does not take back what it implied.

1. `src/dratify/proof.py:623`, `_erase`, removes `(1 2)` from `_occ` and the watches.
   `1` stays true at the root, with no clause left to justify it.
2. `src/dratify/proof.py:578`, `_is_rat`, looks for clauses holding `1`, finds none,
   and passes `(-1)` as vacuously RAT. This is right for the clauses present, and
   README says RAT is checked "against exactly the clauses present".
3. `src/dratify/proof.py:675-677`, `_add_lemma`: `-1` is false at the root, so the
   lemma is "falsified at the root" and `_root_conflict` is set.
4. `src/dratify/proof.py:550`, `_is_rup`, then passes `0`.

The Rust checker has the same steps: `rust/src/checker.rs:452`, `:397`, `:518`,
`:362`. The two share the design, so comparing them could not find this. The
comment at `checker.rs:445` reasons about exactly this for unit clauses ("cannot be
cleanly retracted"), and "Safe because RUP is monotone" is true of RUP. A clause
that is unit only under the root assignment has the same problem, and RAT is not
monotone. `check_step` tests only `len(lits) <= 1`.

Only `check_rat=True, apply_deletions=True` reaches it, which is the default. Each
flag alone closes it: with either off, this proof is rejected on both engines.

The same cause gives a milder symptom. On `-2 / 1 2 / -1 3`, the proof `d 1 2 0`,
`1 0` counts `(1)` under `rup_steps`, where the oracle says it is neither RUP nor RAT
on the clauses present and not implied by them. It does preserve satisfiability,
and it is implied by the input, so on its own it is not a wrong verdict. The
generator counts these as `accepted_beyond_length_one_retained`.

No honest solver is known to write this by accident. The harm is what the README
promises to guard against: a checker exists to distrust the proof, and here a
three-line proof can certify any satisfiable formula with a root-implied literal
whose reason has two or more literals.

## Fix

The hole looks clear, the choice of semantics is the author's.

- **Smallest:** the operational rule. Ignore a deletion when the clause has exactly
  one true literal and the rest false at the root, and count it in
  `ignored_deletions`. Every reason has that shape, so the clause stays and RAT sees
  it. Keeping extra clauses is safe, because it is plain DRAT over a larger multiset.
  It rejects at `-1`, as `operational` does. Some proofs that rely on such a deletion
  for a later RAT step would be rejected, and README's account of deletion would need
  rewriting. Both engines need it.
- **Alternative:** the specified rule, recomputing the root assignment after deleting
  a reason. It rejects at `0`, costs more, and has to undo a root conflict too (see
  ok_empty-3).

## Proposed failing test

The assertions pin only the verdict, so either fix passes.

```python
import unittest

from dratify import check_proof, parse_dimacs, register_native


def _engines():
    try:
        import cdclkit_native
    except ImportError:
        return ["python"]
    register_native(cdclkit_native)
    return ["python", "native"]


class TestADeletedReasonBuysNoRefutation(unittest.TestCase):
    FORMULA = "p cnf 2 2\n-2 0\n1 2 0\n"      # satisfied by 1 -2

    def test_the_refutation_is_refused(self):
        for engine in _engines():
            with self.subTest(engine=engine):
                r = check_proof(parse_dimacs(self.FORMULA),
                                "d 1 2 0\n-1 0\n0\n", engine=engine)
                self.assertFalse(r.ok)
                self.assertFalse(r.reached_empty)

    def test_the_control_without_the_deletion_is_refused(self):
        for engine in _engines():
            with self.subTest(engine=engine):
                r = check_proof(parse_dimacs(self.FORMULA),
                                "-1 0\n0\n", engine=engine)
                self.assertFalse(r.ok)
                self.assertEqual(r.failed_step, 1)


if __name__ == "__main__":
    unittest.main()
```
