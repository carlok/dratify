# api-2: deleting a reason clause leaves its root assignment, and buys a refutation

**Proposed severity: Critical.** `ok=True` on a satisfiable formula, from proof text, on
both engines. It is not specific to any API shape: every shape agrees on the wrong answer.
The generator hit it through its end-to-end check. It belongs as much to the deletion
corner as to this one, so expect it may be reported there too.

## Minimal case

Formula `(1) (-1 2)`, satisfiable. Proof `d -1 2 0`, `-2 0`, `0`. Without the deletion, step
1 is rejected; without `-2`, the empty clause is rejected.

## Reproducer

```python
import cdclkit_native
from dratify import parse_dimacs, check_proof, register_native
from campaign import oracle
register_native(cdclkit_native)
F = [[1], [-1, 2]]
proof = [("d", (-1, 2)), ("a", (-2,)), ("a", ())]
f = parse_dimacs("p cnf 2 2\n1 0\n-1 2 0\n")
for engine in ("python", "native"):
    r = check_proof(f, "d -1 2 0\n-2 0\n0\n", engine=engine)
    print(engine, r.ok, r.reason, r.deletions, r.rat_steps, r.rup_steps)
print("satisfiable", oracle.satisfiable(F))
for flavour in oracle.FLAVOURS:
    steps, _ = oracle.replay(F, proof, flavour)
    print(flavour, [(s.index, s.kind, s.applied if s.kind == "d" else s.acceptable) for s in steps])
print("dropping the deletion", check_proof(f, "-2 0\n0\n", engine="python").failed_step)
print("dropping -2", check_proof(f, "d -1 2 0\n0\n", engine="python").failed_step)
```

Actual output:

```
python True empty clause derived and every step verified 1 1 1
native True empty clause derived and every step verified 1 1 1
satisfiable True
specified [(1, 'd', True), (2, 'a', True), (3, 'a', False)]
operational [(1, 'd', False), (2, 'a', False)]
length-one [(1, 'd', True), (2, 'a', True), (3, 'a', False)]
dropping the deletion 1
dropping -2 2
```

Should be: rejected. Under the rule dratify documents (`length-one`), `-2` is acceptable,
since with `(-1 2)` gone it is vacuously RAT, but the empty clause is not: `(1) (-2)` has
no conflict. Under drat-trim's `operational` reading the deletion is ignored and `-2` is
rejected. No flavour accepts this proof. dratify mixes the two: the clause leaves the
store, so RAT finds no candidate, and its implication stays on the trail.

The generator's default run (6,000 instances, every flag setting) counted 6,275 shape
results of `ok=True` on a satisfiable formula and 204 accepted steps that do not preserve
satisfiability, all after a deletion that changed what propagates at the root. Most come
from a template aimed at this, so read those as "reached", not as a rate.

## Cause

`check_step` erases the clause (`src/dratify/proof.py:622-626`) and never retracts what it
implied: the root trail is never rewound, as the docstring of `_add_lemma` says
(`proof.py:652`). `_is_rat` then consults only live clauses (`proof.py:578-581`) while
`_add_lemma` reads the stale values and sets `_root_conflict` (`proof.py:675-677`). Same in
Rust: `rust/src/checker.rs:451-457` and `:517-518`. The module docstring's argument that
ignoring a deletion is safe is about RUP and does not cover this: here the deletion is
applied, for RAT, and ignored, for the root assignment, at once.

## Fix

The fix looks clear, the choice is the author's. Either ignore deleting a clause that is
unit under the root assignment, as drat-trim does, which is one test in both checkers and
needs the documented rule changed and `ignored_deletions` redefined; or rebuild the root
assignment on such a deletion, which is the `specified` flavour, and slow. Note the first
makes some `specified`-valid proofs rejected, which is the known flavour disagreement.

## Proposed test

```python
class TestDeletingAReason(unittest.TestCase):
    engine = "python"   # and a subclass with engine = "native", as test_proof_stream.py does

    def test_it_does_not_buy_a_refutation(self):
        f = parse_dimacs("p cnf 2 2\n1 0\n-1 2 0\n")
        r = check_proof(f, "d -1 2 0\n-2 0\n0\n", engine=self.engine)
        self.assertFalse(r.ok, r.reason)
```
