# deletion-1: ok=True on a satisfiable formula, after deleting a reason clause

**Proposed severity: Critical.** `dratify` returns `ok=True` on a satisfiable
formula, on both engines, from text proof input and default arguments.

## Minimal case

Formula `(1) (-1 2)`, satisfied by 1=true, 2=true. Proof:

```
d -1 2 0
-2 0
0
```

Removing anything makes it pass, meaning the checker then rejects or reports no
refutation: without the `(1)`, without the `(-1 2)`, without the deletion, without
`-2 0` (the `0` is rejected), and without the `0` (`ok=False`, no empty clause).

## Reproducer

```bash
python - <<'EOF'
from campaign import oracle
from dratify import check_proof, parse_dimacs, register_native
import cdclkit_native; register_native(cdclkit_native)
FORMULA = "p cnf 2 2\n1 0\n-1 2 0\n"
PROOF = "d -1 2 0\n-2 0\n0\n"
F = [[1], [-1, 2]]
STEPS = [("d", [-1, 2]), ("a", [-2]), ("a", [])]
print("satisfiable:", oracle.satisfiable(F))
for engine in ("python", "native"):
    r = check_proof(parse_dimacs(FORMULA), PROOF, engine=engine)
    print(engine, r.ok, r.reached_empty, r.rup_steps, r.rat_steps, r.deletions)
for flavour in oracle.FLAVOURS:
    judged, _ = oracle.replay(F, STEPS, flavour)
    print(flavour, [(s.clause, s.acceptable) for s in judged])
EOF
```

Actual output:

```
satisfiable: True
python True True 1 1 1
native True True 1 1 1
specified [((-1, 2), True), ((-2,), True), ((), False)]
operational [((-1, 2), True), ((-2,), False)]
length-one [((-1, 2), True), ((-2,), True), ((), False)]
```

**Every reading of deletion refuses this refutation.** Under `length-one`, which
dratify documents, and under `specified`, step 2 is fine (it is RAT on `-2`, with
nothing left containing `2`) and step 3 is not: `(1) (-2)` is satisfiable. Under
`operational`, the deletion of the reason is ignored, and step 2 is rejected. dratify
takes the deletion from the first and the root assignment from the second.

With `check_rat=False` or `apply_deletions=False` the same proof is rejected at step 2.

## Cause

Both engines keep a root assignment that is only ever extended. Deleting a clause of
two or more literals removes it from the watches and the occurrence lists, but its
implied literal stays true at the root, even when this clause was its reason. The
checker now holds a literal that nothing in its clause set supports.

1. `(1)` and `(-1 2)` make 2 true at the root.
2. `d -1 2 0` removes the clause; 2 stays true.
3. `-2 0` is not RUP. As RAT on `-2` it looks at clauses containing `2`, and there are
   none, so it passes vacuously. The candidates come from the clauses, while its
   pivot's falsity comes from the root assignment, and the two have come apart.
4. `_add_lemma` finds every literal of `(-2)` false at the root, so it sets
   `_root_conflict`, and from then on `_is_rup` returns True for everything.

Python, `src/dratify/proof.py`: `check_step` deletion path, lines 618-627; `_is_rat`,
lines 575-578; `_add_lemma`, line 676. Rust, `rust/src/checker.rs`: `check_step`
deletion path around line 452; `is_rat` around line 397; `add_lemma`, line 518.

The justification in the module docstring (proof.py lines 41-50, and the note in
README.md line 168) covers *ignored* deletions and says RAT is checked "against exactly
the clauses present". It does not consider an *applied* deletion of a clause whose
consequence stays in the root assignment. The rule tests for length one, where the
reason it gives ("a unit that has already been propagated into the root assignment")
applies equally to any reason clause.

The sweep found no `ok=True` on a satisfiable formula except after accepting a RAT
step whose pivot was false at the root: `ok_on_sat` without that label stayed at 0.

## Fix

The direction is clear, with one decision to make. Either:

- **Ignore the deletion of a clause that is unit under the root assignment**, and count
  it in `ignored_deletions`. This is the `operational` flavour, and what the oracle
  describes for drat-trim. Tried in a scratch subclass of `DRATChecker` (not in the
  tree), on 8,000 instances of this generator: `ok=True` on a satisfiable formula went
  from present to 0. It also over-approximates a reason, like `oracle.is_pseudo_unit`,
  which is safe. The cost is that some steps RAT under `length-one` become rejected.
- Or **retract the literal**, re-propagating the root after deleting a reason. This is
  the `specified` flavour, is what the current docs literally promise, and may reject
  real solver proofs that rely on the literal surviving. Not tried.

Taking the first means changing the documented rule, and the harness along with it:
`_judge_deletion` and `Builder` in `campaign/gen_deletion.py` model `length-one`, so
they would report `deletion_counters` and `false_rejection` on steps such as
`(-3) (3 -2)`, `d 3 -2 0`, `2 0` until they model the new rule. Those steps are
RAT under `length-one` but not under `operational`, so this is the rule changing and
not a regression. Both engines need the same change.

## Proposed failing test

```python
class TestReasonDeletion(unittest.TestCase):
    """Deleting a reason clause must not leave a refutable root assignment."""

    engine = "python"
    FORMULA = "p cnf 2 2\n1 0\n-1 2 0\n"     # satisfiable: 1 and 2 true

    def test_a_refutation_of_a_satisfiable_formula_is_refused(self):
        r = check_proof(parse_dimacs(self.FORMULA), "d -1 2 0\n-2 0\n0\n",
                        engine=self.engine)
        self.assertFalse(r.ok, "the formula is satisfiable")
        self.assertFalse(r.reached_empty)


@unittest.skipIf(_native() is None, "no native checker installed")
class TestReasonDeletionNative(TestReasonDeletion):
    engine = "native"

    @classmethod
    def setUpClass(cls):
        register_native(_native())

    @classmethod
    def tearDownClass(cls):
        register_native(None)
```

`_native` is the helper in `tests/test_root_units.py`.
