# rat-1: a RAT step leans on a root assignment whose reason was deleted, and a satisfiable formula is "refuted"

**Proposed severity: Critical.** `check_proof` returns `ok=True` on a satisfiable
formula, on both engines, from text input and default arguments. Same root cause as
`deletion-1`, `deletion-2`, `root-1`, `engines-1`, `literals-1`, `api-2`, `ok_empty-1` and
`ok_empty-3`, found independently. What this corner adds is the RAT side: why it takes a
RAT step, and that nothing else in the RAT corner is wrong (see "Evidence").

## Minimal case

Formula `(1) (-1 2)`, satisfied by 1=true, 2=true. Proof:

```
d -1 2 0
-2 0
0
```

Removing anything makes it pass. Run on both engines:

| removed | result |
|---|---|
| clause `(1)` | `ok=False`, `failed_step=3` |
| clause `(-1 2)` | `ok=False`, `failed_step=3` |
| `d -1 2 0` | `ok=False`, `failed_step=1` |
| `-2 0` | `ok=False`, `failed_step=2` |
| `0` | `ok=False`, no empty clause |

## Reproducer

```bash
python - <<'EOF'
from campaign import oracle
from dratify import check_proof, parse_dimacs, register_native
import cdclkit_native; register_native(cdclkit_native)
F = [[1], [-1, 2]]
STEPS = [("d", [-1, 2]), ("a", [-2]), ("a", [])]
for e in ("python", "native"):
    r = check_proof(parse_dimacs("p cnf 2 2\n1 0\n-1 2 0\n"), "d -1 2 0\n-2 0\n0\n", engine=e)
    print(e, r.ok, r.reached_empty, r.reason, "rup", r.rup_steps, "rat", r.rat_steps,
          "del", r.deletions)
print("satisfiable", oracle.satisfiable(F))
for fl in oracle.FLAVOURS:
    judged, final = oracle.replay(F, STEPS, fl)
    print(fl, [(s.kind, s.clause, s.rup, s.rat_on_first, s.preserves_sat) for s in judged], final)
EOF
```

Actual output:

```
python True True empty clause derived and every step verified rup 1 rat 1 del 1
native True True empty clause derived and every step verified rup 1 rat 1 del 1
satisfiable True
specified   [('d', (-1, 2), None, None, None), ('a', (-2,), False, True, True), ('a', (), False, None, False)] [[1], [-2]]
operational [('d', (-1, 2), None, None, None), ('a', (-2,), False, False, False)] [[1], [-1, 2]]
length-one  [('d', (-1, 2), None, None, None), ('a', (-2,), False, True, True), ('a', (), False, None, False)] [[1], [-2]]
```

**What it should be:** `ok=False`. Every flavour refuses the proof. Under `length-one`,
the one dratify documents, and under `specified`, `-2` is vacuously RAT and is rightly
accepted, then `0` is not RUP: `(1) (-2)` propagates 1 and -2 and stops, and
`preserves_sat` is False. Under `operational` (drat-trim's reading) the deletion is
ignored and `-2` is refused at once. The primary rule decides it whichever flavour is
meant: `oracle.satisfiable(F)` is True and `ok` is True.

## Why it takes a RAT step

- The root assignment is never undone. `_erase` removes a clause from the watch and
  occurrence lists and leaves `prop.trail` and `prop.val` alone.
- The RAT candidates **are** current: `_occ` loses the deleted clause. So after
  `d -1 2 0` nothing contains `2`, `-2` is vacuously RAT by the rule, and the checker has
  two beliefs that contradict: "2 is true at the root" and "`-2` is a legal addition".
- `_add_lemma` then finds every literal of `-2` false at the root, concludes "falsified
  at the root: the clause set is now refuted outright" and sets `_root_conflict`.
  `_is_rup` answers True from then on, so `0` passes.

In a checker without this defect a RAT lemma cannot be falsified at the root: the literal
making the pivot false rests on a clause containing the pivot's negation, and that
clause's resolvent is not RUP. So `_add_lemma`'s falsified branch is reached on a
satisfiable formula only through a stale assignment.

RUP alone cannot do this. Without RAT every step is implied by the input, stale or not, so
`check_rat=False` stays sound. It can still accept a step not RUP on the clauses present:
formula `1 / -1 2 / -2 3 / -3 4` with `d -1 2 0` then `3 0` reports `rup_steps=1`, where
the oracle's `length-one` says neither RUP nor RAT and `operational` says RUP.

A root conflict sticks in the same way: on `(1 2) (-1 2) (1 -2) (-1 -2)`, the proof
`2 0`, `d 1 -2 0`, `0` is accepted though `0` is not RUP after that deletion. That formula
is unsatisfiable, so the verdict is right; `operational` agrees with it and `length-one`
does not.

## Suspected cause

The comment at `src/dratify/proof.py:41-50` handles the right problem for one case: "A
unit that has already been propagated into the checker's root assignment cannot be cleanly
retracted", so unit deletions are ignored. A clause of two or more literals that is the
reason for a root literal has the same property and is deleted.

- Python: `check_step` at `src/dratify/proof.py:618-627`, `_erase` at `:524-537`, the
  falsified branch at `:675-677`, the short-circuit at `:550-551`.
- Rust: `check_step` at `rust/src/checker.rs:443-458`, `erase` at `:322-348`, the falsified
  arm at `:518`, the short-circuit at `:362-364`.

**Engines:** both, identically, including every counter.

## Is the fix clear?

The defect is clear. There are two fixes, and which one is a decision about flavour:

1. **Ignore the deletion of a clause that is pseudo-unit at the root**, as drat-trim does
   in its default mode, and count it in `ignored_deletions`. The clause stays, so it stays
   a RAT candidate and the root assignment stays honest. Small and local to `check_step`
   in both engines. With this fix `-2 0` above is refused at step 2. It contradicts the
   README's "RAT steps are checked against exactly the clauses present" only as much as
   ignoring unit deletions already does; the rule would have to say so.
2. **Honour the deletion and rebuild the root assignment**, the `specified` reading. More
   code and a cost per reason deletion, and it rejects proofs drat-trim accepts, such as
   `1 / -1 2 / -2 3 / -3 4` with `d -1 2 0`, `3 0`.

Option 1 looks better, and it holds up. A scratch subclass of `DRATChecker` (Python only,
nothing in `src/` touched) that ignores a deletion when the clause has one true literal and
the rest false at the root, or once the root has conflicted, gave **zero mismatches**
against `--flavour operational` on 4,000 instances of this generator (seed 20261108, 53,256
steps judged), with no `ok=True` on a satisfiable formula. That shows the defect is this and
that the rule closes it. It says nothing about the Rust side, which would need the same
change.

On 730 proofs from cadical and kissat on 365 unsatisfiable formulas of at most 16 variables
(7,641 steps, all of which pass all three flavours and dratify), neither solver deleted a
root reason, so this sample does not separate the two options. It is small and these
formulas are tiny, so that says little about large proofs.

After option 1 this generator's default `length-one` reading will disagree with the
checker by design; run `python -m campaign.gen_rat --flavour operational`. Note that
`oracle.is_pseudo_unit` over-approximates a reason test, so a checker using true reasons
may differ from that flavour on clauses that only look like a reason.

## Evidence

`python -m campaign.gen_rat` (see `campaign/results/rat.json` for the counts). Every
mismatch labelled `rat-1` is one where `model_check(stale=True)`, a model of exactly this
defect on the oracle's primitives, predicts every field the checkers reported, except
`resolvents_checked` on a rejected step, which depends on candidate order. In the
70% of instances that never delete a root reason (`no-stale`) there are no `rat-1`
mismatches and no unexplained ones: with the stale assignment out of the way the RAT rule
agreed with the oracle on the pivot, candidates, tautological resolvents and counters.

## Proposed test

Run from a scratch copy, all three subtests fail today on each engine.

```python
import unittest

from dratify import check_proof, parse_dimacs, register_native


def _native():
    try:
        import cdclkit_native as impl
    except ImportError:
        return None
    return impl


class TestDeletingARootReason(unittest.TestCase):
    """A root literal rests on a clause; deleting that clause takes the support."""

    engine = "python"
    REFUTATIONS = {
        "lemma falsified outright": ("p cnf 2 2\n1 0\n-1 2 0\n",
                                     "d -1 2 0\n-2 0\n0\n"),
        "two lemmas": ("p cnf 3 2\n1 0\n-1 2 0\n",
                       "d -1 2 0\n-2 3 0\n-2 -3 0\n0\n"),
        "longer chain": ("p cnf 3 3\n1 0\n-1 2 0\n-2 3 0\n",
                         "d -1 2 0\nd -2 3 0\n-3 0\n0\n"),
    }

    def test_no_refutation_of_a_satisfiable_formula(self):
        for name, (cnf, proof) in self.REFUTATIONS.items():
            with self.subTest(name):
                r = check_proof(parse_dimacs(cnf), proof, engine=self.engine)
                self.assertFalse(r.ok, "every one of these formulas is satisfiable")


@unittest.skipIf(_native() is None, "no native checker installed")
class TestDeletingARootReasonNative(TestDeletingARootReason):
    engine = "native"

    @classmethod
    def setUpClass(cls):
        register_native(_native())

    @classmethod
    def tearDownClass(cls):
        register_native(None)
```
