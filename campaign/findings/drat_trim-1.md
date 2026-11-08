# drat_trim-1: `ok=True` on a satisfiable formula, which `rate` rejects in every mode

**Proposed severity: Critical.** dratify returns `ok=True` on a satisfiable formula, on
both engines, from proof text with default arguments.

This is the same defect as `deletion-1` and `root-1`, reached independently. What this
file adds is the external comparison and the measurement of real solver proofs below.
Everything external here is `rate` 0.3.0. drat-trim was built later, at commit 2e3b2dc: it
says `s NOT VERIFIED` on this proof in its default mode, in `-f` and in `-S`, and `-W` stops
it with exit 80 at the deletion it ignores (`drat_trim-11`).

## Minimal case

Formula `(1) (-1 2)`, satisfied by 1=true, 2=true. Proof:

```
d -1 2 0
-2 0
0
```

Removing either clause or any step makes dratify reject (checked for the clauses by
script, and for the steps by reasoning: `-2` is neither RUP nor RAT without the deletion,
and without `-2` or `0` there is no refutation).

## Reproducer

From the repository root:

```python
from dratify import parse_dimacs, check_proof, register_native
import cdclkit_native
register_native(cdclkit_native)
from campaign import oracle

cnf = "p cnf 2 2\n1 0\n-1 2 0\n"
proof = "d -1 2 0\n-2 0\n0\n"
for engine in ("python", "native"):
    r = check_proof(parse_dimacs(cnf), proof, engine=engine)
    print(engine, r.ok, r.rup_steps, r.rat_steps, r.deletions, r.ignored_deletions)
F = [[1], [-1, 2]]
print(oracle.satisfiable(F))
steps = [("d", (-1, 2)), ("a", (-2,)), ("a", ())]
print(oracle.replay(F, steps, "length-one")[0][-1])
```

Actual:

```
python True 1 1 1 0
native True 1 1 1 0
True
Step(index=3, kind='a', clause=(), rup=False, rat_on_first=None, implied=False, preserves_sat=False, present=None, applied=None)
```

The oracle says `satisfiable(F)` is True, so `ok=True` is wrong by the first rule of the
campaign. Under the flavour dratify documents, `length-one`, step 2 is acceptable (RAT,
vacuously) and step 3 is not RUP. Under `operational`, step 1 is ignored and step 2 is
already unacceptable. No flavour accepts this proof.

`rate` (files `a.cnf`, `a.drat`), all four modes:

| flags | reading | `rate` says |
|---|---|---|
| `-f -p` | forward, deletions honoured | `s NOT VERIFIED`, "conflict claimed but not detected" |
| `-f -p -d` | forward, skips deletion of clauses unit at the root | `s NOT VERIFIED` |
| `-p` | backward, deletions honoured | `s NOT VERIFIED`, "conflict claimed but not detected" |
| `-p -d` | backward, "drat-trim compatibility" | `s NOT VERIFIED` |

`rate` reports `reason deletions shrinking trail: 1` when it honours the deletion, so it
retracts what dratify keeps.

## Second symptom: a step counted as RUP that is not implied

Formula `(-4) (4 1)`, proof `d 4 1 0` then `1 0`. dratify returns `rup_steps=1`, on both
engines. The oracle's `length-one` reading of step 2: `rup=False`, `implied=False`,
`rat_on_first=True`. The brief says a RUP step must be implied. `deletion-2` proposes Bug
for this symptom alone, since the step does preserve satisfiability; the generator
reports it as Critical under the brief's literal wording. Either way it has the same
cause, and the severity of this finding rests on the `ok=True` case.

## How often

`python -m campaign.gen_drat_trim --rate PATH`, seed 1: 1,593 instances, 170 deletions
that shrink the root assignment. `ok_on_satisfiable` 102, which is 51 instances counted
once per engine; `rup_not_implied` 93; `field_mismatch` 18. All carry this label, which
means a deletion shrank the root assignment earlier in that proof. Seeds 2 and 3 are the
same in kind, plus one `accepted_unacceptable` on seed 3.

Replacing dratify with the oracle's `length-one` semantics (`Reference` in the generator)
leaves zero mismatches over the same 1,600 generated instances, beside the real `rate`.
So nothing else in this corner is hiding behind these labels on this seed, and these
mismatches are not an artefact of the harness.

## Suspected cause

The root assignment is propagated once and never revisited, and deleting a clause does not
touch it.

- Python: `src/dratify/proof.py:622-626` applies the deletion through `_erase` (524-537),
  which detaches the clause and leaves `prop.val` and `prop.trail` alone. Line 556 then
  treats a stale root literal as true, and 677 sets `_root_conflict` when a lemma is false
  under it.
- Rust: `rust/src/checker.rs:451-457` and `erase` at 322, with the same use of
  `prop.val` at 368 and 501-512.

The comment at `checker.rs:445-447` gives the reason a *unit* deletion is skipped:
"cannot be cleanly retracted". A clause of two or more literals that is the reason for a
root literal has the same problem, and the `len(lits) <= 1` test does not cover it. In the
example, `-2` is accepted as vacuously RAT on the clauses present, but it is false under
the stale root, so it sets `_root_conflict`, and `0` passes as RUP.

The README's "RAT steps are checked against exactly the clauses present" holds for the
RAT candidates, and not for the propagation that judges their resolvents.

## Is the fix clear?

The direction is clear and the choice is the maintainer's, because it decides which
flavour dratify documents:

1. **Ignore these deletions too**, counting them in `ignored_deletions`: skip a deletion
   when the clause has one true literal and the rest false at the root. This is the
   `operational` reading, the one `rate -d` implements and the oracle attributes to
   drat-trim. It is the small change, and it also ends the second symptom. `DOCUMENTED_FLAVOUR`
   in the generator and the README's wording would have to change with it.
2. **Honour them**: recompute the root assignment after such a deletion. This keeps
   `length-one`. It has a trap: `_add_lemma` (667-669) stores a clause satisfied at the root
   with arbitrary watches because the root never shrinks. Once it can shrink, those watches
   are wrong, so watches must be rebuilt along with the assignment. `_root_conflict` would
   also need a decision.

Data for that choice, with its limits: in the default run, 55 of 193 proofs from CaDiCaL
3.0.1 and kissat 4.0.4 contain a deletion, none shrink the root, and `rate` in `-f -p`
rejected none of the unsatisfiable ones. Seeds 2 and 3 have one shrinking proof each and
also no rejection. These formulas are tiny, and older solvers (the PySAT ones the README
names) were not measured. drat-trim's reason for skipping these deletions is that real
proofs can rely on them, so option 2 could reject proofs that verify today.

## Proposed failing test

```python
import unittest

from dratify import check_proof, parse_dimacs, register_native


class TestDeletedReasonClause(unittest.TestCase):
    """A root literal must not outlive the clause that implied it."""

    @classmethod
    def setUpClass(cls):
        import cdclkit_native
        register_native(cdclkit_native)

    def test_a_satisfiable_formula_is_not_refuted(self):
        formula = "p cnf 2 2\n1 0\n-1 2 0\n"      # satisfied by 1, 2
        for engine in ("python", "native"):
            with self.subTest(engine=engine):
                r = check_proof(parse_dimacs(formula), "d -1 2 0\n-2 0\n0\n", engine=engine)
                self.assertFalse(r.ok)

    def test_the_deleted_implication_is_not_counted_as_rup(self):
        formula = "p cnf 4 2\n-4 0\n4 1 0\n"
        for engine in ("python", "native"):
            with self.subTest(engine=engine):
                r = check_proof(parse_dimacs(formula), "d 4 1 0\n1 0\n", engine=engine)
                self.assertEqual(r.rup_steps, 0)
```

Both tests fail today on both engines. Under option 1 the second one needs rewriting: the
deletion is ignored, so `1` really is RUP and `rup_steps` is 1, with
`ignored_deletions` 1.
