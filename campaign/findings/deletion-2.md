# deletion-2: a step neither RUP nor RAT on the clauses present is accepted, and counted as RUP

**Proposed severity: Bug.** Please check this one against your reading of the
definitions. The rubric's Critical line says "a RUP step must be implied", and read
literally against the current multiset this step is not. I propose Bug because the step
*is* implied by the input and does preserve satisfiability, so it cannot refute anything
by itself; what it contradicts is dratify's documentation. The oracle's `operational`
flavour accepts it; drat-trim itself was not run.

## Minimal case

Formula `(1) (-1 2) (-2 3)`. Proof:

```
d -1 2 0
2 0
```

Remove `(-2 3)` and `(2)` becomes vacuously RAT, so it is acceptable on the clauses
present (though still counted as RUP). Remove `(1)` and it is rejected. Remove the
deletion and it is honestly RUP.

## Reproducer

```bash
python - <<'EOF'
from campaign import oracle
from dratify import check_proof, parse_dimacs, register_native
import cdclkit_native; register_native(cdclkit_native)
FORMULA = "p cnf 3 3\n1 0\n-1 2 0\n-2 3 0\n"
F = [[1], [-1, 2], [-2, 3]]
STEPS = [("d", [-1, 2]), ("a", [2])]
for engine in ("python", "native"):
    r = check_proof(parse_dimacs(FORMULA), "d -1 2 0\n2 0\n", engine=engine)
    print(engine, "failed_step", r.failed_step, "rup", r.rup_steps, "rat", r.rat_steps,
          "deletions", r.deletions)
for flavour in oracle.FLAVOURS:
    s = oracle.replay(F, STEPS, flavour)[0][1]
    print(flavour, "rup", s.rup, "rat", s.rat_on_first, "implied", s.implied,
          "preserves_sat", s.preserves_sat)
print("implied by the input:", oracle.implies(F, [2]))
EOF
```

Actual output:

```
python failed_step -1 rup 1 rat 0 deletions 1
native failed_step -1 rup 1 rat 0 deletions 1
specified rup False rat False implied False preserves_sat True
operational rup True rat True implied True preserves_sat True
length-one rup False rat False implied False preserves_sat True
implied by the input: True
```

The documented flavour is `length-one`, and it says reject. dratify reports the
deletion as applied (`deletions` 1), then uses what that clause implied.

## What the documents say

- `DRATChecker` docstring (proof.py line 473): every addition is "verified against the
  clauses present at that moment".
- proof.py line 50 and README.md line 169: a RAT step "is checked against exactly the
  clauses present".
- proof.py line 41: deletion lines "are honoured", with unit clauses the one exception.

The same happens inside RAT: resolvents are RUP-checked under the stale root too, and a
RAT step on the clauses present can be counted in `rup_steps` instead of `rat_steps`
(`rat_step_counted_as_rup` in the generator).

## Why it is not deletion-1

Same root cause, different effect. The literal is implied by the clauses present when
it was derived, so a checker using it is working on the clauses present plus consequences
of earlier clauses. RUP stays sound there, and with `check_rat=False` every step the sweep
accepted was implied by the input (`rup_mode_not_implied_by_input` stayed at 0). The false
refutation needs the RAT step of deletion-1 as well.

## Cause and fix

Suspected cause is as in deletion-1: the root assignment is not retracted when a clause
of two or more literals is deleted. Python: `_erase` and the deletion path in
`check_step` in `src/dratify/proof.py`, lines 618-627, with `_is_rup` reading the root
values at lines 548-563. Rust: `check_step` in `rust/src/checker.rs` around line 452.
Both engines are affected, identically.

The fix is the same decision. Ignoring the deletion of a clause unit at the root makes
this behaviour correct by definition, and then the documentation needs to say so.
Retracting the literal makes this step rejected. Either way, doc and code then agree.

## Proposed failing test

This pins the documented behaviour. If the fix ignores reason deletions, the assertion
should become `(deletions, ignored_deletions) == (0, 1)` instead, so that a deletion
reported as applied never leaves its consequences usable.

```python
class TestDeletedReasonIsGone(unittest.TestCase):
    engine = "python"

    def test_a_step_needing_a_deleted_reason(self):
        formula = parse_dimacs("p cnf 3 3\n1 0\n-1 2 0\n-2 3 0\n")
        r = check_proof(formula, "d -1 2 0\n2 0\n", engine=self.engine)
        if r.deletions == 1:
            # the deletion was applied, so (2) is neither RUP nor RAT here
            self.assertEqual(r.failed_step, 2)
        else:
            self.assertEqual((r.deletions, r.ignored_deletions), (0, 1))
```
