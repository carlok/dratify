# deletion-4: ignored_deletions counts more than report() says it does

**Proposed severity: Note.** The verdict is right and both engines agree. Ignoring a
deletion of a clause that is not there is what the oracle's every flavour does too. This
is about what a number is called.

## Minimal cases

1. Formula `(1 2)`, proof `d 3 4 0`: a two-literal clause that is not present.
2. Formula `(1 -1) (1 2)`, proof `d 1 -1 0`: a tautology the input held, which
   `CNF.add` dropped.
3. For contrast, formula `(1 2)`, proof `1 -1 0`, `d 1 -1 0`: a tautological *lemma* is
   stored, so this deletion is applied.

## Reproducer

```bash
python - <<'EOF'
from dratify import check_proof, parse_dimacs, register_native
import cdclkit_native; register_native(cdclkit_native)
cases = [("p cnf 4 1\n1 2 0\n", "d 3 4 0\n"),
         ("p cnf 2 2\n1 -1 0\n1 2 0\n", "d 1 -1 0\n"),
         ("p cnf 2 1\n1 2 0\n", "1 -1 0\nd 1 -1 0\n")]
for formula, proof in cases:
    for engine in ("python", "native"):
        r = check_proof(parse_dimacs(formula), proof, engine=engine)
        print(engine, "deletions", r.deletions, "ignored", r.ignored_deletions)
print(check_proof(parse_dimacs(cases[0][0]), cases[0][1], engine="python").report())
EOF
```

Actual output:

```
python deletions 0 ignored 1
native deletions 0 ignored 1
python deletions 0 ignored 1
native deletions 0 ignored 1
python deletions 1 ignored 0
native deletions 1 ignored 0
s NOT VERIFIED
c every step verified, but the proof never derives the empty clause
c proof steps checked : 1
c   by RUP            : 0
c   by RAT            : 0 (0 resolvents checked)
c deletions applied   : 0 (1 unit deletions ignored)
```

Line 2 of the report calls `d 3 4 0` a unit deletion. A proof that deletes clauses the
checker does not have, which is what a mismatched formula and proof look like, is
reported as harmless unit handling. The oracle has no opinion on the wording.

For case 2, `oracle.remove_one([[1, -1], [1, 2]], [1, -1])` finds the clause present,
because the oracle keeps tautologies. The generator's model removes input tautologies
first, on the strength of `CNF.add` documenting the drop, so this is not a mismatch.
Tautologies never constrain anything, so verdicts cannot change this way.

## Cause and fix

`src/dratify/proof.py` line 626 (`r.ignored_deletions += 1` when `_erase` finds nothing)
and line 461 (the `report()` wording); `rust/src/checker.rs` around line 455. Both engines
behave the same.

The minimum fix is the wording: `(n unit or absent deletions ignored)`. A separate
counter would add a field to the native tuple, which is a bigger change for little gain.

Also, `test_deleting_a_clause_that_was_never_there` in `tests/test_rat.py` line 129
asserts `assertGreaterEqual(r.ignored_deletions, 0)`, which cannot fail.

## Proposed test

Replaces that assertion, and it passes today. The behaviour it pins is the one the
generator checks as `deletions_absent`.

```python
def test_deleting_a_clause_that_was_never_there(self):
    f = parse_dimacs("p cnf 2 1\n1 2 0\n")
    r = DRATChecker(f).check([("d", lits(1, -2)), ("a", lits(1, 2))])
    self.assertEqual((r.deletions, r.ignored_deletions), (0, 1))
```
