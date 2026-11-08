# rat-3: reason deletions split dratify from drat-trim, and `ignored_deletions` is mislabelled

**Proposed severity: Note,** on two small points. Neither changes a verdict.
`deletion-4` reports the second point too.

## 1. The two flavours part on a reason deletion

drat-trim is not installed here, so this compares with the oracle's `operational`
flavour, its approximation of drat-trim, and not with drat-trim itself.

Formula `(1) (-1 2)`, proof `d -1 2 0`, `-2 3 0`:

- `length-one` (dratify's documented rule) and `specified`: the deletion applies, nothing
  contains `2`, and `-2 3` is vacuously RAT.
- `operational`: the deletion is ignored because the clause is pseudo-unit, so `(-1 2)` is
  a candidate, the resolvent `(-2 3 -1)` is not RUP, and the step is refused.

```bash
python - <<'EOF'
from campaign import oracle
for fl in oracle.FLAVOURS:
    judged, final = oracle.replay([[1], [-1, 2]], [("d", [-1, 2]), ("a", [-2, 3])], fl)
    print(fl, [s.acceptable for s in judged if s.kind == "a"], final)
EOF
```

Output:

```
specified [True] [[1], [-2, 3]]
operational [False] [[1], [-1, 2]]
length-one [True] [[1], [-2, 3]]
```

dratify accepts this step today. With `rat-1` in place that acceptance is what leads on
to the unsound verdict, and with `rat-1` fixed by honouring the deletion it would remain a
documented difference from drat-trim. Soundness does not depend on which flavour is
chosen, provided the root assignment agrees with it. The generator counts these as
`note_verdict_differs_operational` and `note_verdict_differs_specified`, and they do not
fail the run.

Whichever flavour `rat-1`'s fix picks, the README's "Deletion" paragraph and the comment at
`src/dratify/proof.py:41-50` should say which. That comment calls ignoring unit deletions
"the one universally adopted exception", but by Rebola-Pardo and Biere's account, which the
oracle follows, drat-trim also ignores deletions of pseudo-unit clauses.

## 2. `report()` calls absent-clause deletions "unit deletions"

Deleting a clause that is not there is counted in `ignored_deletions`, which is
reasonable, and `report()` then describes it as a unit:

```bash
python - <<'EOF'
from dratify import check_proof, parse_dimacs
print(check_proof(parse_dimacs("p cnf 2 1\n1 2 0\n"), "d 1 -2 0\n", engine="python").report())
EOF
```

```
s NOT VERIFIED
c every step verified, but the proof never derives the empty clause
c proof steps checked : 1
c   by RUP            : 0
c   by RAT            : 0 (0 resolvents checked)
c deletions applied   : 0 (1 unit deletions ignored)
```

`(1 -2)` is neither a unit nor present. Both engines count it the same way (`proof.py:625-626`,
`rust/src/checker.rs:454-456`). The wording is at `proof.py:461`. A proof with many deletions of
absent clauses, usually a sign the formula and proof do not belong together, reads as a
routine count of ignored units. Suggested wording: "ignored (units or not present)".

## Proposed test

Point 1 calls for documentation, not a test. For point 2:

```python
import unittest

from dratify import check_proof, parse_dimacs


class TestIgnoredDeletionWording(unittest.TestCase):
    def test_an_absent_clause_is_not_called_a_unit(self):
        r = check_proof(parse_dimacs("p cnf 2 1\n1 2 0\n"), "d 1 -2 0\n", engine="python")
        self.assertEqual(r.ignored_deletions, 1)
        self.assertNotIn("1 unit deletions ignored", r.report())
```
