# rat-2: the engines disagree on `failed_clause` when a rejected step repeats a literal

**Proposed severity: Bug.** The two engines disagree on a field, which the definitions
name as a Bug. The verdict and every other field agree. Same as `deletion-3`, `root-2`,
`engines-2`, `literals-2`, `api-3` and `ok_empty-2`, found independently.

## Minimal case

Formula `(-1)`, proof `1 1 0`. Removing either the repeat or the step makes it pass: with
`1 0` both engines report `(0,)`, and with no step nothing is rejected.

## Reproducer

```bash
python - <<'EOF'
from dratify import check_proof, parse_dimacs, register_native
import cdclkit_native; register_native(cdclkit_native)
for e in ("python", "native"):
    r = check_proof(parse_dimacs("p cnf 1 1\n-1 0\n"), "1 1 0\n", engine=e)
    print(e, r.ok, r.failed_step, r.failed_clause)
EOF
```

Actual output:

```
python False 1 (0,)
native False 1 (0, 0)
```

**What it should be:** the same tuple from both. The oracle reads both as the clause (1),
which is not RUP and not RAT: `oracle.rup([[-1]], [1])` and `oracle.rat([[-1]], [1], 1)` are
both False, so the rejection is right. The 0.1.9 changelog says "a clause is a set", and
`check_step` removes repeats, so `(0,)` is the consistent answer.

## Suspected cause

`_native_check` at `src/dratify/proof.py:909-910` does not read the checker's answer. It
rebuilds `failed_clause` from the step as written:
`r.failed_clause = tuple(steps[failed_step - 1][1])`. The Python checker reports the
deduplicated clause (`proof.py:635`), and so does the Rust one internally
(`rust/src/checker.rs:467`), but that value does not cross the binding. So the crate is
not at fault, and the fix belongs in the Python wrapper.

`tests/test_differential.py:69-71` compares this field, but on no proof with a repeated
literal in a rejected step.

**Engines:** the native path through `check_proof` is the odd one out, on text and list
input alike. Reached by any list or text proof whose rejected step repeats a literal.

## Is the fix clear?

Yes: `tuple(dict.fromkeys(steps[failed_step - 1][1]))` at `proof.py:910`, which keeps the
first occurrence and so keeps the pivot first, as `check_step` does.

## Evidence

`python -m campaign.gen_rat`: mismatches labelled `rat-2` are exactly those where
`failed_clause` is the only field that differs and the failing step has a repeat. There
are none with any other shape.

## Proposed test

```python
import unittest

from dratify import check_proof, parse_dimacs, register_native


def _native():
    try:
        import cdclkit_native as impl
    except ImportError:
        return None
    return impl


@unittest.skipIf(_native() is None, "no native checker installed")
class TestFailedClauseAgrees(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        register_native(_native())

    @classmethod
    def tearDownClass(cls):
        register_native(None)

    def test_a_rejected_step_with_a_repeated_literal(self):
        f = "p cnf 1 1\n-1 0\n"
        py = check_proof(parse_dimacs(f), "1 1 0\n", engine="python")
        rs = check_proof(parse_dimacs(f), "1 1 0\n", engine="native")
        self.assertEqual(py.failed_step, 1)
        self.assertEqual(py.failed_clause, rs.failed_clause)
```
