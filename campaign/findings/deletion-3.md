# deletion-3: the engines disagree on failed_clause when the failing step repeats a literal

**Proposed severity: Bug**, by the rubric's "the Python and native engines disagree on
any field". It does not change a verdict.

## Minimal case

Formula `(1 2)`, proof `-1 -1 0`. Without the repeat, both engines report the same.

## Reproducer

```bash
python - <<'EOF'
from dratify import check_proof, parse_dimacs, register_native
import cdclkit_native; register_native(cdclkit_native)
for engine in ("python", "native"):
    r = check_proof(parse_dimacs("p cnf 2 1\n1 2 0\n"), "-1 -1 0\n", engine=engine)
    print(engine, r.failed_step, r.failed_clause)
EOF
```

Actual output:

```
python 1 (1,)
native 1 (1, 1)
```

The oracle reads a clause as the set of its literals, and `check_step` in both engines
removes repeats first ("A clause is a set"). So Python's `(1,)` is what is documented.
`report()` prints the difference too, in its `first bad step` line.

## Cause

`_native_check` in `src/dratify/proof.py`, line 910:
`r.failed_clause = tuple(steps[failed_step - 1][1])`. The native tuple has no
`failed_clause`, so Python rebuilds it from the step as written, whereas Rust's
`result.failed_clause` is deduplicated and never leaves the crate. Python's `check_step`
stores the deduplicated `lits`. Only `engine="native"` (or `"auto"` with a native
checker) is affected.

The fix is clear: `tuple(dict.fromkeys(steps[failed_step - 1][1]))`.

## Proposed failing test

```python
class TestFailedClauseRepeats(unittest.TestCase):

    @unittest.skipIf(_native() is None, "no native checker installed")
    def test_both_engines_report_the_clause_as_a_set(self):
        register_native(_native())
        self.addCleanup(register_native, None)
        formula = "p cnf 2 1\n1 2 0\n"
        for engine in ("python", "native"):
            with self.subTest(engine=engine):
                r = check_proof(parse_dimacs(formula), "-1 -1 0\n", engine=engine)
                self.assertEqual(r.failed_clause, (from_dimacs(-1),))
```
