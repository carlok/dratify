# parsing-10: `failed_clause` differs between engines on a repeated literal (not a parsing bug)

**Proposed severity: Bug.** The engines disagree on a field. This is a **duplicate** of api-3,
deletion-3, engines-2, literals-2, ok_empty-2 and root-2. It is recorded because this generator's
engine comparison found it independently, from text with a repeated literal.

## Minimal case

Formula `1 0`, proof `-1 -1 0`. With no repeat the engines agree.

## Reproducer

```python
from dratify import check_proof, parse_dimacs, register_native
from campaign import oracle
import cdclkit_native
register_native(cdclkit_native)

f = parse_dimacs("p cnf 1 1\n1 0\n")
for engine in ("python", "native"):
    r = check_proof(f, "-1 -1 0\n", engine=engine)
    print(engine, r.failed_step, r.failed_clause)
print(oracle.rup([[1]], [-1, -1]), oracle.rat([[1]], [-1, -1], -1))
```

```
python 1 (1,)
native 1 (1, 1)
False False
```

Should be: the same tuple on both. The oracle agrees that the step is unacceptable, so only
the field differs. The internal literal for `-1` is 1.

## Suspected cause

Python records the deduplicated `lits` (`src/dratify/proof.py:612,635`). `_native_check` rebuilds
the field from the raw step (`r.failed_clause = tuple(steps[failed_step - 1][1])`). The fix is clear:
`tuple(dict.fromkeys(...))` there.

## Proposed test

```python
import unittest

from dratify import check_proof, parse_dimacs, register_native


class TestFailedClauseAgrees(unittest.TestCase):
    def test_both_engines_report_the_clause_as_a_set(self):
        import cdclkit_native
        register_native(cdclkit_native)
        self.addCleanup(register_native, None)
        f = parse_dimacs("p cnf 1 1\n1 0\n")
        py = check_proof(f, "-1 -1 0\n", engine="python")
        native = check_proof(f, "-1 -1 0\n", engine="native")
        self.assertEqual(py.failed_clause, native.failed_clause)
```
