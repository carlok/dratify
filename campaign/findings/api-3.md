# api-3: `failed_clause` differs between engines when the rejected step repeats a literal

**Proposed severity: Bug.** The engines disagree on a field. The verdict is unaffected.

## Minimal case

Formula `(1)`, proof `-1 -1 0`. A rejected clause with no repeat agrees.

## Reproducer

```python
import cdclkit_native
from dratify import parse_dimacs, check_proof, register_native
from campaign import oracle
register_native(cdclkit_native)
f = parse_dimacs("p cnf 1 1\n1 0\n")
print(oracle.rup([[1]], [-1, -1]), oracle.rat([[1]], [-1, -1], -1))
for engine in ("python", "native"):
    r = check_proof(f, "-1 -1 0\n", engine=engine)
    print(engine, r.failed_step, r.failed_clause, r.report().splitlines()[-1])
```

Actual output:

```
False False
python 1 (1,) c first bad step 1: -1 0
native 1 (1, 1) c first bad step 1: -1 -1 0
```

Should be: the same tuple on both. Both are defensible as a value, since "a clause is a
set" favours `(1,)` and "what the proof said" favours `(1, 1)`, but the differential claim
is that they are the same. The oracle agrees that the step is rejected.

## Cause

Python records the clause after removing repeats (`src/dratify/proof.py:611-612` then
`:635`). The native path does not return `failed_clause`; `_native_check` rebuilds it from
the step as written (`proof.py:910`). The Rust crate itself is right: its own
`CheckResult.failed_clause` (`rust/src/checker.rs:467`) is deduplicated, and the generator's
Rust driver sees it agree with Python. `tests/test_differential.py:71` compares this field,
but on no proof with a repeat in a rejected step.

## Engines

Only `engine="native"` and `"auto"` through `check_proof`.

## Fix

Clear: `r.failed_clause = tuple(dict.fromkeys(steps[failed_step - 1][1]))` at `proof.py:910`.

## Proposed test

```python
class TestFailedClause(unittest.TestCase):   # with register_native, as test_differential.py
    def test_it_is_the_same_set_on_both_engines(self):
        f = parse_dimacs("p cnf 1 1\n1 0\n")
        py = check_proof(f, "-1 -1 0\n", engine="python")
        native = check_proof(f, "-1 -1 0\n", engine="native")
        self.assertEqual(py.failed_clause, (from_dimacs(-1),))
        self.assertEqual(native.failed_clause, py.failed_clause)
        self.assertEqual(native.report(), py.report())
```
