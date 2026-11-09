# root-2: `failed_clause` differs between the engines when a rejected step repeats a literal

**Proposed severity: Bug.** The brief's definition: the Python and native engines
disagree on any field. The verdict is the same, and no soundness question arises.

## Minimal case

Formula `(-1 2)`, proof `1 1 0`. It is rejected by both, and neither removing the
repeat nor removing the clause leaves a disagreement.

## Reproducer

```python
import cdclkit_native
from dratify import check_proof, parse_dimacs, register_native
register_native(cdclkit_native)

for e in ("python", "native"):
    r = check_proof(parse_dimacs("p cnf 2 1\n-1 2 0\n"), "1 1 0\n", engine=e)
    print(e, r.ok, r.failed_step, r.failed_clause)
```

## Actual

```
python False 1 (0,)
native False 1 (0, 0)
```

## What it should be

The same on both. CHANGELOG 0.1.9 says "A clause is a set" and "Repeats are now
removed when a step is read", so `(0,)`, Python's answer, is the documented one. The
oracle has no opinion on this field beyond the set: `oracle.replay` agrees the step
is rejected, and `_lits` reads `[1, 1]` as the clause (1). README.md claims the
engines have been "differentially tested ... on acceptances *and* on rejections",
and `CheckResult.report()` prints this field.

4,834 comparisons carry this label in the default run. `tests/test_differential.py`
does compare this field (line 71), so its absence there is a coverage gap: none of
its cases reported this mismatch. Why its sweep misses it was not investigated.
`_NATIVE_FIELDS` does not carry the field across, and it is rebuilt in Python.

## Suspected cause

`_native_check` in `src/dratify/proof.py:910` rebuilds the clause from the raw step:

```python
r.failed_clause = tuple(steps[failed_step - 1][1])
```

Python stores the deduplicated step (proof.py:611-612, then 635). The Rust checker
stores the deduplicated one too (`checker.rs:436`, then 467), but that value is not
among the fields returned to Python.

So the Rust checker itself is right and only `engine="native"` from Python shows the
raw clause; a direct Rust caller gets the deduplicated one (from reading
`checker.rs`, not run). The fix looks clear:
`tuple(dict.fromkeys(steps[failed_step - 1][1]))`.

## Proposed failing test

```python
# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Both engines report a rejected clause as the same set of literals."""

from __future__ import annotations

import unittest

from dratify import check_proof, parse_dimacs, register_native


def _native():
    try:
        import cdclkit_native as impl
    except ImportError:
        return None
    return impl


@unittest.skipIf(_native() is None,
                 "no native checker installed; CI installs cdclkit-native")
class TestFailedClauseAgrees(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        register_native(_native())

    @classmethod
    def tearDownClass(cls):
        register_native(None)

    def test_a_rejected_step_with_a_repeated_literal(self):
        f = "p cnf 2 1\n-1 2 0\n"
        py = check_proof(parse_dimacs(f), "1 1 0\n", engine="python")
        rs = check_proof(parse_dimacs(f), "1 1 0\n", engine="native")
        self.assertEqual(py.failed_step, 1)
        self.assertEqual(py.failed_clause, rs.failed_clause)


if __name__ == "__main__":
    unittest.main()
```
