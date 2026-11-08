# engines-2: failed_clause differs between engines when a step repeats a literal

**Proposed severity: Bug.** The Python and native engines disagree on a field. The verdict,
the counters and `failed_step` all agree, so no proof changes outcome. The same defect as
`deletion-3` and `root-2`, reached independently.

## Minimal case

```
p cnf 2 1
1 2 0
```

```
-1 -1 0
```

With `-1 0` as the step, both engines report `(1,)`. Repetition is what separates them.

## Reproducer

From the repo root:

```python
import cdclkit_native
from dratify import parse_dimacs, check_proof, register_native
from campaign import oracle

register_native(cdclkit_native)
f = parse_dimacs("p cnf 2 1\n1 2 0\n")
for engine in ("python", "native"):
    r = check_proof(f, "-1 -1 0\n", engine=engine)
    print(engine, r.ok, r.failed_step, r.failed_clause)

print(oracle.rup([[1, 2]], [-1, -1]), oracle.rat([[1, 2]], [-1, -1], -1))
```

## Actual output

```
python False 1 (1,)
native False 1 (1, 1)
False False
```

## What it should be

The oracle agrees with the rejection, as it treats a clause as the set of its literals.
The two engines should give the same `failed_clause`. The documentation says repeats are
removed when a step is read (CHANGELOG, and the comment at `src/dratify/proof.py:604`), and
`tests/test_differential.py:69` lists `failed_clause` among the fields that must agree. So
`(1,)` is right, and the native path is the one to change.

## Suspected cause

`src/dratify/proof.py:909-910`. The native tuple has no `failed_clause`, so the bridge
rebuilds it from the raw step:

```python
if failed_step > 0 and failed_step <= len(steps):
    r.failed_clause = tuple(steps[failed_step - 1][1])
```

The Rust crate itself is right. `rust/src/checker.rs:467` stores the deduplicated clause,
but `py_check_proof` in cdclkit's `native/src/lib.rs:591` does not return it. Python
deduplicates before storing at `src/dratify/proof.py:611-612` and `635`.

It reaches `report()` as well, whose last line prints `failed_clause`.

## Engines affected

Native only, through the bridge in the Python package. In the default run, 13150 comparisons
flagged this. They were made on text proofs, and the list and `MemoryProof` paths gave each
engine the same result as text. It is the only field the engines disagreed on across
3,503,940 comparisons.

`tests/test_differential.py` misses it because its random sweep never repeats a literal.

## Fix

Clear, and one line:

```python
r.failed_clause = tuple(dict.fromkeys(steps[failed_step - 1][1]))
```

## Proposed test

For `TestBothCheckersAgree` in `tests/test_differential.py`. Run against the current tree,
it fails with `failed_clause differs`.

```python
    def test_a_failed_step_that_repeats_a_literal(self):
        r = self._agree("p cnf 2 1\n1 2 0\n", "-1 -1 0\n", "repeat")
        self.assertFalse(r.ok)
        self.assertEqual(r.failed_clause, (from_dimacs(-1),))
```

This needs `from_dimacs` imported from `dratify`.
