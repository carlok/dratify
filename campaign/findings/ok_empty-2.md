# ok_empty-2: `failed_clause` differs between the engines on a repeated literal

**Proposed severity: Bug.** "The Python and native engines disagree on any field".
The verdict and every other field agree.

## Minimal case

```
formula            proof
p cnf 1 1          -1 -1 0
1 0
```

Dropping either copy of `-1` makes the engines agree, and with no clause or no step
nothing fails.

## Reproducer

Run from the repo root, with `cdclkit_native` installed:

```python
from dratify import parse_dimacs, check_proof, register_native
import cdclkit_native
from campaign import oracle

register_native(cdclkit_native)
f = parse_dimacs("p cnf 1 1\n1 0\n")
for engine in ("python", "native"):
    r = check_proof(f, "-1 -1 0\n", engine=engine)
    print(engine, r.ok, r.failed_step, r.failed_clause)
steps, _ = oracle.replay([[1]], [("a", (-1, -1))])
print([(s.clause, s.rup, s.rat_on_first, s.acceptable) for s in steps])
```

Actual output:

```
python False 1 (1,)
native False 1 (1, 1)
[((-1, -1), False, False, False)]
```

Expected: the same `failed_clause` from both. The oracle agrees with the rejection, so
only the reporting differs. `report()` follows it: `c first bad step 1: -1 0` against
`-1 -1 0`.

## Suspected cause

`src/dratify/proof.py:635` stores the clause after `check_step` removes repeats (0.1.9).
The native result has no such field (`_NATIVE_FIELDS`), so `src/dratify/proof.py:910`
rebuilds it from the raw step. The Rust checker's own `failed_clause`
(`rust/src/checker.rs:467`) is deduplicated, but never crosses into Python. Text, list
and `MemoryProof` input all show it. `tests/test_differential.py` compares this field,
but on no failing step with a repeat.

## Fix

Clear, if deduplicated is the intended meaning, since a clause is a set:
`tuple(dict.fromkeys(steps[failed_step - 1][1]))` at `proof.py:910`. It keeps the order,
so the pivot stays first.

## Proposed failing test

For `TestBothCheckersAgree` in `tests/test_differential.py`, whose `_agree` compares
every field:

```python
    def test_a_failing_step_that_repeats_a_literal(self):
        r = self._agree("p cnf 1 1\n1 0\n", "-1 -1 0\n", "repeat in a failing step")
        self.assertFalse(r.ok)
        self.assertEqual(r.failed_step, 1)
```
