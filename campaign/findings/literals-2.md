# literals-2: `failed_clause` keeps repeated literals on native and drops them on Python

**Proposed severity: Bug.** The Python and native engines disagree on a result field,
which the brief lists as a Bug and `SECURITY.md` asks to hear about. The verdict is the
same on both.

Also reported as `api-3`, `deletion-3`, `engines-2`, `root-2`.

## Minimal case

```
formula: p cnf 2 1 / 1 2 0
proof:   -1 -1 0
```

With one `-1` the engines agree, so the repeat is what matters.

## Reproducer

```python
import cdclkit_native
from campaign import oracle
from dratify import check_proof, parse_dimacs, register_native
register_native(cdclkit_native)

f = parse_dimacs("p cnf 2 1\n1 2 0\n")
for e in ("python", "native"):
    r = check_proof(f, "-1 -1 0\n", engine=e)
    print(e, r.ok, r.failed_step, r.failed_clause, repr(r.report().splitlines()[-1]))
print(oracle.rup([[1, 2]], [-1, -1]), oracle.rat([[1, 2]], [-1, -1], -1))
```

Actual output:

```
python False 1 (1,) 'c first bad step 1: -1 0'
native False 1 (1, 1) 'c first bad step 1: -1 -1 0'
False False
```

Expected: the same `failed_clause` from both. The oracle confirms the step should be
rejected, and both engines do reject it. `tests/test_differential.py` and CHANGELOG 0.1.7
say every field is compared, including `failed_clause`, but no case there rejects a
repeated literal.

## Cause and engines

`src/dratify/proof.py:909-910` (`_native_check`). The native binding does not return
`failed_clause`, so Python rebuilds it from the step as written:

```python
r.failed_clause = tuple(steps[failed_step - 1][1])
```

The Python checker stores it after removing repeats (`proof.py:611-612`, `:635`). So does
the Rust `Checker` itself (`rust/src/checker.rs:436`, `:467`), but that value never crosses
the binding.

## Is the fix clear?

Yes, once the author picks a meaning:

- The set: `tuple(dict.fromkeys(steps[failed_step - 1][1]))` in `_native_check`. This
  matches Python and Rust's own field, and "a clause is a set" is what 0.1.9 settled.
- The step as written, if a report should quote the proof line. Then Python and Rust change.

## Proposed failing test

Add to `tests/test_differential.py`, inside `TestBothCheckersAgree`:

```python
    def test_a_rejected_step_that_repeats_a_literal(self):
        r = self._agree("p cnf 2 1\n1 2 0\n", "-1 -1 0\n", "repeat in failed step")
        self.assertEqual(r.failed_step, 1)
```
