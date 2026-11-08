# api-7: a step's literals may be a set, and then the engines disagree

**Proposed severity: Bug**, the low end. The brief's rule is that the engines disagreeing on any
field is a Bug, and here one raises while the other returns a verdict. The input is outside the
annotation, `Sequence[int]`, so the author may reasonably call it a Note. `_validate_steps`
exists to refuse such input, though, and lets it through.

## Minimal case

Formula `(-1 2)`, one step whose literals are `frozenset({0, 3})`. A clause that is RUP does not
show it, because only `_is_rat` indexes the literals.

## Reproducer

```python
import cdclkit_native
from dratify import parse_dimacs, check_proof, register_native
register_native(cdclkit_native)
f = parse_dimacs("p cnf 2 1\n-1 2 0\n")
for engine in ("python", "native"):
    try:
        r = check_proof(f, [("a", frozenset({0, 3}))], engine=engine)
        print(engine, r.rat_steps, r.failed_step, r.reason)
    except Exception as e:
        print(engine, type(e).__name__, e)
```

Actual output:

```
python TypeError 'frozenset' object is not subscriptable
native 1 -1 every step verified, but the proof never derives the empty clause
```

Should be: `ValueError` from both, because a set has no first literal and the RAT pivot is the
first literal. The native answer depends on the order `list()` happens to give. SECURITY.md rates
an unhandled exception a caller cannot tell from a verdict as High, and bare `TypeError` is what
it means; `("a", 5)` and `("a", None)` also raise bare `TypeError`, from the `len` at
`_validate_steps` itself, on both engines.

## Cause

`_validate_steps` (`src/dratify/proof.py:731-742`) checks each literal but not the container:
`len(step[1])` and a `for` loop pass for any sized iterable. `_is_rat` then does `lits[0]`
(`proof.py:573`) on Python, while `_native_check` does `list(lits)` (`proof.py:863`).

## Fix

Clear: in `_validate_steps`, require `isinstance(lits, (tuple, list))` and raise the existing
"a proof step must be (kind, literals)" `ValueError`.

## Proposed test

```python
class TestLiteralsNeedAnOrder(unittest.TestCase):   # with register_native, as test_differential.py
    def test_a_set_is_refused_on_both_engines(self):
        f = parse_dimacs("p cnf 2 1\n-1 2 0\n")
        for engine in ("python", "native"):
            with self.subTest(engine=engine), self.assertRaises(ValueError):
                check_proof(f, [("a", frozenset({0, 3}))], engine=engine)
```
