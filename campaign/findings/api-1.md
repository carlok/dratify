# api-1: the 0.1.7 soundness hole is still open on `DRATChecker`

**Proposed severity: Critical.** `ok=True` on a satisfiable formula, through a class
in `dratify.__all__` and re-exported by `cdclkit`.

## Minimal case

Formula `(1)`, satisfiable. Steps `[("a", (-1,)), ("a", ())]`: a DIMACS literal where an
internal one belongs, the mistake AGENTS.md calls the most common. Removing either step
or the clause makes it pass.

## Reproducer

```python
from dratify import parse_dimacs, check_proof
from dratify.proof import DRATChecker
from campaign import oracle
f = parse_dimacs("p cnf 1 1\n1 0\n")
print(oracle.satisfiable([[1]]))
print(DRATChecker(f).check([("a", (-1,)), ("a", ())]))
c = DRATChecker(f)
print(c.check_step("a", (-1,)), c.check_step("a", ()), c.result.reached_empty)
try:
    check_proof(f, [("a", (-1,)), ("a", ())], engine="python")
except ValueError as e:
    print("check_proof:", e)
g = parse_dimacs("p cnf 2 1\n1 2 0\n")
print(DRATChecker(g).check_step("x", (0, 2)))
```

Actual output:

```
True
<CheckResult VERIFIED: empty clause derived and every step verified>
True True True
check_proof: proof step 1: -1 is not an internal literal. Internal literals are non-negative integers; use lits.from_dimacs for signed DIMACS input.
True
```

Should be: the oracle says satisfiable, so `ok=True` is wrong, and `check` and `check_step`
should refuse as `check_proof` does. The last line is the same gap without the soundness
consequence: an unknown kind is read as an addition. A float raises `TypeError` where
`check_proof` raises `ValueError`, and a literal past the bound is accepted and grows the
arrays. Sizes up to 40 variables past the formula were run; a huge one was not run.

## Cause

`_validate_steps` is called only from `check_proof` (`src/dratify/proof.py:782`). The
CHANGELOG entry for 0.1.7 says "Every step is now validated before either checker runs",
which is true of that path only. `DRATChecker.check` (`proof.py:684`) and `check_step`
(`proof.py:601`) reach `_is_rup` and `_is_rat` with the negative index: `val[-1]` and
`occ[-2]` read from the end of the arrays, `_is_rat` accepts, and `_add_lemma`
(`proof.py:675-677`) sees no free literal and sets `_root_conflict`.

## Engines

Python only. Rust's `Lit` is `u32`, so the crate cannot be handed a negative literal, and
`engine="native"` goes through `check_proof`.

## Fix

Clear in outline. Validate inside `check_step`, so that `check` inherits it: literal a
non-negative `int`, not `bool`; kind `"a"` or `"d"`. `check_step` has no whole proof to
bound against, so the variable bound needs its own decision, and api-4 says that bound
needs rethinking anyway. Cost: one check per literal on the hot path; the
`tests/test_rat.py` calls pass internal literals and stay valid.

## Proposed test

```python
class TestStreamingApiValidates(unittest.TestCase):
    def test_a_negative_literal_is_refused(self):
        f = parse_dimacs("p cnf 1 1\n1 0\n")
        with self.assertRaises(ValueError):
            DRATChecker(f).check([("a", (-1,)), ("a", ())])
        with self.assertRaises(ValueError):
            DRATChecker(f).check_step("a", (-1,))

    def test_an_unknown_kind_is_refused(self):
        f = parse_dimacs("p cnf 2 1\n1 2 0\n")
        with self.assertRaises(ValueError):
            DRATChecker(f).check_step("x", (0, 2))
```
