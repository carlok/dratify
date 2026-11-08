# literals-5: literals that skip the parser are not validated, the 0.1.7 hole by other doors

**Proposed severity: Critical, on 0.1.7's own precedent, with narrow reachability.**
0.1.7 rated `[("a", (-5,)), ("a", ())]` a security fix, and validated steps in
`check_proof`. That exact input still gets `ok=True` through the exported `DRATChecker`, and
the same mistake on `CNF.clauses` gets it through `check_proof` itself. Pure Python only.

The caveat: these inputs are off contract, since internal literals are documented as
non-negative. Text, `parse_dimacs`, `CNF.add`, and step lists through `check_proof` are all
safe. If the owner treats `DRATChecker` and direct `CNF.clauses` writes as internal, the
remaining certain part is the engine disagreement, which is a Bug. The `DRATChecker` part is
also reported as `api-1`.

## Minimal cases

```python
import cdclkit_native
from campaign import oracle
from dratify import CNF, DRATChecker, check_proof, parse_dimacs, register_native
register_native(cdclkit_native)

# (a) DIMACS integers on CNF.clauses, through check_proof
f = CNF(3)
f.clauses = [(-1,), (-2,), (3,)]
for e in ("python", "native"):
    try:
        r = check_proof(f, "0\n", engine=e); print(e, r.ok, r.reason)
    except Exception as ex:
        print(e, type(ex).__name__, ex)
print(oracle.satisfiable([[-1], [-2], [3]]))

# (b) 0.1.7's exact step list, through the exported class
g = parse_dimacs("p cnf 3 2\n1 2 0\n-2 3 0\n")
r = DRATChecker(g).check([("a", (-5,)), ("a", ())])
print("DRATChecker", r.ok, r.reason)
print(oracle.satisfiable([[1, 2], [-2, 3]]))
try:
    check_proof(g, [("a", (-5,)), ("a", ())], engine="python")
except ValueError as ex:
    print("check_proof ValueError", str(ex)[:60])

# (c) a repeated literal on CNF.clauses is not a unit: fails closed
h = CNF(1)
h.clauses = [(0, 0), (1, 1)]
for e in ("python", "native"):
    r = check_proof(h, "0\n", engine=e); print(e, r.ok, r.failed_step)
print(oracle.propagate([[1, 1], [-1, -1]])[0])

# (d) a count past u32: same bare error, no clause involved
w = CNF(1 << 32)
w.add_dimacs([1])
for e in ("python", "native"):
    try:
        r = check_proof(w, "", engine=e); print(e, r.ok, r.reason)
    except Exception as ex:
        print(e, type(ex).__name__, ex)
```

Actual output:

```
python True input formula is refuted by unit propagation alone
native OverflowError out of range integral type conversion attempted
True
DRATChecker True empty clause derived and every step verified
True
check_proof ValueError proof step 1: -5 is not an internal literal. Internal litera
python False 1
native False 1
True
python False every step verified, but the proof never derives the empty clause
native OverflowError out of range integral type conversion attempted
```

Expected:

- (a) `ValueError` naming `from_dimacs`, from both engines, before either runs. `[[-1],
  [-2], [3]]` read as DIMACS is satisfiable, and Python called it refuted because `-1` and
  `-2` index the end of the value array, where they alias a literal and its complement.
- (b) the same `ValueError` that `check_proof` raises for the same list.
- (c) `ok=True`, because `(x1 x1)` and `(-x1 -x1)` are refuted by unit propagation when a
  clause is a set, as the oracle shows. `CNF.add` would have collapsed them.
- (d) one answer. CHANGELOG 0.1.7 itself calls this `OverflowError` "unexplained".

## Cause and engines

- `src/dratify/proof.py:782`: `_validate_steps` looks at steps, not at `formula.clauses`.
- `src/dratify/proof.py:481-501`: `DRATChecker.__init__` inserts `formula.clauses` as they
  are, with no check for negative values or repeats.
- `src/dratify/proof.py:684` and `:601`: `DRATChecker.check` and `check_step` take steps
  directly, and validation lives only in `check_proof`.
- Python is exposed. Native raises `OverflowError` at the binding because its types are
  `u32`, so it fails closed.

`DRATChecker` is in `__all__`, and cdclkit re-exports it (`cdclkit/__init__.py:52`). AGENTS.md
calls passing DIMACS integers "the most common mistake".

## Is the fix clear?

Mostly:

- Validate `formula.clauses` once, in `DRATChecker.__init__` and before the native path:
  non-negative ints, each clause free of repeats, or normalise repeats on the way in.
  That costs one pass over the formula.
- Move the step check into `DRATChecker.check_step`, or give `check` the same validation.
  `check_step` is the hot path, so a sign check on `lits` there has a measurable cost: the
  owner may prefer validating in `check` and documenting `check_step` as trusted.
- Reject or explain `nvars` above u32 before calling native.

## Reach in this generator

Labels `unvalidated-surface` (1753) and `repeat-surface` (1122), from `family_surfaces` and
`family_floor`.

## Proposed failing test

```python
class TestLiteralsThatSkipTheParser(unittest.TestCase):
    def test_a_negative_literal_on_the_formula_is_refused(self):
        f = CNF(3)
        f.clauses = [(-1,), (-2,), (3,)]
        for engine in ("python", "native"):
            with self.subTest(engine=engine), self.assertRaises(ValueError):
                check_proof(f, "0\n", engine=engine)

    def test_drat_checker_refuses_a_negative_step(self):
        g = parse_dimacs("p cnf 3 2\n1 2 0\n-2 3 0\n")
        with self.assertRaises(ValueError):
            DRATChecker(g).check([("a", (-5,)), ("a", ())])

    def test_a_repeat_on_the_formula_is_the_same_clause(self):
        h = CNF(1)
        h.clauses = [(0, 0), (1, 1)]
        self.assertTrue(check_proof(h, "0\n", engine="python").ok)
```

The native subtest needs `register_native`, as in `tests/test_repeated_literals.py`.
