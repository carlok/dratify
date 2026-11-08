# engines-3: a valid proof raises ValueError over a fresh variable's index

**Proposed severity: Bug, of low impact.** dratify refuses a step that is RAT on its first
literal, under semantics it documents ("A proof may still introduce fresh variables"). It
fails closed, which `SECURITY.md` places under "not a vulnerability" but still "a bug worth
an issue". It is not listed under "Honest limitations". If the guard is meant as a limit,
this becomes a documentation Note, and the claim below still needs correcting.

## Minimal case

```
p cnf 2 4
1 2 0
1 -2 0
-1 2 0
-1 -2 0
```

```
50 0
1 0
0
```

`1 0` and `0` alone are a valid refutation that both engines accept. `50 0` adds a unit on
a variable nothing else mentions, which is vacuously RAT. Without `50 0` it passes, with
`9 0` in its place it passes, and with `50 0` it raises.

## Reproducer

From the repo root:

```python
import cdclkit_native
from dratify import parse_dimacs, check_proof, register_native, from_dimacs
from campaign import oracle

register_native(cdclkit_native)
SQUARE = "p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n"
f = parse_dimacs(SQUARE)
for engine in ("python", "native"):
    try:
        print(engine, check_proof(f, "50 0\n1 0\n0\n", engine=engine))
    except ValueError as e:
        print(engine, "ValueError:", e)

G = [[1, 2], [1, -2], [-1, 2], [-1, -2]]
walk, _ = oracle.replay(G, [("a", [50]), ("a", [1]), ("a", [])], "length-one")
print([(s.clause, s.rup, s.rat_on_first, s.acceptable) for s in walk])

# the same proof as text and as a list of steps
print(check_proof(f, "6 0\n1 0\n0\n", engine="python").ok)
steps = [("a", (from_dimacs(6),)), ("a", (from_dimacs(1),)), ("a", ())]
try:
    print(check_proof(f, steps, engine="python").ok)
except ValueError as e:
    print("ValueError:", e)
```

## Actual output

```
python ValueError: proof step 1: literal 50 names variable 50, but a 2-variable formula and this proof can account for at most 13
native ValueError: proof step 1: literal 50 names variable 50, but a 2-variable formula and this proof can account for at most 13
[((50,), False, True, True), ((1,), True, True, True), ((), True, None, True)]
True
ValueError: proof step 1: literal 6 names variable 6, but a 2-variable formula and this proof can account for at most 4
```

## What it should be

The oracle says every step is acceptable and the formula is unsatisfiable, so `ok=True`, as
with `9 0` in the same place.

The last two lines show a second consequence: the same proof is accepted as text and
refused as a list of steps, because the bound is tighter there.

## Suspected cause

`src/dratify/proof.py:736` and `747`, in `_validate_steps`, which runs before either engine.
Its docstring reasons:

> a proof can only introduce variables it mentions, so the largest index is at most the
> formula's count plus the number of literal occurrences

That does not follow, since a proof can mention variable 50 once without mentioning 3 to 49.
The bound is a guard against allocation from a hostile literal, which is worth keeping,
but this reasoning makes it sound exact, and it is not.

The CHANGELOG records a smaller case of this being fixed once, as "Valid short proofs of
larger formulas were refused as malformed": the literal was bounded by the proof's length,
and `6 0` for a seven-variable formula was refused. Adding the formula's count fixed that
case and left this one.

Real proofs are unlikely to hit it through text, as their text is long and solvers number
new variables contiguously. It is likelier on short proofs and on the list and
`MemoryProof` paths, where the bound is only the literal count.

## Engines affected

Both, identically, since the guard runs before them. In the default run, 1460 runs were
refused as text (one per flag pair). Another 2570 engine runs were refused only on the list
and `MemoryProof` paths, where the same proof had passed as text.

## Fix

Fairly clear: `cnf.py` has already settled this for headers, with `HEADER_VARS_FLOOR`
(2^20), described there as "affordable to accept from a hostile header". The same floor
would do here:

```python
limit = max(formula.nvars + max(occurrences, text_len), HEADER_VARS_FLOOR)
```

That still refuses `99999999999 0`, which `test_a_proof_literal_larger_than_the_file_is_rejected`
expects. It would let a short proof ask for about 100 MB through the native path. Whether
that is acceptable is the maintainer's choice, and is why the fix is not entirely clear.

## Proposed test

For `tests/test_untrusted_input.py`. Run against the current tree, it fails with the
`ValueError` above.

```python
    def test_a_fresh_variable_may_leave_a_gap(self):
        """`50 0` is vacuously RAT. Nothing obliges a proof to use 3 to 49."""
        f = parse_dimacs("p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n")
        self.assertTrue(check_proof(f, "50 0\n1 0\n0\n", engine="python").ok)

    def test_text_and_a_list_of_steps_bound_literals_alike(self):
        f = parse_dimacs("p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n")
        steps = [("a", (from_dimacs(6),)), ("a", (from_dimacs(1),)), ("a", ())]
        self.assertTrue(check_proof(f, "6 0\n1 0\n0\n", engine="python").ok)
        self.assertTrue(check_proof(f, steps, engine="python").ok)
```

This needs `from_dimacs` imported from `dratify`.
