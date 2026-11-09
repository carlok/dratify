# literals-3: a valid proof raises when a fresh variable's number is above the literal bound

**Proposed severity: Bug.** A proof that is valid under dratify's own rules gets a
`ValueError`, and whether it does depends on how much text surrounds it. Also reported as
`api-4` and `engines-3`.

This fails closed, so it is not a soundness problem. The guard itself is deliberate. Its
docstring records it, but README and AGENTS.md do not mention it, and CHANGELOG 0.1.7 fixed
the same complaint for formula variables, so I do not read it as a documented limitation.
The owner may disagree.

## Minimal case

```
formula: p cnf 0 0
proof:   7 0
```

A variable no clause mentions, so RAT on it is vacuous. Variable 7 needs nothing else:
below the bound the same line is accepted, and the number means nothing to the oracle.

## Reproducer

```python
import cdclkit_native
from campaign import oracle
from dratify import check_proof, parse_dimacs, parse_proof, register_native
register_native(cdclkit_native)

SQUARE = "p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n"
f = parse_dimacs(SQUARE)
for p in ("3 1 0\n1 0\n0\n", "99 1 0\n1 0\n0\n", "c " + "x" * 100 + "\n99 1 0\n1 0\n0\n"):
    for e in ("python", "native"):
        try:
            r = check_proof(f, p, engine=e); print(e, repr(p[:12]), r.ok, r.reason)
        except ValueError as ex:
            print(e, repr(p[:12]), "ValueError:", ex)
print(oracle.rup([[1, 2], [1, -2], [-1, 2], [-1, -2]], [99, 1]))

f0 = parse_dimacs("p cnf 0 0\n")
for shape in ("7 0\n", "c xxxxxx\n7 0\n", parse_proof("c xxxxxx\n7 0\n")):
    try:
        r = check_proof(f0, shape, engine="python")
        print(repr(shape), "rat_steps", r.rat_steps, "failed_step", r.failed_step)
    except ValueError as ex:
        print(repr(shape), "ValueError:", ex)
print(oracle.rat([], [7], 7))
```

Actual output:

```
python '3 1 0\n1 0\n0\n' True empty clause derived and every step verified
native '3 1 0\n1 0\n0\n' True empty clause derived and every step verified
python '99 1 0\n1 0\n0' ValueError: proof step 1: literal 99 names variable 99, but a 2-variable formula and this proof can account for at most 15
native '99 1 0\n1 0\n0' ValueError: proof step 1: literal 99 names variable 99, but a 2-variable formula and this proof can account for at most 15
python 'c xxxxxxxxxx' True empty clause derived and every step verified
native 'c xxxxxxxxxx' True empty clause derived and every step verified
True
'7 0\n' ValueError: proof step 1: literal 7 names variable 7, but a 0-variable formula and this proof can account for at most 4
'c xxxxxx\n7 0\n' rat_steps 1 failed_step -1
[('a', (12,))] ValueError: proof step 1: literal 7 names variable 7, but a 0-variable formula and this proof can account for at most 1
True
```

So:

- A real refutation of the square raises with `99` in it and verifies with `3`.
- The same refutation verifies again once a long comment is added above it.
- The same proof as text passes and as `parse_proof(text)` raises, on one engine.

Expected: the same verdict in all of these. The oracle says the step is RUP, or RAT on its
first literal, whatever the number is. `parse_dimacs` takes any variable up to 2^20 from a
one-line file, so `9 0` is fine as a formula and refused as a proof.

## Cause and engines

`src/dratify/proof.py:736`, in `_validate_steps`, before either engine runs:

```python
limit = formula.nvars + max(occurrences, text_len)
```

The docstring's argument is "a proof can only introduce variables it mentions, so the
largest index is at most the formula's count plus the number of literal occurrences". That
holds only if fresh variables are numbered contiguously. DRAT does not require it, and a
preprocessor may name definitions from any base.

Both engines are affected, identically.

## Is the fix clear?

Yes. Use the floor the header already uses, so a hostile literal costs what a hostile
header costs (`HEADER_VARS_FLOOR`, 2^20):

```python
limit = max(formula.nvars + max(occurrences, text_len), HEADER_VARS_FLOOR)
```

`test_a_proof_literal_larger_than_the_file_is_rejected` (99999999999) and
`test_a_huge_literal_in_a_list_is_refused_quickly` (variable 10^11) are above the floor and
still pass. Above the floor the text-length dependence stays, but a floor removes it for
every proof that is not enormous or hostile.

## Reach in this generator

Label `bound-refuses-valid`, 4796 occurrences. `bound_at_limit_accepted` confirms the
boundary is where the code says it is, and `bound_huge_refused` confirms the guard still
refuses above the floor.

## Proposed failing test

```python
class TestFreshVariableNumbers(unittest.TestCase):
    SQUARE = "p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n"

    def test_a_fresh_variable_number_does_not_decide_the_verdict(self):
        f = parse_dimacs(self.SQUARE)
        for var in (3, 99, 1000):
            with self.subTest(var=var):
                self.assertTrue(check_proof(f, f"{var} 1 0\n1 0\n0\n",
                                            engine="python").ok)

    def test_text_and_list_shapes_agree_on_the_bound(self):
        f = parse_dimacs("p cnf 0 0\n")
        text = "c xxxxxx\n7 0\n"
        self.assertEqual(check_proof(f, text, engine="python").rat_steps,
                         check_proof(f, parse_proof(text), engine="python").rat_steps)
```
