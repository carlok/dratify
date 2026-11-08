# rat-4: a fresh-variable RAT step can raise `ValueError` instead of being checked

**Proposed severity: Bug, with a judgement call.** The same proof is accepted or refused
depending on the shape of the input and on comment lines. Same root cause as `engines-3`,
`literals-3` and `api-4`, found independently; here it is a RAT rule that is cut off.

The call: a rejection that is a documented limitation is not a bug. `_validate_steps`
states this bound in its docstring, a private one, and it exists for a real reason
(hostile input). But the README and AGENTS.md do not mention it, CHANGELOG 0.1.3 says "A
proof may still introduce fresh variables -- that is what RAT is for", and the docstring's
argument for it is false, so I read it as a bug and not as a limit. If you read the
docstring as documentation, this is a Note. It is not a soundness problem: nothing wrong
is accepted, and the failure is loud and names the bound.

## Minimal case

Formula `(1)`, proof `8 0`. `8` is vacuously RAT: nothing contains `-8`. Removing the step
leaves nothing to reject, and any variable up to 5 is accepted.

## Reproducer

```bash
python - <<'EOF'
from campaign import oracle
from dratify import check_proof, parse_dimacs, register_native
from dratify.lits import from_dimacs
import cdclkit_native; register_native(cdclkit_native)
print("rat", oracle.rat([[1]], [8], 8), "preserves_sat", oracle.preserves_sat([[1]], [8]))
for e in ("python", "native"):
    for name, proof in (("text", "8 0\n"),
                        ("text with a comment", "c padding padding\n8 0\n"),
                        ("list", [("a", (from_dimacs(8),))])):
        try:
            r = check_proof(parse_dimacs("p cnf 1 1\n1 0\n"), proof, engine=e)
            print(e, name, "failed_step", r.failed_step, "rat_steps", r.rat_steps)
        except ValueError as ex:
            print(e, name, "ValueError:", ex)
EOF
```

Actual output:

```
rat True preserves_sat True
python text ValueError: proof step 1: literal 8 names variable 8, but a 1-variable formula and this proof can account for at most 5
python text with a comment failed_step -1 rat_steps 1
python list ValueError: proof step 1: literal 8 names variable 8, but a 1-variable formula and this proof can account for at most 2
native text ValueError: proof step 1: literal 8 names variable 8, but a 1-variable formula and this proof can account for at most 5
native text with a comment failed_step -1 rat_steps 1
native list ValueError: proof step 1: literal 8 names variable 8, but a 1-variable formula and this proof can account for at most 2
```

And the same proof by two routes: on `p cnf 5 1 / 1 2 0`, the text `-8 3 0` gives
`rat_steps=1`, while the list form raises "can account for at most 7".

**What it should be:** the step is RAT on its first literal under the oracle, so it should
be accepted, and the answer should not depend on a comment or on the input's shape.

## Suspected cause

`_validate_steps` at `src/dratify/proof.py:724-736`: `limit = formula.nvars +
max(occurrences, text_len)`. The docstring argues "a proof can only introduce variables it
mentions, so the largest index is at most the formula's count plus the number of literal
occurrences". That counts how many variables a proof can introduce, not what they may be
numbered: nothing makes fresh variables consecutive. `text_len` includes comments, so a
comment raises the bound.

**Engines:** both. Validation runs before either.

Real proofs rarely hit it: extension variables are usually numbered right after the
formula's, and a large text gives room. The header counts too, so `p cnf 8 1` with the same
proof passes. In this generator it is reached because the header is the largest variable
*used*, and fresh variables may be picked with gaps.

## Is the fix clear?

Not entirely, because the hostile-input guard is wanted. Options: bound variables by a
fixed floor, as the DIMACS header already does with `HEADER_VARS_FLOOR` (`cnf.py:44`, a
million variables accepted from any file), which removes the dependence on shape and on
comments; or remap fresh variables densely before sizing the arrays, which removes the
limit altogether. The floor is the smaller change.

## Proposed test

```python
import unittest

from dratify import check_proof, parse_dimacs
from dratify.lits import from_dimacs


class TestFreshVariableNumbering(unittest.TestCase):
    def test_a_fresh_variable_may_skip_numbers(self):
        f = "p cnf 1 1\n1 0\n"
        for proof in ("8 0\n", [("a", (from_dimacs(8),))]):
            with self.subTest(proof=proof):
                r = check_proof(parse_dimacs(f), proof, engine="python")
                self.assertEqual(r.failed_step, -1)
                self.assertEqual(r.rat_steps, 1)

    def test_a_comment_does_not_change_the_answer(self):
        f = "p cnf 1 1\n1 0\n"
        plain = check_proof(parse_dimacs(f), "8 0\n", engine="python")
        padded = check_proof(parse_dimacs(f), "c padding padding\n8 0\n", engine="python")
        self.assertEqual(plain.rat_steps, padded.rat_steps)

    def test_the_hostile_input_guard_still_holds(self):
        with self.assertRaises(ValueError):
            check_proof(parse_dimacs("p cnf 1 0\n"), "99999999999 0\n")
```
