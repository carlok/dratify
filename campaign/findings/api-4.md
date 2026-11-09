# api-4: the variable bound depends on the shape and on the text's length

**Proposed severity: Bug.** `check_proof` raises on a step that is RAT on its first literal,
under no documented rule, and whether it raises depends on how the same proof is written
down. This is not in "Honest limitations". It is never unsound: it only refuses.

## Minimal case

Formula `(1 2)`, proof the single step `(5)`, a fresh variable, vacuously RAT. Then `(7)`,
which flips on a comment.

## Reproducer

```python
import cdclkit_native
from dratify import MemoryProof, parse_dimacs, check_proof, from_dimacs, register_native
from campaign import oracle
register_native(cdclkit_native)
f = parse_dimacs("p cnf 2 1\n1 2 0\n")
print(oracle.rat([[1, 2]], [5], 5), oracle.preserves_sat([[1, 2]], [5]))
print(oracle.rat([[1, 2]], [7], 7), oracle.preserves_sat([[1, 2]], [7]))
m = MemoryProof(); m.add((from_dimacs(5),))
def show(name, proof):
    for engine in ("python", "native"):
        try:
            r = check_proof(f, proof, engine=engine)
            print(f"{name:24} {engine:7} rat_steps={r.rat_steps} failed_step={r.failed_step}")
        except ValueError as e:
            print(f"{name:24} {engine:7} ValueError: ...{str(e)[-34:]}")
show("text '5 0\\n'", "5 0\n")
show("list", [("a", (from_dimacs(5),))])
show("MemoryProof", m)
show("to_text", m.to_text())
show("text '7 0\\n'", "7 0\n")
show("with a comment", "c pad pad pad\n7 0\n")
```

Actual output:

```
True True
True True
text '5 0\n'             python  rat_steps=1 failed_step=-1
text '5 0\n'             native  rat_steps=1 failed_step=-1
list                     python  ValueError: ...is proof can account for at most 3
list                     native  ValueError: ...is proof can account for at most 3
MemoryProof              python  ValueError: ...is proof can account for at most 3
MemoryProof              native  ValueError: ...is proof can account for at most 3
to_text                  python  rat_steps=1 failed_step=-1
to_text                  native  rat_steps=1 failed_step=-1
text '7 0\n'             python  ValueError: ...is proof can account for at most 6
text '7 0\n'             native  ValueError: ...is proof can account for at most 6
with a comment           python  rat_steps=1 failed_step=-1
with a comment           native  rat_steps=1 failed_step=-1
```

Should be: all of these `rat_steps=1, failed_step=-1`, as the oracle says, and as
`DRATChecker` directly gives. The same `MemoryProof` is judged through `to_text` and refused
without it. Whitespace and comments are "only whitespace" by `parse_proof`'s own docstring,
yet they decide it: the generator also caught `11 0` on a 4-variable formula raising without
a trailing newline and being judged with one.

## Cause

`src/dratify/proof.py:736`: `limit = formula.nvars + max(occurrences, text_len)`, with
`text_len` being 0 unless the proof was a string (`proof.py:782`). The docstring's reasoning
(`proof.py:724-728`), "a proof can only introduce variables it mentions, so the largest
index is at most the formula's count plus the number of literal occurrences", does not
follow: a proof can name variable 1000 with one occurrence. Nothing makes fresh variables
consecutive, and drat-trim does not require it. The check is engine-independent, so both
engines are affected alike.

## Fix

Not obvious, because the bound exists to stop a short proof asking for 10^11 variables
(CHANGELOG 0.1.7). A shape-independent rule, for instance the formula's count plus
`max(occurrences, HEADER_VARS_FLOOR)` from `cnf.py`, keeps the guard and refuses only past
a million variables, the amount `parse_dimacs` already accepts from any file. Dropping
`text_len` would refuse big-variable proofs in long texts that pass today, so the floor
would need weighing against the 0.1.x "keeps every proof the old text bound accepted"
promise.

## Proposed test

```python
class TestTheBoundIgnoresTheShape(unittest.TestCase):
    def setUp(self):
        self.f = parse_dimacs("p cnf 2 1\n1 2 0\n")

    def test_a_fresh_variable_is_judged_the_same_in_every_shape(self):
        memory = MemoryProof()
        memory.add((from_dimacs(5),))
        for proof in ("5 0\n", [("a", (from_dimacs(5),))], memory):
            r = check_proof(self.f, proof, engine="python")
            self.assertEqual((r.ok, r.rat_steps, r.failed_step), (False, 1, -1))

    def test_a_comment_does_not_decide_whether_a_proof_is_judged(self):
        plain = check_proof(self.f, "7 0\n", engine="python")
        noted = check_proof(self.f, "c pad pad pad\n7 0\n", engine="python")
        self.assertEqual(plain.rat_steps, noted.rat_steps)
```
