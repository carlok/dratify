# ok_empty-4: where a refutation ends, three behaviours the docs do not state

**Proposed severity: Note.** No wrong verdict and no contradiction that matters. All three
are the same on both engines, and the generator holds them on every instance. They are
written down because each is a place someone could be surprised, and the README and
CHANGELOG words come close to saying otherwise.

drat-trim is not installed here, so this says nothing about what it does.

## Minimal cases

| | formula | proof | `ok` | `reached_empty` | `steps` |
|---|---|---|---|---|---|
| a. conflict, no `0` | square | `1 0` | False | False | 1 |
| b. step after the empty clause | square | `1 0`, `0`, `3 0` | True | True | 2 |
| c. input refuted by propagation | `1 / -1` | `2 0` | True | True | 0 |

"square" is `1 2 / 1 -2 / -1 2 / -1 -2`.

## Reproducer

Run from the repo root, with `cdclkit_native` installed:

```python
from dratify import parse_dimacs, check_proof, register_native
import cdclkit_native
from campaign import oracle

register_native(cdclkit_native)
SQ = "p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n"
UP = "p cnf 1 2\n1 0\n-1 0\n"
for label, f, p in (("a", SQ, "1 0\n"), ("b", SQ, "1 0\n0\n3 0\n"), ("c", UP, "2 0\n")):
    for engine in ("python", "native"):
        r = check_proof(parse_dimacs(f), p, engine=engine)
        print(label, engine, r.ok, r.reached_empty, r.steps, repr(r.reason))
square = [[1, 2], [1, -2], [-1, 2], [-1, -2]]
print("a: refuted by propagation after the lemma", oracle.propagate([*square, [1]])[0])
print("b: tail step is RUP once refuted", oracle.rup([*square, [1], []], [3]))
print("c: unsatisfiable", not oracle.satisfiable([[1], [-1]]))
```

Actual output:

```
a python False False 1 'every step verified, but the proof never derives the empty clause'
a native False False 1 'every step verified, but the proof never derives the empty clause'
b python True True 2 'empty clause derived and every step verified'
b native True True 2 'empty clause derived and every step verified'
c python True True 0 'input formula is refuted by unit propagation alone'
c native True True 0 'input formula is refuted by unit propagation alone'
a: refuted by propagation after the lemma True
b: tail step is RUP once refuted True
c: unsatisfiable True
```

## What each one means

**a. Reaching a conflict is not enough; `0` has to be written.** The checker already holds a
root conflict, and still answers False. This is what AGENTS.md documents ("never reaches the
empty clause is not a refutation"), and it is on the safe side. It is a completeness choice,
and it matters for a proof cut just before its last line.

**b. Nothing after the first empty clause is checked.** `check` stops there
(`src/dratify/proof.py:695`, `rust/src/checker.rs:545`). The reason still says "every step
verified", and the 0.1.10 entry in CHANGELOG calls the same wording about an unchecked step
a bug: "a forward checker promises to check every step the solver wrote". Here the sentence
holds, though only vacuously: with the empty clause present every addition is RUP, and a
deletion always passes, so no tail step could have failed. The honest signal is `steps`,
which is 2 for a three-step proof. Malformed text or a negative literal in the tail does
still raise, because parsing and `_validate_steps` read the whole proof first.

**c. On an input refuted by propagation, the proof is not read at all.** `ok` and
`reached_empty` are True with `steps=0` (`proof.py:686`, `checker.rs:533`), whatever the proof
says, including no proof. The verdict is right and the reason is plain, but AGENTS.md
describes `reached_empty` as "was the empty clause actually derived?", and here no step
derived it. README's "every step is verified" has this exception too.

## What to do

One or two sentences in AGENTS.md or README's "What it checks" would cover all three. No
code change is proposed.

## Proposed test

These pass today, and pin the behaviour so a change to it is deliberate.

```python
import unittest

from dratify import check_proof, parse_dimacs

SQUARE = "p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n"


class TestWhereARefutationEnds(unittest.TestCase):
    def test_a_conflict_without_the_empty_clause_is_not_a_refutation(self):
        r = check_proof(parse_dimacs(SQUARE), "1 0\n", engine="python")
        self.assertFalse(r.ok)
        self.assertFalse(r.reached_empty)

    def test_nothing_after_the_empty_clause_changes_the_result(self):
        f = parse_dimacs(SQUARE)
        short = check_proof(f, "1 0\n0\n", engine="python")
        long = check_proof(f, "1 0\n0\n3 0\nd 1 2 0\nd 0\n0\n", engine="python")
        for field in short.__slots__:
            self.assertEqual(getattr(short, field), getattr(long, field), field)
        self.assertEqual(long.steps, 2)

    def test_a_refuted_input_needs_no_proof_and_reads_none(self):
        f = parse_dimacs("p cnf 1 2\n1 0\n-1 0\n")
        for proof in ("", "2 0\n"):
            r = check_proof(f, proof, engine="python")
            self.assertTrue(r.ok)
            self.assertTrue(r.reached_empty)
            self.assertEqual(r.steps, 0)


if __name__ == "__main__":
    unittest.main()
```
