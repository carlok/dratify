# api-6: `ProofWriter` and `MemoryProof.to_text` write a different clause for a negative literal

**Proposed severity: Note.** Not unsound: a checker judges whatever text comes out. None of the
brief's Bug definitions apply. It is the writing half of the mistake 0.1.7 closed on reading,
and it sends the failure far from its cause, so it is worth having on record.

## Minimal case

One `add` with one negative literal.

## Reproducer

```python
import io
from dratify import MemoryProof, ProofWriter, check_proof, parse_dimacs
f = parse_dimacs("p cnf 3 1\n1 2 0\n")
for lit in (-5, -1, -2):
    m = MemoryProof(); m.add((lit,))
    b = io.StringIO()
    with ProofWriter(b) as w: w.add((lit,))
    try: check_proof(f, m, engine="python"); v = "accepted"
    except ValueError as e: v = "ValueError"
    print(lit, repr(b.getvalue()), repr(m.to_text()), v)
```

Actual output:

```
-5 '2 0\n' '2 0\n' ValueError
-1 '0 0\n' '0 0\n' ValueError
-2 '0 0\n' '0 0\n' ValueError
```

Should be: `ValueError` from all three, or at least the same answer. The same `MemoryProof` is
refused as itself and accepted as its `to_text()`. `-5` becomes the unrelated clause `(2)`,
and `-1` and `-2` write `0 0`, which reads as two empty clauses: no clause of the solver's
remains in the proof, and the checker reports a failure of a step nobody wrote.

## Cause

`to_dimacs` (`src/dratify/lits.py:105-108`) does arithmetic with no range check, and
`ProofWriter.add`, `.delete` and `MemoryProof.to_text` (`src/dratify/proof.py:144,150,198`) trust
it. The module docstring of `lits.py` says nothing inside sees a signed literal, but these sit at
the boundary. Same on both engines, since text is parsed once in Python.

## Fix

Clear: raise `ValueError` for a negative literal in `to_dimacs`, the same message
`CNF.add` already uses. `ProofWriter` runs in the solver's hot path, so measure that; cdclkit
writes internal literals and will not hit it.

## Proposed test

```python
class TestWritersRefuseWhatTheCheckerRefuses(unittest.TestCase):
    def test_a_negative_literal(self):
        with self.assertRaises(ValueError):
            ProofWriter(io.StringIO()).add((-5,))
        memory = MemoryProof()
        memory.add((-5,))
        with self.assertRaises(ValueError):
            memory.to_text()
```
