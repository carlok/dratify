# drat_trim-3: `rate` verifies a proof that never writes the empty clause; dratify does not

**Proposed severity: Note.** dratify is stricter, and says so. The checker compared is
`rate` 0.3.0. `drat-trim` was not run, so whether it does the same is untested here.

## Minimal case

Formula `(1 2) (-1 2) (1 -2) (-1 -2)`, which is unsatisfiable. Proof, one line:

```
1 0
```

After `(1)`, propagation reaches a conflict, so the empty clause is one step away and is
not written.

## Reproducer and output

```python
from dratify import parse_dimacs, check_proof

cnf = "p cnf 2 4\n1 2 0\n-1 2 0\n1 -2 0\n-1 -2 0\n"
r = check_proof(parse_dimacs(cnf), "1 0\n", engine="python")
print(r.ok, r.reached_empty, r.rup_steps, r.failed_step)     # False False 1 -1
print(r.reason)   # every step verified, but the proof never derives the empty clause
```

The native engine returns the same. `rate` says `s VERIFIED` in all four modes (`-f -p`,
`-f -p -d`, `-p`, `-p -d`). With `oracle.replay`, every flavour finds the one step RUP and
`oracle.propagate(F + [[1]])` returns a conflict.

## Why it is not a bug

`AGENTS.md`, "`ok` and `reached_empty` are different questions": "A proof whose every step
verifies but which never reaches the empty clause is **not** a refutation". The rule exists
because truncated proofs were being accepted. The rejection is safe, documented, and
reported by a distinct `reason`, with `failed_step` left at -1.

A caller moving from an external checker should know: a solver proof cut off just before its
last line can verify there and be rejected here.

## Counts

Seed 1: 28 proofs, in every `rate` mode. `proofs_with_implicit_empty_clause` is a required
category.

## Suspected cause, and test

`src/dratify/proof.py:697-704`, as documented. A test that pins it:

```python
import unittest

from dratify import check_proof, parse_dimacs


class TestImplicitEmptyClause(unittest.TestCase):
    def test_a_propagation_conflict_is_not_a_written_empty_clause(self):
        cnf = "p cnf 2 4\n1 2 0\n-1 2 0\n1 -2 0\n-1 -2 0\n"
        r = check_proof(parse_dimacs(cnf), "1 0\n", engine="python")
        self.assertFalse(r.ok)
        self.assertFalse(r.reached_empty)
        self.assertEqual(r.failed_step, -1)
```
