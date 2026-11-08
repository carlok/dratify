# parsing-9: deleting a root reason clause buys a refutation (not a parsing bug)

**Proposed severity: Critical.** `ok=True` on a satisfiable formula, both engines. This is a
**duplicate** of deletion-1, root-1, api-2, engines-1, literals-1 and ok_empty-1, which own the
analysis. It is recorded because this generator found it independently: the end-to-end check
fired on rendered proof text with no parse difference at all, so the parser is not involved.

## Minimal case

Formula `-2 0`, `2 1 0`. Proof `d 2 1 0`, `-1 0`, `0`. Removing any clause or step makes dratify reject.

## Reproducer

```python
from dratify import check_proof, parse_dimacs, register_native
from campaign import oracle
import cdclkit_native
register_native(cdclkit_native)

f = parse_dimacs("p cnf 2 2\n-2 0\n2 1 0\n")
for engine in ("python", "native"):
    print(engine, check_proof(f, "d 2 1 0\n-1 0\n0\n", engine=engine).ok)
meant = [[-2], [2, 1]]
print(oracle.satisfiable(meant))
steps = [("d", (2, 1)), ("a", (-1,)), ("a", ())]
for flavour in oracle.FLAVOURS:
    judged, _ = oracle.replay(meant, steps, flavour)
    print(flavour, [s.acceptable for s in judged])
```

```
python True
native True
True
specified [True, True, False]
operational [True, False]
length-one [True, True, False]
```

Should be: `ok=False`. Every flavour rejects, so this is not a flavour difference.

## Suspected cause

`DRATChecker._erase` (`src/dratify/proof.py:524`) detaches the clause, and `_add_lemma`
(`proof.py:666-682`) then reads the root value it implied. `(-1)` is RAT because no clause has
`1` any more, and is falsified at a root where `1` is still true, which sets `_root_conflict`.
Rust: `erase` and `add_lemma` in `rust/src/checker.rs:322,500`. The fix is a decision about the
deletion flavour, so it belongs with the deletion corner's finding.

## Proposed test

```python
import unittest

from dratify import check_proof, parse_dimacs


class TestDeletingAReason(unittest.TestCase):
    def test_a_satisfiable_formula_is_not_refuted(self):
        f = parse_dimacs("p cnf 2 2\n-2 0\n2 1 0\n")
        self.assertFalse(check_proof(f, "d 2 1 0\n-1 0\n0\n", engine="python").ok)
```
