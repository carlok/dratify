# drat_trim-8: drat-trim's parser reads `d 0`, then swallows the next token of the proof

**Proposed severity: Note.** dratify reads the line as written. It is a parsing quirk of
drat-trim at commit 2e3b2dc0ecf938addbd779d42877b6ed69d9a985, on a line no solver writes. Found by
reading its parser, not by the default seed.

## Minimal case

Formula `(1 2) (-1 2) (1 -2) (-1 -2)`, which is unsatisfiable. Proof:

```
d 0
1 0
0
```

## Reproducer and output

```python
from dratify import parse_dimacs, check_proof

cnf = "p cnf 2 4\n1 2 0\n-1 2 0\n1 -2 0\n-1 -2 0\n"
r = check_proof(parse_dimacs(cnf), "d 0\n1 0\n0\n", engine="python")
print(r.ok, r.ignored_deletions)   # True 1
r = check_proof(parse_dimacs(cnf), "1 0\n0\n", engine="python")
print(r.ok)                        # True
```

The native engine returns the same. drat-trim says `s NOT VERIFIED` on the first proof, in its
default mode and in `-f`, and `s VERIFIED` on the second. Its output names what happened:

```
c WARNING: backward mode ignores deletion of (pseudo) unit clause [0] 1 0
c conflict claimed, but not detected
```

## Why it is not a bug

An empty deletion names no clause, and dratify ignores it and counts it. drat-trim.c 1117 reads
`" d  %i "`, which takes the `0` as the first literal with `del` set. Line 1121 then treats 0 as "no
literal yet" and reads again, so `1` joins the deletion, and the lemma `(1)` is gone from the proof.
Removing the `d 0` line changes drat-trim's verdict and not dratify's, which is the generator's
test for this category.

## Counts

Zero on seeds 1, 2 and 3, in every mode. `--self-test` pins the example above. `mutate` can write
this line, so a run can reach it.

## Test

```python
import unittest

from dratify import check_proof, parse_dimacs


class TestDeletionOfNothing(unittest.TestCase):
    def test_it_is_ignored_and_the_next_line_is_read(self):
        cnf = "p cnf 2 4\n1 2 0\n-1 2 0\n1 -2 0\n-1 -2 0\n"
        r = check_proof(parse_dimacs(cnf), "d 0\n1 0\n0\n", engine="python")
        self.assertTrue(r.ok)
        self.assertEqual(r.ignored_deletions, 1)
```
