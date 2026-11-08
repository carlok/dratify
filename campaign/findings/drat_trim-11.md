# drat_trim-11: dratify's root-unit test is not drat-trim's reason test, and no verdict moved

**Proposed severity: Note.** The claim in dratify's documents, that its rule is drat-trim's
operational reading "approximated" by a root-unit test, holds for verdicts on everything run here.
The two rules keep different clauses, as the documents say, and one README sentence draws a
consequence from that which does not follow. Checked with drat-trim at commit
2e3b2dc0ecf938addbd779d42877b6ed69d9a985.

## What each one tests

dratify, `src/dratify/proof.py` `_unit_at_root`: any clause, as a set, with exactly one literal true
and the others false at the root.

drat-trim.c 807: `(S->reason[abs (lemmas[0])] - 1) == (lemmas - S->DB)`. This is identity, not
shape: is this very clause the one recorded as the reason for its first literal? Clauses of one
literal are dropped earlier (1168-1173 in the default mode, 794-799 in `-f`).

So every clause drat-trim keeps, dratify keeps, and not the reverse. A reason has the shape, and
keeps it as the root only grows.

## Where they differ

| formula | deletions | dratify | drat-trim `-v` |
|---|---|---|---|
| `(1) (2) (-1 2)` | `d -1 2` | ignored | applied: the reason for 2 is `(2)` |
| `(1) (-1 2) (-1 2)` | `d -1 2` twice | both ignored, 2 copies stay | one applied, 1 copy stays |
| `(1) (3) (-1 2) (-3 2)` | `d -1 2`, `d -3 2` | both ignored | keeps the one recorded, here `(-1 2)`, and applies the other |

`-v` prints `c ignoring deletion instruction` for each one it keeps. `-W`, which exits 80 when it
keeps one, exits 80 on the last two and runs normally on the first.

## Why the verdict should not move

Take a clause `C` with one literal `t` true and the rest false at the root, which is not the
recorded reason for `t`. The root assignment is never undone in either checker, so:

- `C` can never propagate or conflict: every variable in it is set, and it is satisfied.
- As a RAT candidate, `C` matters only to a lemma with pivot `p` where `-p` is in `C`. If `-p` is a
  false literal of `C`, then `p` is true at the root, and the lemma is RUP. If `-p` is `t`, then `p`
  is false at the root, the real reason for `t` is also a candidate, and is kept by both. The
  resolvent with it is RUP only if the lemma itself is RUP, since its other literals are false at
  the root.

So whether `C` is present can change no step's outcome. drat-trim adds a shortcut for the second
case at line 666, refusing a false pivot outright, with the same result. This is an argument, not a
proof checked by machine, and it is backed by the test below.

## The test

`deletion_rule` in the generator takes the deletions in each proof up to the first conflict and up
to any step dratify rejects, which is where a proof relying on a clause being gone would show. It
compares what dratify keeps with what `drat-trim -v` says it keeps. On each proof where they differ,
it changes the reading on either side and asks again: drat-trim with those deletion lines removed
from the proof, so it keeps them too, in its default mode and `-f`; and dratify's Python engine with
those deletions honoured, so it holds drat-trim's rule. A verdict that moves fails the run, as does
a clause only drat-trim keeps. `gen_lookalike` adds 1,000 proofs aimed at this, half on formulas with
a refutation available.

The first version of this test did fail, and it was the test that was wrong. drat-trim's parser
matches a deletion to a copy before it knows the copy is a reason, so a second deletion of a reason
it kept finds nothing and warns "does not occur". No clause goes, as in dratify, where it counts as
ignored. Treating that as a clause drat-trim had applied made dratify erase a real reason, which is
the old defect, and rightly moved the verdict. The run now counts those apart, as repeats below, and
`--self-test` pins one.

| | seed 1 corpus | seed 1 look-alikes | seed 2 both | seed 3 both |
|---|---:|---:|---:|---:|
| proofs compared | 1,526 | 1,000 | 2,529 | 2,515 |
| clauses both keep | 214 | 620 | 862 | 869 |
| clauses only dratify keeps | 57 | 701 | 798 | 818 |
| clauses only drat-trim keeps | 0 | 0 | 0 | 0 |
| repeats on a clause both keep | 1 | 272 | 257 | 246 |
| proofs where the rules differ | 27 | 677 | 726 | 719 |
| of those, dratify and default drat-trim agree | 27 | 623 | 685 | 672 |
| of those, dratify accepts | 0 | 197 | 189 | 180 |
| verdicts that moved | 0 | 0 | 0 | 0 |

The disagreements with drat-trim that remain on these proofs have other causes, each with its own
finding. None is the deletion rule.

## The sentences

Accurate: `src/dratify/proof.py` 51-53, "This is drat-trim's operational reading of deletion
(Rebola-Pardo and Biere, 2018), approximated by the root-unit test: a clause that merely looks like
a reason is kept along with the real ones." The same in `rust/src/checker.rs` and `REPORT.md`. It
would help to say that the approximation shows in `ignored_deletions`, which is larger than the
count of deletions drat-trim ignores, and not in a verdict.

Not supported, `README.md` 282-283: "A proof that relies on such a clause being gone can be
rejected." After the sentence before it, "such a clause" reads as one that only looks like a reason.
By the argument above no proof can rely on that, and none did here. The sentence is true of a real
reason clause, and would be right if it said so. `src/` was not changed, and neither was the README.

## Test

```python
import unittest

from dratify import check_proof, parse_dimacs


class TestLookAlikeReasons(unittest.TestCase):
    def test_a_clause_with_a_reasons_shape_is_kept(self):
        r = check_proof(parse_dimacs("p cnf 2 3\n1 0\n2 0\n-1 2 0\n"), "d -1 2 0\n", engine="python")
        self.assertEqual((r.deletions, r.ignored_deletions), (0, 1))

    def test_it_does_not_block_a_refutation(self):
        cnf = "p cnf 4 7\n1 0\n2 0\n-1 2 0\n3 4 0\n3 -4 0\n-3 4 0\n-3 -4 0\n"
        r = check_proof(parse_dimacs(cnf), "d -1 2 0\n3 0\n0\n", engine="python")
        self.assertTrue(r.ok)
```
