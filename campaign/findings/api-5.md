# api-5: `check` on a used checker reports things that did not happen

**Proposed severity: Bug.** Never unsound: the formula really is unsatisfiable whenever
`ok=True` appears here, since the root conflict came from verified steps. But AGENTS.md says
a proof that never reaches the empty clause "is **not** a refutation", and that `reached_empty`
answers "was the empty clause actually derived?". This is the only way to read a Rust
stream's result, so it is not an obscure path there. If the author holds that `check` is
single-use, this drops to a documentation gap, but nothing says so today.

## Minimal case

The square `(1 2) (1 -2) (-1 2) (-1 -2)`, one step `(1)`, no empty clause. Then a second
`check` with nothing in it.

## Reproducer

```python
from dratify import parse_dimacs
from dratify.proof import DRATChecker
f = parse_dimacs("p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n")
one = [("a", (0,))]   # the unit (1), and no empty clause
whole = DRATChecker(f).check(one)
print("whole   ", whole.ok, whole.reached_empty, repr(whole.reason))
c = DRATChecker(f); c.check_step("a", (0,)); r = c.check([])
print("stepped ", r.ok, r.reached_empty, repr(r.reason))
c = DRATChecker(f); c.check(one); r = c.check([])
print("pieces  ", r.ok, r.reached_empty, repr(r.reason))
good = one + [("a", ())]
w = DRATChecker(f).check(good); c = DRATChecker(f)
for s in good: c.check_step(*s)
print("complete", repr(w.reason), "/", repr(c.result.ok), repr(c.result.reason), "/", repr(c.check([]).reason))
g = parse_dimacs("p cnf 2 1\n-1 2 0\n")
c = DRATChecker(g, check_rat=False); print(c.check_step("a", (0, 3)), repr(c.result.reason))
r = c.check([]); print(r.failed_step, repr(r.reason))
x = parse_dimacs("p cnf 1 2\n1 0\n-1 0\n")
print("refuted input, 1 step:", DRATChecker(x).check([("a", ())]).steps, end=" / ")
c = DRATChecker(x); c.check_step("a", ()); print(c.check([]).steps)
```

Actual output:

```
whole    False False 'every step verified, but the proof never derives the empty clause'
stepped  True True 'input formula is refuted by unit propagation alone'
pieces   True True 'input formula is refuted by unit propagation alone'
complete 'empty clause derived and every step verified' / False '' / 'input formula is refuted by unit propagation alone'
False 'clause is not RUP (RAT checking disabled)'
1 'every step verified, but the proof never derives the empty clause'
refuted input, 1 step: 0 / 1
```

What each line shows, all against "every shape gives the same result on every field":

1. The same steps, driven by hand or in two pieces, turn `ok=False, reached_empty=False` into
   `ok=True, reached_empty=True`. No empty clause was derived, and `(1 2) ...` is not refuted
   by propagation alone, which the oracle confirms: `oracle.propagate(F)[0]` is False.
2. A complete, valid proof gets the wrong reason. Very common: any proof whose lemmas conflict
   at the root before its `0`. And if `check` is split after such a lemma, the second piece
   is not read at all, so `steps` and `rup_steps` come up short (`rust_check_in_two_pieces` on
   generator instance 2: 3 steps against 8).
3. After a rejected step, `failed_step=1` sits next to "every step verified".
4. `check_step` alone leaves `ok=False, reason=""` after a complete refutation. That one may
   be fine as the contract is its returned bool, so the generator does not count it. But
   it needs saying, and Python users reading `c.result.ok` get False.
5. An input refuted by propagation gives `steps=0` from `check`, and counts from `check_step`.

Also, Python's `check` returns its own `self.result` each time, so an earlier result changes
under the caller: `a = c.check(x); c.check(y)` overwrites `a`. Rust returns a clone.

## Cause

`src/dratify/proof.py:686-690` tests `_root_conflict` on entry, assuming it can only have come
from the input; `check_step` sets it (via `_add_lemma`, `proof.py:677,680,682`). `:697-704`
then overwrite `reason` whatever happened before. Rust is the same: `rust/src/checker.rs:533-538`
and `:549-557`. And Rust's `result` field is private (`checker.rs:248`) with no getter, so
`check(&[])` is the only way a Rust stream can read its counters. Python and Rust agree
with each other on all of this.

## Fix

Clear for the wrong fields: decide "input refuted" once in the constructor, in a flag `check`
tests, and leave `_root_conflict` to `_is_rup`; keep the reason of a failed step. Rust also
wants a `pub fn result(&self) -> &CheckResult`. Whether a stream with a root conflict and no `0`
counts as a refutation stays false, per AGENTS.md. Or document `check` as single-use and add a
`finish()`. That is the author's choice.

## Proposed test

```python
class TestDrivingByHandMatchesCheck(unittest.TestCase):
    def setUp(self):
        self.f = parse_dimacs("p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n")

    def test_no_empty_clause_is_not_reached_empty_however_it_is_driven(self):
        whole = DRATChecker(self.f).check([("a", (0,))])
        self.assertFalse(whole.reached_empty)
        c = DRATChecker(self.f)
        self.assertTrue(c.check_step("a", (0,)))
        after = c.check([])
        self.assertEqual((after.ok, after.reached_empty, after.reason),
                         (whole.ok, whole.reached_empty, whole.reason))

    def test_a_reason_is_not_overwritten_after_a_rejected_step(self):
        g = parse_dimacs("p cnf 2 1\n-1 2 0\n")
        whole = DRATChecker(g, check_rat=False).check([("a", (0, 3))])
        c = DRATChecker(g, check_rat=False)
        self.assertFalse(c.check_step("a", (0, 3)))
        self.assertEqual(c.check([]).reason, whole.reason)
```
