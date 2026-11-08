# drat_trim-10: drat-trim can segfault on a final empty clause with no conflict behind it

**Proposed severity: Note.** A memory error in drat-trim at commit
2e3b2dc0ecf938addbd779d42877b6ed69d9a985, on proofs dratify and drat-trim both refuse. No verdict
depends on it, as long as the crash is not read as a verdict. It is a Note here because the run
must handle it, and it is the reason a harness cannot trust one run of this binary.

## Minimal case

Formula `(1 2)`, proof `0`, under AddressSanitizer:

```
ERROR: AddressSanitizer: heap-buffer-overflow
READ of size 4
    #0 in verify drat-trim.c:790
```

The plain build reads that int too, and what it does next depends on the heap. On this formula it
answers `s NOT VERIFIED`. On this one, from seed 2, it crashed 25 times out of 25:

```python
F = [[-9, -6, 2], [-4, -6], [-8, 9], [7, -5, -2], [9, -10], [1, -7, -2], [5, -6, -2], [9, -3],
     [8, 9, -3], [9, -7], [10, 2, 9], [-5, -6, 10], [-7, 1, -3], [-7, 4, 6], [-6, -10, 3], [7, -4, 5]]
proof = [(-2, -4, -10), (1,), (-5, 6, 4), (-4, -9, 1), (-6, 2), (-8,), (-8,), (10, -1, 2), ()]
```

Others crashed on between a quarter and a half of their runs.

## Why it does not change a verdict

Line 790 asks `!lemmas[1]` of every step. An empty clause has `lemmas[0] == 0`, so `lemmas[1]` is
the next clause's header, and for the last clause in the database it is one int past the
allocation. If that int is 0, the step goes on to line 845, "conflict claimed, but not detected",
and `s NOT VERIFIED`. If it is not, line 842 calls `addWatch` with literal 0 and with whatever that
int was, and the watch list access crashes. `-f` also reads this clause's pivot at line 618, which
line 1202 never set. The step is reached only when propagation has found no conflict, so the answer
it would give is NOT VERIFIED.

A valid refutation never reaches it: a conflict jumps to verification at line 849 first. Every
crash in this corner was on a proof dratify also refused.

## What the generator does

It repeats a crash up to five times. Then it tests the cause on every instance: without the empty
clause the proof must not crash in ten runs, and with a second empty clause after it, the read
stays inside the database, and the answer must be `s NOT VERIFIED`. That answer is the one judged.
Anything else fails the run as `drat_trim_crash_unexplained`. `--self-test` checks both paths on
shell stubs, since the real crash depends on the heap.

## Counts

Proofs that crashed at least once, seeds 1, 2, 3, default mode: 2, 4, 1. On all five tries: 0, 3, 1.
Other modes are alike and are in the results. These vary
between runs of the same seed. `-S` is counted separately, since it is not judged.

## Test

No dratify behaviour to pin.
