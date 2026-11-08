# drat_trim-9: no mode of drat-trim honours a unit deletion and also checks a refutation

**Proposed severity: Note.** This is a limit on what the comparison can say, not a disagreement.
Read from drat-trim.c at commit 2e3b2dc0ecf938addbd779d42877b6ed69d9a985, and run.

## What the source says

| flag | what happens to a deletion of one literal | to a deletion of a reason | additions |
|---|---|---|---|
| none | dropped while parsing, with a warning (1168-1173) | ignored (807-814) | backward, only the core |
| `-f` | dropped (794-799), no warning | ignored (807-814) | forward, to the first conflict |
| `-S` | honoured: `removeUnit`, then `propagateUnits` (795-796) | honoured: the watches go, then `propagateUnits` (815-817) | not checked |
| `-p` | every deletion is dropped | the same | backward |
| `-W` | exit 80 at the warning | exit 80 (811), with no `s` line | as the rest |

The warning's text says "(pseudo) unit", but it fires only for one literal or none. Ignoring a real
reason of two or more literals is silent unless `-v` is given. `-W` stops at that too, whether or
not it printed anything.

So `-S` is the only reading close to the specified one, and it asks something else. It checks
deleted clauses and skips additions, appends a deletion of every clause still active, and stops
with no verdict when it reaches a written empty clause ("c ERROR: found empty clause during SAT
check"). Its `s VERIFIED` is no verdict on a refutation.

## Output

| seed 1 | `-S` says |
|---|---|
| satisfiable formula | `s VERIFIED` 190 |
| unsatisfiable, propagation refutes the input | `s VERIFIED` 67 |
| unsatisfiable, propagation does not | `s VERIFIED` 12 |
| `s NOT VERIFIED` | 814 |
| no verdict, mostly the error above | 507 |
| killed by a signal on all five tries | 3 |

An example of the third row is a pigeonhole formula of 4 pigeons and 3 holes with an empty proof.
It was not pursued: this corner has no claim to make about `-S`.

So the run counts `-S` and does not compare it with dratify. On the flavours' own example, the
proof in `drat_trim-2`, it does part from the default as expected: `s NOT VERIFIED` in `-S`, and
`s VERIFIED` in the default mode and `-f`, as `rate -f -p` and `rate -f -p -d` part.

## The two named cases, every mode

| proof | default | `-f` | `-S` | `-W` | dratify |
|---|---|---|---|---|---|
| `(1) (-1 2)`; `d -1 2`, `-2`, `0` | NOT VERIFIED, "conflict claimed, but not detected" | NOT VERIFIED at line 2 | NOT VERIFIED | exit 80, no `s` line | ok=False, failed_step=2 |
| `(1) (-1 2) (-2 3)`; `d -1 2`, `2` | NOT VERIFIED, "no conflict" | `s DERIVATION` | NOT VERIFIED, at the deletion of `(2)` it appended | exit 80, no `s` line | ok=False, failed_step=-1 |

`s DERIVATION` is `-f`'s "all lemmas preserve satisfiability" with no refutation, which is what
dratify's ok=False with no failed step means, so the generator counts that as agreement. In the
default mode the second proof's `2` is dropped from the proof as already true (803), and the run
ends for want of a conflict.

## Test

No dratify behaviour to pin. `gen_drat_trim --self-test` pins both named cases against the real
binary.
