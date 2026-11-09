# root-3: a root refutation ends the checking

**Proposed severity: Note.** Both are sound, both engines agree, and neither
contradicts the documentation. Nothing here should be fixed to make the campaign
pass, and the harness models both readings as expected.

## (a) A formula refuted by propagation never looks at the proof

```python
from dratify import check_proof, parse_dimacs
r = check_proof(parse_dimacs("p cnf 2 2\n1 0\n-1 0\n"), "2 0\n", engine="python")
print(r.ok, r.reached_empty, r.steps, r.reason)
```

```
True True 0 input formula is refuted by unit propagation alone
```

`(2)` is not examined. The answer is right (`oracle.satisfiable` says False,
`oracle.propagate` conflicts), the reason says what happened and `steps=0` shows
nothing was counted. Text that cannot be parsed still raises, because parsing comes
first, and so does a literal over the `_validate_steps` bound.

Nothing is lost by not looking: on a multiset refuted by propagation every addition
is RUP by definition (`oracle.rup([[1], [-1]], [2])` is True). So README.md's
"Checking is **forward**: every step is verified" still holds in substance, and only
the step counters read differently. The same goes for steps after an accepted empty
clause, which are not counted: the `0` is accepted only on a multiset that is already
refuted. `proof.py:686-690`, `checker.rs:533-539`.

drat-trim is known to treat a trivially refuted input similarly. That comes from
memory: drat-trim is not on PATH here, so it was not run.

## (b) A deletion after a root conflict does not un-refute

```python
from dratify import check_proof, parse_dimacs
from campaign import oracle

F = [[1, 2], [1, -2], [-1, 2], [-1, -2]]
S = [("a", [1]), ("d", [1, 2]), ("d", [1, -2]), ("d", [-1, 2]), ("d", [-1, -2]), ("a", [])]
cnf = "p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n"
proof = "1 0\nd 1 2 0\nd 1 -2 0\nd -1 2 0\nd -1 -2 0\n0\n"
print(check_proof(parse_dimacs(cnf), proof, engine="python").ok)     # True
for flavour in ("length-one", "operational"):
    print(flavour, oracle.replay(F, S, flavour)[0][-1].acceptable)
```

```
True
length-one False
operational True
```

`(1)` makes the multiset refuted at the root, so `_root_conflict` is set. The
deletions then apply, and the multiset left is `(1)`, against which `0` is not RUP
under `length-one`. dratify still accepts, with `deletions=4`.

Sound, because the refutation was legitimate at the moment it was reached: every
earlier step preserved satisfiability, so the input is unsatisfiable. This differs
from root-1, where the conflict itself was false. Flavour `operational` says the same
("every deletion is ignored once top-level propagation conflicts, because the proof
is over"), with the difference that dratify counts those deletions as applied.

The harness's `predict` holds refuted as refuted. 924 such deletions were walked in
the default run, with no mismatch.

## Test

None proposed, since neither is a defect.
