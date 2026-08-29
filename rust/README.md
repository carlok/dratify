# dratify

**Check DRAT/DRUP proofs of unsatisfiability.** No dependencies.

A SAT solver that answers "unsatisfiable" is asking to be trusted. A DRAT proof
is how it stops asking: the solver logs every clause it derives, and a checker
that shares no code with it replays the log and confirms the empty clause
really follows.

```rust
use dratify::{Checker, Lit};

// (a ∨ b) (a ∨ ¬b) (¬a ∨ b) (¬a ∨ ¬b) — unsatisfiable.
// Doubled-index encoding: variable v has literals 2v and 2v+1.
let formula: Vec<Vec<Lit>> = vec![vec![0, 2], vec![0, 3], vec![1, 2], vec![1, 3]];

let mut c = Checker::new(2, &formula, true, true);
assert!(c.check_step(false, &[0]));  // "a" is RUP
assert!(c.check_step(false, &[]));   // and then so is the empty clause
```

## What it checks

- **RUP** (reverse unit propagation), the common case.
- **RAT** (resolution asymmetric tautology), the rule that puts the "A" in
  DRAT: `C` is RAT on pivot `p` when for every clause `D` containing `~p` the
  resolvent `C ∪ (D \ {~p})` is RUP.
- **Deletion**, applied by default. Deletion is monotone-safe for RUP; RAT is
  not monotone, so RAT steps are checked against exactly the clauses present.

Checking is **forward**: every step is verified in order rather than working
backwards from the empty clause, so a corrupted step is caught where it occurs.

## Companion Python package

This crate is the accelerator behind the [`dratify`](https://pypi.org/project/dratify/)
Python package, which ships an *independent* pure-Python implementation of the
same checker. The two are differentially tested against each other on
rejections as well as acceptances — proof checking is the one domain where two
implementations agreeing is itself the evidence.

## Licence

Apache-2.0.
