# dratify

**Check a DRAT/DRUP proof of unsatisfiability, inside your Python process.**

A SAT solver that answers "unsatisfiable" is asking to be trusted. A DRAT proof
is how it stops asking: the solver logs every clause it derives, and a checker
that shares no code with it replays the log and confirms the empty clause
really follows.

Emitting those proofs is routine. PySAT exposes them from six solver families
with `with_proof=True` / `get_proof()`. *Checking* them from Python has not
been practical: `drat-trim` is C you compile and shell out to, and the only
checker on PyPI installs on Linux x86-64 under Python ≤ 3.10 alone.

```bash
pip install dratify              # pure Python, zero dependencies
```

A Rust implementation of the same checker is published separately as the
[`dratify` crate](https://crates.io/crates/dratify). Python bindings for it are
not packaged yet; `engine="native"` is wired up and will pick them up when they
are.

## Check a proof from PySAT

```python
from pysat.formula import CNF as PyCNF
from pysat.solvers import Glucose42
from dratify import parse_dimacs, check_proof

cnf = PyCNF(from_file="problem.cnf")
with Glucose42(bootstrap_with=cnf, with_proof=True) as s:
    assert not s.solve()
    proof = s.get_proof()

result = check_proof(parse_dimacs(cnf.to_dimacs()), "\n".join(proof))
print(result.ok)          # True -- the refutation is genuine
```

No subprocess, no compiler, no temporary files.

## Two engines, and that is the point

Proof checking is the one domain where two independent implementations agreeing
*is* the evidence. This ships both:

| | |
|---|---|
| **Pure Python** | zero dependencies, runs anywhere Python does |
| **Rust** (crates.io) | ~18x faster; Python bindings not yet packaged |

Neither is the "real" one. They have been differentially tested against each
other on acceptances *and* on rejections, and they agree.

```python
check_proof(formula, proof, engine="python")   # always available
check_proof(formula, proof, engine="native")   # when bindings are installed
check_proof(formula, proof, engine="auto")     # default: native when present
```

## What it checks

- **RUP** (reverse unit propagation) — the common case.
- **RAT** (resolution asymmetric tautology) — the "A" in DRAT, checked properly:
  pivot on the first literal, resolvent against every clause containing its
  negation, RUP on each.
- **Deletion**, applied by default. Deletion is monotone-safe for RUP; RAT is
  not monotone, so RAT steps are checked against exactly the clauses present.

Checking is **forward**: every step is verified, rather than working backwards
from the empty clause as `drat-trim` does. That makes it slower on large proofs
and means a corrupted step is caught where it occurs.

## Speed

Measured against `drat-trim` (which does backward checking by default):

| proof | steps | pure Python | Rust | drat-trim |
|---|---|---|---|---|
| uuf100-01 | 774 | 0.01s | 0.01s | 0.05s |
| uuf100-010 | 1,103 | 0.05s | 0.00s | 0.06s |
| uuf250-01 | 209,367 | 41.47s | 2.27s | 1.30s |

Rust wins on small proofs — `drat-trim` pays process startup and cannot be
called in-process — and loses 1.75x on the large one, while checking forward.

On 10 proofs from two solvers, `dratify` and `drat-trim` agreed on every case,
including four rejections.

## Honest limitations

- Forward checking only. Backward checking would close the large-proof gap.
- No binary DRAT format yet; text proofs only.
- Not formally verified. It is carefully written, differentially tested against
  a second implementation, and cross-validated against `drat-trim` — which is
  not the same thing as a machine-checked proof of the checker itself. If you
  need that, `cake_lpr` is CakeML-verified and consumes LRAT.

## Related

[`cdclkit`](https://github.com/carlok/cdclkit) is a from-scratch CDCL SAT
solver by the same author that uses this package to check its own refutations.
You do not need it to use `dratify` — checking a proof should never require
installing a solver, which is why these are separate packages.

## Licence

Apache-2.0. See [LICENSE](LICENSE).
