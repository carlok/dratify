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

```python
from dratify import parse_dimacs, check_proof

formula = parse_dimacs(open("problem.cnf").read())
result = check_proof(formula, open("proof.drat").read())

print(result.ok)              # True  -- the refutation is genuine
print(result.reached_empty)   # True  -- the empty clause was derived
```

No subprocess, no compiler, no temporary files.

**Use this if:**

- ✅ You have a DRAT or DRUP proof and need to verify it
- ✅ You are about to act on "no solution exists"
- ✅ You want it in-process, from Python or Rust, on any platform
- ✅ You want two independent implementations that agree

**Use something else if:**

- ❌ You want to *solve* rather than check → [PySAT](https://pypi.org/project/python-sat/), or [cdclkit](https://pypi.org/project/cdclkit/)
- ❌ You only ever look at SAT answers — then you do not need this at all

The same checker is published as a Rust crate, for use from Rust directly:

```bash
cargo add dratify                # https://crates.io/crates/dratify
```

**Want the Rust checker from Python?** This package deliberately ships no
compiled extension of its own -- installing a proof checker should never need a
toolchain. Instead it exposes a seam, `register_native()`, and anything that
already embeds the crate can supply an implementation. Today that is
[`cdclkit-native`](https://pypi.org/project/cdclkit-native/):

```bash
pip install "cdclkit[native]"    # brings wheels that register with dratify
```

After that, `engine="auto"` uses the Rust checker (~18x faster on large proofs)
with no further configuration.

## Why you would want this

Something reported that no solution exists, and you are about to act on it.
Ship the hardware. Declare the configuration impossible. Sign off the safety
argument. Close the bug as "cannot happen".

That report is a bare assertion from a large, aggressively optimised program.
A "yes" answer from a solver checks itself — walk the clauses, confirm each has
a true literal. A "no" answer does not: it is a claim about all 2^n
assignments, and nothing about it is verifiable unless the solver shows its
work.

DRAT is how it shows its work, and this is what reads it. Emitting proofs is
routine; PySAT exposes them from six solver families. Checking them from Python
has not been practical until now, and checking them from Rust meant shelling
out to a C program.

**When not to.** If you want to *solve* rather than check, this is not that —
use [PySAT](https://pypi.org/project/python-sat/) or, from Rust, an established
solver crate. If you never look at UNSAT answers, you do not need this at all.

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
| **Rust** ([crate](https://crates.io/crates/dratify)) | ~18x faster; reachable from Python via `register_native()` |

Neither is the "real" one. They have been differentially tested against each
other on acceptances *and* on rejections, and they agree.

```python
check_proof(formula, proof, engine="python")   # always available
check_proof(formula, proof, engine="native")   # once an implementation is registered
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

## Tests

96 tests, 87% statement coverage, both gated in CI. The negative cases carry
most of the weight: a checker that accepts everything passes any suite that
only feeds it valid proofs, so there are tests for truncated proofs, bogus
refutations of satisfiable formulas, clauses that are neither RUP nor RAT, and
the tautological-resolvent case that makes some surprising clauses vacuously
RAT.

```bash
python3 -m unittest discover -s tests
python3 tests/coverage_report.py      # floor is 80%
```

The coverage tool uses the standard library's `trace` module, so checking this
package needs no more dependencies than using it.

A separate CI job installs a native checker and runs
`tests/test_differential.py`, which compares the two implementations on every
verdict field over a 150-instance random sweep plus hand-written cases. That
job fails if those tests *skip* — the agreement claim above is only worth
making while something is checking it.

## Honest limitations

- Forward checking only. Backward checking would close the large-proof gap.
- No binary DRAT format yet; text proofs only.
- Not formally verified. It is carefully written, differentially tested against
  a second implementation, and cross-validated against `drat-trim` — which is
  not the same thing as a machine-checked proof of the checker itself. If you
  need that, `cake_lpr` is CakeML-verified and consumes LRAT.

## Related

[`cdclkit`](https://pypi.org/project/cdclkit/)
([source](https://github.com/carlok/cdclkit)) is a from-scratch CDCL SAT
solver by the same author that uses this package to check its own refutations.
You do not need it to use `dratify` — checking a proof should never require
installing a solver, which is why these are separate packages.

## Generating code against this?

[AGENTS.md](AGENTS.md) lists the API's sharp edges — the mistakes that have
actually been made, not hypothetical ones. Worth reading before writing a line.

## Licence

Apache-2.0. See [LICENSE](LICENSE).
