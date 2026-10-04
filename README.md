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
from pathlib import Path
from dratify import parse_dimacs, check_proof

formula = parse_dimacs(Path("problem.cnf").read_text())
result = check_proof(formula, Path("proof.drat").read_text())

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

After that, `engine="auto"` uses the Rust checker (~15x faster; see Speed)
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
from pathlib import Path
from pysat.solvers import Glucose42
from dratify import parse_dimacs, check_proof, to_dimacs

formula = parse_dimacs(Path("problem.cnf").read_text())
clauses = [[to_dimacs(lit) for lit in c] for c in formula.clauses]

with Glucose42(bootstrap_with=clauses, with_proof=True) as s:
    assert not s.solve()
    proof = s.get_proof()

result = check_proof(formula, "\n".join(proof))
print(result.ok)          # True -- the refutation is genuine
```

No subprocess, no compiler, no temporary files.

The file is parsed here rather than by PySAT on purpose. SATLIB's benchmark
files end with a `%` line, and `pysat.formula.CNF(from_file=...)` stops on it
with `ValueError: invalid integer token`; this parser reads them.

**PySAT's CaDiCaL proofs arrive truncated; flush before reading them.** Every
CaDiCaL that PySAT ships (`Cadical103`, `Cadical153`, `Cadical195`, `Cadical300`)
writes its proof through a C `FILE*` that `get_proof()` reads before it has been
flushed, so the end of the proof, usually including the empty clause, is still
in a buffer. On 50 SATLIB `uuf100` instances with python-sat 1.9.dev15 on macOS,
4 to 8 of 50 verify as shipped and 49 to 50 of 50 after a flush. `drat-trim`
agrees. CaDiCaL itself is not at fault: the same version built standalone
writes proofs that verify. Glucose and Lingeling write text proofs, which line
buffering flushes, and verify 50 of 50; on Windows that buffering is compiled
out and every solver is affected ([pysathq/pysat#233](https://github.com/pysathq/pysat/issues/233)).
Until PySAT flushes the file itself:

```python
import ctypes
from pathlib import Path
from pysat.solvers import Cadical195
from dratify import parse_dimacs, check_proof, to_dimacs

formula = parse_dimacs(Path("problem.cnf").read_text())
clauses = [[to_dimacs(lit) for lit in c] for c in formula.clauses]

with Cadical195(bootstrap_with=clauses, with_proof=True) as s:
    assert not s.solve()
    ctypes.CDLL(None).fflush(None)   # PySAT reads the proof before flushing it
    proof = s.get_proof()

result = check_proof(formula, "\n".join(proof))
print(result.ok)          # True -- with the flush; often False without it
```

On Windows the flush is `ctypes.cdll.ucrtbase._flushall()`.

## Two engines, and that is the point

Proof checking is the one domain where two independent implementations agreeing
*is* the evidence. This ships both:

| | |
|---|---|
| **Pure Python** | zero dependencies, runs anywhere Python does |
| **Rust** ([crate](https://crates.io/crates/dratify)) | ~15x faster; reachable from Python via `register_native()` |

Neither is the "real" one. They have been differentially tested against each
other on acceptances *and* on rejections, and they agree.

<!-- readme-test: skip -- a signature listing, not a program -->
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

Every number here is regenerated by `python bench/repro.py`, which builds the
instances, obtains proofs from whichever solvers are on `PATH`, times both
engines, and cross-checks `drat-trim` when it is installed. It writes the whole
result set, with the host and versions attached, to `bench/results.json`.

Measured on Darwin arm64, Python 3.14, proofs from CaDiCaL and kissat:

| proof | steps | pure Python | Rust | Rust vs Python | drat-trim |
|---|---|---|---|---|---|
| uuf100-01 (cadical) | 671 | 0.010s | 0.001s | 11.4x | 0.032s |
| php(8,7) (cadical) | 13,001 | 0.258s | 0.020s | 12.8x | 0.048s |
| php(9,8) (cadical) | 109,179 | 7.00s | 0.44s | 15.9x | 0.38s |
| uuf250-01 (kissat) | 251,243 | 63.1s | 2.92s | 21.6x | 1.37s |
| php(10,9) (cadical) | 856,267 | 148.0s | 8.24s | 18.0x | 4.30s |

Across all 12 measurements the Rust engine's geometric mean is **about 15x**
over pure Python, and the ratio grows with proof size.

**Read the per-instance numbers as a range, not as values.** Two runs of the
script on this machine gave geometric means of 14.7x and 14.9x — stable — while
individual ratios moved between 11x and 22x, one of them by a third. The
absolute times are worse: `uuf250-01` took 43.9s of pure Python in one run and
63.1s in another, because the second shared the laptop with a compile. Run
`repro.py` on an otherwise idle machine, and treat the geometric mean as the
figure and any single row as an illustration.

Against `drat-trim` the pattern is the one forward checking implies: Rust wins
by 20-50x on small proofs, where `drat-trim` pays process startup and cannot be
called in-process at all, and loses about 2x on the largest, where the backward
pass gets to skip work.

### What "skip work" means

`drat-trim` verifies only the lemmas its refutation needs. On `uuf100-01` it
reports *"304 of 403 lemmas in core"* — the other 99 are never examined. So
corrupting one of them is a proof `drat-trim` still calls VERIFIED, and this
checker rejects at the step where the corruption is.

`bench/repro.py` demonstrates exactly that: of 36 perturbed proofs, the two
tools agree on 33, and the 3 they split on are all this direction. **Zero** are
the direction that would matter — this checker accepting something `drat-trim`
rejects — and the script fails the run if one ever appears.

That is the trade the speed table is buying, in both directions.

## Tests

130 tests and 90% statement coverage, of which the enforced floor is 80% — the
percentage is a snapshot, the floor is the gate. Fifteen of the tests need a
native checker and two need `python-sat`, and both kinds skip without them, so
the dependency-free job runs 113 and two separate jobs (below) run the rest,
failing if anything they exist for was skipped. The negative cases carry
most of the weight: a checker that accepts everything passes any suite that
only feeds it valid proofs, so there are tests for truncated proofs, bogus
refutations of satisfiable formulas, clauses that are neither RUP nor RAT, and
the tautological-resolvent case that makes some surprising clauses vacuously
RAT.

```bash
make test        # or: PYTHONPATH=src python3 -m unittest discover -s tests
make coverage    # floor is 80%
make fuzz        # randomised; SEED=n reproduces a run
```

The package lives under `src/`, so it has to be on the path to be imported
without installing — `make` handles that.

The coverage tool uses the standard library's `trace` module, so checking this
package needs no more dependencies than using it.

A separate CI job builds the native checker from the commit under test and
runs `tests/test_differential.py`, which compares the two implementations on
every result field over a 150-instance random sweep plus hand-written cases.
That job fails if those tests *skip* — the agreement claim above is only worth
making while something is checking it.

Agreement between two implementations of one design is weaker evidence than it
sounds: both can share a mistake, and in 0.1.6 both did (a lemma that was unit
at the root when added did not extend the root assignment, so valid proofs were
rejected). So both are also compared against `tests/naive.py`, a deliberately
slow RUP checker that shares no code or data structures with either, on random
proofs aimed at that case. That comparison found nothing until its generator
was aimed; it runs in the suite and in the weekly fuzzer.

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
