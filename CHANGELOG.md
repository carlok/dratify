# Changelog

All notable changes to this project are documented here.

The format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

Versions are published to [PyPI](https://pypi.org/project/dratify/) as
`dratify` and to [crates.io](https://crates.io/crates/dratify) as the `dratify`
crate. The two are released together and are meant to be a matching pair; from
0.1.4 a test enforces that their version strings agree.

## [Unreleased]

## [0.1.4] — 2026-09-03

Nothing in the checker's behaviour changed. What changed is that the claims
made for it are now reproducible, and several were wrong.

### Added

- **`bench/repro.py`** regenerates every performance figure this project
  publishes: it builds the instances, obtains proofs from whichever solvers are
  on `PATH`, times both engines, cross-checks `drat-trim` when installed, and
  records the host, CPU and versions alongside the numbers.
- **`tests/fuzz.py`** and a weekly workflow at four seeds. It asserts that the
  parsers fail as `ValueError` rather than crash or hang on random text, and
  that the two checkers agree on every `CheckResult` field on inputs neither
  author chose. The job fails if no native checker was installed, since half
  the properties would otherwise pass without being tested.
- **`tests/test_packaging.py`**: the Python package, the crate and
  `__version__` must agree. They had agreed only because someone kept them in
  step by hand; `release.yml` compares the tag against the sdist filename and
  would not have noticed the crate drifting.
- `CHANGELOG.md`, `CONTRIBUTING.md`, `docs/RELEASING.md`, and a `Makefile`. The
  working test invocation existed only inside CI, so a fresh clone running the
  obvious command got six import errors.

### Fixed

- **The published speed numbers were not reproducible and were wrong.** The
  README's table came from CNF files absent from the repository; "~18x" was the
  top of a range quoted as typical. Measured: **12x to 18x**, geometric mean
  14.7x over 12 measurements, growing with proof size.
- **"On 10 proofs from two solvers, dratify and drat-trim agreed on every
  case"** had nothing behind it — no script, no CI job, and no occurrence of
  the string `drat-trim` anywhere in the tree. The comparison now runs, and the
  result is more interesting than the claim: of 36 perturbed proofs the two
  agree on 33, and all 3 splits are proofs `drat-trim` reports as VERIFIED and
  this checker rejects. `drat-trim` checks backwards and reports "304 of 403
  lemmas in core" on `uuf100-01`; a corrupted step among the other 99 is never
  examined. Zero splits are the direction that would matter, and `repro.py`
  fails the run if one appears.
- **"96 tests, 87% coverage, both gated in CI"** overstated the second half.
  The gate is a floor of 80%; 87% is a snapshot. Both are now stated as what
  they are.
- The old project's name reached users through raised text: `_native_check`
  interpolated a local named `sable_native` into four error messages. The
  `lits.py` and `cnf.py` module docstrings documented a solver's propagation
  hot loop, and `checker.rs` — whose module doc ships to docs.rs — opened by
  citing a measurement of that solver. None of it is in this package.
- The release workflow now runs the test suite on the tagged commit and refuses
  a tag that names a different version than the one being built. Previously
  `release.yml` ran only `build` and `twine check`, and `ci.yml` does not
  trigger on tags — so no test ran on the released ref. Combined with
  `skip-existing`, tagging without bumping the version built the old version,
  PyPI skipped it as already present, and the workflow reported success.
- `build-system.requires` asked for `setuptools>=68` while the PEP 639 `license`
  expression needs 77. Latent, and only ever visible in someone else's
  environment.
- `[project.urls]` gained `Issues`, `Changelog`, `Security` and
  `Documentation`; it previously had two keys pointing at the same URL.

### Known

- `bench/repro.py` needs a solver on `PATH` (CaDiCaL or kissat) to obtain
  proofs, and `drat-trim` for the cross-check. It reports what it found rather
  than failing, but a run without them measures less than the README quotes.
- CaDiCaL cannot parse SATLIB files as distributed — it stops at the trailing
  `%`, as PySAT does — so `repro.py` re-serialises through this package's own
  parser before handing formulas to solvers, guarded by the header check.

## [0.1.3] — 2026-09-01

### Added

- `tests/test_differential.py`, and a CI job that makes it run. The claim in
  the README, `SECURITY.md` and both Rust documents is that the Python and Rust
  checkers are differentially tested against each other on acceptances *and*
  rejections. Nothing that ran did so: both comparisons sat behind
  `skipUnless(native_available())`, evaluated at import time before anything can
  register a checker. They skipped on every run, so the Rust `Checker` had never
  once been compared against `DRATChecker`. The new suite compares them across a
  150-instance random sweep plus hand-written accept and reject cases, and the
  CI job fails if the tests skip.
- `native_implementation()`, which reports which checker is actually in use —
  `dratify_native` otherwise wins silently over an explicitly registered module.
- `CheckResult` and `parse_proof` are now exported from the package root. The
  first is the return type of `check_proof`, and the package ships `py.typed`,
  so it could not previously be annotated without reaching into `dratify.proof`.

### Fixed

- **Unbounded allocation from one header line.** `p cnf 99999999999 0` sized the
  checker's watch and value arrays and asked for hundreds of gigabytes before a
  clause was read. The same held for an arbitrary proof literal. Both are now
  bounded by what the input could describe, and rejected with the offending line
  and value named. A proof may still introduce fresh variables — that is what
  RAT is for. `SECURITY.md` rated this High and nothing tested it.
- **`ProofWriter.add` corrupted an empty clause written from a generator.** The
  parameter is annotated `Iterable[int]` but the generator was consumed by the
  join and then tested for emptiness while exhausted — always truthy — so the
  empty clause was written as `" 0\n"` with a leading space.
- **`register_native` trusted whatever it was handed.** It checked only for a
  `check_proof` attribute, then unpacked a fixed 10-tuple, so a version skew
  surfaced as `not enough values to unpack` raised from inside a checker: an
  exception a caller cannot distinguish from a verdict. The result shape is now
  validated, and a module reporting a valid refutation that never derived the
  empty clause is refused outright.
- Corrected the install instructions. The module docstring told users to run
  `pip install dratify[native]`; no such extra exists, so pip warned and
  installed nothing. The working route is `pip install "cdclkit[native]"` plus
  `register_native()`, which is what the error message now says too.

## [0.1.2] — 2026-08-29

### Changed

- README corrections reach the package pages: both READMEs point at the
  published packages, and a stale performance claim was removed.
- The native checker may be supplied by another package. `cdclkit-native`
  embeds this crate and registers itself, so installing a proof checker never
  requires a Rust toolchain.

### Added

- `AGENTS.md`, and a README section saying who needs this package and when.
- The checker gained its own tests — 12 to 71 — and a statement-coverage gate
  using the standard library's `trace` module, so the zero-dependency promise
  holds for the checks as well as the package.
- A security policy, and every GitHub Action pinned to a commit SHA with
  Dependabot to keep the pins fresh.

## [0.1.1] — 2026-08-29

### Fixed

- `Cargo.lock` kept in step with the version, and the PyPI publish step made
  idempotent so re-running a release does not fail on an already-uploaded file.
- The crates.io publish step is idempotent: it checks whether the version is
  already on the index before attempting to publish.

## [0.1.0] — 2026-08-29

Initial release: a DRAT/DRUP proof checker that installs anywhere.

- Forward checking of RUP and RAT steps against a DIMACS CNF, with deletion
  applied by default and unit deletions ignored deliberately.
- A DIMACS parser that accepts the SATLIB files in the wild, including the
  trailing `%` that some standard tools reject.
- Zero dependencies, pure Python, plus an optional Rust crate implementing the
  same rules.
- Tokenless publishing to both registries via Trusted Publishing.

[Unreleased]: https://github.com/carlok/dratify/compare/v0.1.4...HEAD
[0.1.4]: https://github.com/carlok/dratify/compare/v0.1.3...v0.1.4
[0.1.3]: https://github.com/carlok/dratify/compare/v0.1.2...v0.1.3
[0.1.2]: https://github.com/carlok/dratify/compare/v0.1.1...v0.1.2
[0.1.1]: https://github.com/carlok/dratify/compare/v0.1.0...v0.1.1
[0.1.0]: https://github.com/carlok/dratify/releases/tag/v0.1.0
