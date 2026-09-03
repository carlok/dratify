# Changelog

All notable changes to this project are documented here.

The format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

Versions are published to [PyPI](https://pypi.org/project/dratify/) as
`dratify` and to [crates.io](https://crates.io/crates/dratify) as the `dratify`
crate. The two are released together and are meant to be a matching pair; from
0.1.4 a test enforces that their version strings agree.

## [Unreleased]

### Fixed

- The release workflow now runs the test suite on the tagged commit and refuses
  a tag that names a different version than the one being built. Previously
  `release.yml` ran only `build` and `twine check`, and `ci.yml` does not
  trigger on tags — so no test ran on the released ref. Combined with
  `skip-existing`, tagging without bumping the version built the old version,
  PyPI skipped it as already present, and the workflow reported success.

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

[Unreleased]: https://github.com/carlok/dratify/compare/v0.1.3...HEAD
[0.1.3]: https://github.com/carlok/dratify/compare/v0.1.2...v0.1.3
[0.1.2]: https://github.com/carlok/dratify/compare/v0.1.1...v0.1.2
[0.1.1]: https://github.com/carlok/dratify/compare/v0.1.0...v0.1.1
[0.1.0]: https://github.com/carlok/dratify/releases/tag/v0.1.0
