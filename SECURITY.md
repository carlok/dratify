# Security policy

## Reporting

Use GitHub's [private vulnerability
reporting](https://github.com/carlok/dratify/security/advisories/new). Please do
not open a public issue for anything in the first category below.

## What counts as a vulnerability here

This package exists to answer one question — *is this proof of unsatisfiability
genuine?* — so the severity ordering is unusual.

**Critical: a proof that should be rejected and is accepted.** If you can
construct a formula and a "proof" that `check_proof` accepts, where the formula
is in fact satisfiable or the proof does not derive the empty clause, that is
the worst bug this package can have. Everything it is used for rests on that
not happening. A satisfying assignment for the formula is the ideal report,
since it settles the question immediately.

**High: a crash or hang on untrusted input.** Proofs and DIMACS files often
arrive from elsewhere. Neither parser should be able to be driven into an
unbounded loop, unbounded memory, or an unhandled exception that a caller
cannot distinguish from a verdict.

**Also wanted: a disagreement between the two checkers.** The Python and Rust
implementations are meant to agree on every input, acceptances and rejections
alike. A case where they differ is a real finding even if neither is obviously
wrong, because the agreement is the evidence.

**Not a vulnerability:** rejecting a valid proof (annoying, and a bug worth an
issue, but it fails closed); running out of time or memory on a genuinely huge
proof; anything requiring the attacker to already control the process.

## Scope

The `dratify` Python package and the `dratify` Rust crate, at the latest
released version.

## What this is not

The checker is carefully written, differentially tested against a second
implementation, and cross-validated against `drat-trim` (`bench/repro.py`
reruns both comparisons from scratch) — but it is **not formally verified**. If you need a checker with a machine-checked correctness
proof, use [cake_lpr](https://github.com/tanyongkiam/cake_lpr), which is
verified in CakeML and consumes LRAT.
