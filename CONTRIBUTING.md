# Contributing

## Running things

The package lives under `src/`, so it must be on the path to import without
installing. Every `make` target handles that; running `python -m unittest`
directly will not.

```bash
make test        # the full suite, no Rust and no install needed
make coverage    # statement coverage, floor 80%
make lint        # cargo test and clippy on the crate
make gate        # all of the above; run before opening a PR
```

The optional Rust checker is published as part of `cdclkit-native`, not under
this name — installing a proof checker should never require a toolchain:

```bash
make native      # pip install cdclkit-native
make test-native # the suite with it present; fails if it is absent
```

## What a change needs

**A test that fails without it.** For a bug fix, write the test first and watch
it fail; a test that passes before the fix is testing something else.

**Numbers regenerated, not edited.** Every quantitative claim in the README,
`SECURITY.md` and `AGENTS.md` comes from `python bench/repro.py`. If a change
moves one, rerun it and paste the new output — do not adjust the figure by
hand. Numbers nobody can reproduce are how this project got a speed table for
files that were not in the repository.

**Both checkers, if you touch the rules.** `src/dratify/proof.py` and
`rust/src/checker.rs` implement the same thing, and the package is sold on
their agreeing. A change to one needs the same change to the other, and
`tests/test_differential.py` compares them on every verdict field.
`tests/fuzz.py --seed N` will find a divergence faster than reading will.

## What this package is for

It checks DRAT/DRUP proofs. It does not solve — that is
[cdclkit](https://github.com/carlok/cdclkit), which depends on this.

Three properties are load-bearing and a change should not quietly cost one:

- **Zero dependencies**, including for the tests and the coverage tool.
- **Untrusted input is safe.** Parsers must fail as `ValueError`, never crash,
  hang, or allocate on a header's say-so. See `SECURITY.md`.
- **Checking is forward.** Every step is verified where it occurs, which is the
  whole difference from `drat-trim` and the reason to prefer this on a proof
  you do not trust.

## Reporting a vulnerability

See [SECURITY.md](SECURITY.md). Do not open a public issue for one.
