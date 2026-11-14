# Handoff for a follow-up agent

This document is for another LLM (or human) continuing public-repo hygiene or
feature work on `carlok/dratify`. Run commands from the repository root unless
noted.

## Verification checklist

Each row is a claim you can re-check without trusting this file.

| Claim | Command | Expected output (shape) |
|---|---|---|
| Full Python test suite passes | `make test` | Ends with `OK` (no `FAILED` or `ERROR`) |
| Coverage gate passes | `make coverage` | Prints coverage ≥ 80% and exits 0 |
| Community file test passes | `PYTHONPATH=src python3 -m unittest tests.test_community -v` | `test_required_files_exist` and `test_security_md_points_to_private_advisory_reporting` OK |
| CI workflow exists | `test -f .github/workflows/ci.yml && head -1 .github/workflows/ci.yml` | First line `name: ci` |
| Issue templates block blank issues | `grep blank_issues_enabled .github/ISSUE_TEMPLATE/config.yml` | `blank_issues_enabled: false` |
| Security advisory URL in policy | `grep advisories/new SECURITY.md` | Line containing `https://github.com/carlok/dratify/security/advisories/new` |
| No secrets in new docs | `git grep -iE 'api[_-]?key|token|password|BEGIN (RSA\|OPENSSH)' -- '*.md' '.github'` | No matches (or only instructional negatives) |
| Bytecode compiles | `python3 -m compileall -q src tests` | Silent success |
| Optional: native differential job locally | `make native && make test-native` | Only if cargo is available; ends with `OK` |

After edits, paste real `make test` and `make coverage` output into the PR
description — do not paraphrase.

## Prioritized TODO

### P0 — Owner-only (may require repo admin)

**Enable private vulnerability reporting on GitHub**

- **Acceptance:** Repository Settings → Security → Private vulnerability
  reporting is enabled, and
  `https://github.com/carlok/dratify/security/advisories/new` opens the report
  form for reporters with access.
- **Note:** An automated `gh api -X PUT repos/carlok/dratify/private-vulnerability-reporting`
  call may return 403 from a cloud agent token; treat that as manual.

### P1 — Keep community files aligned with tests

**When adding a required community path, update `tests/test_community.py`**

- **Acceptance:** `REQUIRED_PATHS` lists every file the standard expects;
  `make test` includes `tests.test_community` and passes.

### P2 — README numbers

**Regenerate speed table if checker performance changes**

- **Acceptance:** `python bench/repro.py` run on an idle machine; paste output
  into commit/PR; README table matches regenerated numbers (not hand-edited).

### P3 — Rust/Python parity

**Any change to `src/dratify/proof.py` or `rust/src/checker.rs`**

- **Acceptance:** Matching change in the other file; `tests/test_differential.py`
  passes in CI differential job or via `make native && make test-native`.

## Starter prompt

```text
You are working on https://github.com/carlok/dratify (branch main or a PR branch).

Read AGENTS.md for API pitfalls and for rules before each commit: run tests,
try to increase coverage, never commit secrets.

Read docs/TODO-handoff.md and run the verification checklist commands. Fix any
failure with minimal diffs. Keep Apache-2.0. Security reports only via
https://github.com/carlok/dratify/security/advisories/new — never public issues
or email. Contacts: @carlok; CoC enforcement email only in CODE_OF_CONDUCT.md.

When done: make test, make coverage, commit on cursor/*-28a1, push, open or
update one PR (do not merge). Paste real test and coverage terminal output in
the PR body.
```