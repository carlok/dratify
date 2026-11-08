# Soundness campaign: dratify

Formulas of at most 16 variables, an oracle that shares no code with this repository
(`campaign/oracle.py`, reviewed by a second agent against the definitions in Wetzler, Heule and
Hunt 2014 and Rebola-Pardo and Biere 2018), and one seeded generator per corner.

**Three Critical defects were found and fixed on this branch, none yet released.** The deleted
reason clause is the serious one: every release from 0.1.0 to 0.1.10 accepts the refutation below
of a satisfiable formula, on default flags, through proof text. Each version was installed and run
on it: the wheels from PyPI on the Python engine, the crates from crates.io directly, and
`cdclkit-native` 0.1.1 to 0.1.7, which embed the crate.

```
p cnf 2 2        d -1 2 0
1 0              -2 0
-1 2 0           0
```

Since Critical findings appeared, no README sentence is proposed.

## Corners

Numbers are from the final run after the fixes, recorded in `campaign/results/`. Every generator's
self-test passes against deliberately wrong stubs, and each now flags the old deletion rule. No
generator reports a required category at zero. No corner has an unexplained mismatch.

| Corner | Instances | Steps | Seeds | Open mismatches at the end |
|---|---:|---:|---|---|
| RAT | 10,000 | 132,742 | 20261108 | none |
| Deletion | 40,000 | 1,529,980 | 1 | none |
| Root level | 72,240 | 363,216 | 20261108 | none |
| Literals | 30,000 | 107,927 | 1, 2, 3 | literals-7 ×29 (Note) |
| `ok` against `reached_empty` | 2,821 | 79,154 | 20261108 | none |
| Parsing | 20,000 | 87,093 | 20261108 | parsing-5 ×24,420 (Note) |
| API shapes | 6,001 | 66,903 | 20261108 | api-6 ×1,201 (Note) |
| Engines | 80,000 | 1,010,093 | 20261108 | none |
| drat-trim and `rate` | 1,593 | 9,378 | 1 | see "Against `rate` and drat-trim" |
| **Total** | **262,655** | **3,386,486** | | |

The api, literals and parsing generators exit 1 while those Notes stay open, as designed.

Full suite at the end, with the native engine built from this checkout: `make test` 273 tests, OK,
2 skipped (python-sat only); without native, 273 tests with 57 skipped; `cargo test` 19 + 1;
clippy clean; `tests/fuzz.py --seed 9 --rounds 2000` no failures; cdclkit's suite passes on this
checkout. Proofs from cadical and kissat on uuf100, uuf250 and php 4, 6, 7 and 8 verify on both
engines.

An independent sweep written after the fixes, sharing no code with the generators or tests: 40,000
random instances, seed 90210, 0 false refutations, 0 differences between engines on any field. A
similar sweep on the old code found 167 in 60,000.

## Findings

Duplicates are collapsed: nine corners found the deleted reason clause independently.

### Critical

Each was checked by a second agent, with the oracle and by hand: `campaign/findings/VERIFICATION.md`.

| Defect | Findings | Fix | Test |
|---|---|---|---|
| A deleted reason clause leaves its literal assigned, so a RAT step refutes a satisfiable formula | root-1, deletion-1, deletion-2, api-2, engines-1, ok_empty-1, literals-1, parsing-9, rat-1, drat_trim-1 | dee3b51 | `tests/test_deleted_reasons.py` |
| A comment ends at any Unicode line break, so a hidden clause is read | parsing-1, literals-4 | 9a6eda3 | `tests/test_text_forms.py` |
| `DRATChecker` used directly skips validation: the 0.1.7 hole by another door | api-1, literals-5 | 0647efb, dadab66 | `tests/test_direct_checker.py` |

**The deleted reason clause.** Deletion shrank the clause store and never the root assignment. RAT
candidates come from the live clauses, so the clause that implied a literal was gone while the
literal stayed true. Now a deletion is ignored when the clause, as a set, has exactly one literal
true and the others false at the root. Every reason has that shape, so every root literal stays
supported, and ignoring a deletion is always sound. This is drat-trim's operational reading,
approximated by the root-unit test: a clause that merely looks like a reason is kept too. With
either `check_rat=False` or `apply_deletions=False` the old code was not exposed.

**Comments.** This is Critical only if "the formula" means the file, the reading the second agent
accepted: minisat, cadical and kissat all answer SAT on `p cnf 1 1\n1 0\nc\x0c-1 0\n`, and dratify
certified it unsatisfiable. If it means what `parse_dimacs` returned, this is a Bug. Reaching it
requires control of the formula file, not only the proof. A line now ends at `\n`, with one
trailing `\r` removed. CR-only files raise.

**`DRATChecker`.** Low reachability: a caller passing signed integers to an exported class that
the README does not describe. Rated Critical on 0.1.7's own precedent for the same input.

### Bug

| Defect | Findings | Fix | Test |
|---|---|---|---|
| A second header replaced the first and defeated `strict=True` | parsing-4 | c7653a8 | `test_text_forms` |
| Header tokens past the fourth dropped, `pq cnf` counted as a header | parsing-2 | bd9e2ca | `test_text_forms` |
| `1_0`, Unicode digits and NBSP accepted as DIMACS | parsing-3, literals-6 | bdac29e | `test_text_forms` |
| `failed_clause` differed between engines on a repeated literal | root-2, deletion-3, api-3, engines-2, ok_empty-2, literals-2, parsing-10, rat-2 | 51bbff6 | `test_repeated_literals`, `test_differential` |
| The variable bound depended on shape and text length, so a comment could flip the outcome | api-4, engines-3, literals-3, rat-4, parsing-8 | cbb66d6 | `test_literal_bound` |
| `check` on a used checker reported an empty clause nobody derived | api-5 | df9dc99 | `test_direct_checker` |
| Set literals: Python TypeError, native a verdict | api-7 | b5b49e4 | `test_direct_checker` |
| A refutation is final, which the docs contradicted (moved up from Note by the second agent) | ok_empty-3, drat_trim-5, root-3 | 69db922, documented | `test_refutation_is_final` |

### Note, open

- api-6: `ProofWriter` and `MemoryProof.to_text` mistranslate a negative internal literal. No
  wrong verdict: a checker judges what it is handed. The fix is more than one line on a hot path.
- literals-7: `nvars` depends on literal order in a dropped tautology.
- parsing-5: `header_mismatch` has gaps. parsing-6: `%` ends the formula, as documented.
- parsing-7: `010` reads as 10 here and as 8 under drat-trim's `fscanf("%i")`.
- ok_empty-4: where a refutation ends, three behaviours the docs do not state.
- deletion-4 and rat-3: `report()`'s wording on `ignored_deletions`, now fixed in dee3b51.
- drat_trim-2, 3, 4, 6, 7, 8, 9, 10 and 11: see "Against `rate` and drat-trim".

## Behaviour that changes

- A proof that relied on deleting a reason clause is now rejected or checked against more clauses.
  cadical and kissat proofs are unaffected in everything run here.
- A file with a second header, extra header tokens, a mid-line `\r`, `+1`, `1_0` or non-ASCII
  digits now raises. minisat reads `+1`; the choice here is to reject rather than guess.
- A proof variable more than 2^20 past the formula, with fewer occurrences than that, now raises.
  Only the old text-length bound let those through.

## Against `rate` and drat-trim

Two outside checkers read the same 1,593 proofs: `rate` 0.3.0, and drat-trim at commit
`2e3b2dc0ecf938addbd779d42877b6ed69d9a985`, from a read-only clone of
github.com/marijnheule/drat-trim, built with `cc -std=c99 -O2`. **Nothing from either is Critical
or a Bug.** Every disagreement below is a Note, and for drat-trim the generator shows the cause on
each one: it changes the proof by the named cause, and both checkers must then give the expected
answer. One it cannot show fails the run. Seeds 2 and 3 have none either.

`rate`. In the forward modes it rejected no proof a solver wrote. Only the deletion-skipping modes
compare like with like.

| `rate` mode | Disagree | `rate` accepts, dratify rejects | dratify accepts, `rate` rejects | Why |
|---|---:|---:|---:|---|
| `-f -p -d` | 28 | 28 | 0 | drat_trim-3: no written empty clause; dratify is stricter |
| `-p -d` | 32 | 32 | 0 | drat_trim-3, drat_trim-4 |
| `-f -p` | 61 | 28 | 33 | adds drat_trim-2: `rate` honours a unit deletion |
| `-p` | 65 | 32 | 33 | the same, and drat_trim-4: backward checking skips an unused lemma |

drat-trim. A proof can have two causes, so the last column can add up to more than the disagreements.

| drat-trim mode | Disagree | it accepts, dratify rejects | dratify accepts, it rejects | Why |
|---|---:|---:|---:|---|
| default, `-I` | 32 | 32 | 0 | drat_trim-3 ×28, -4 ×1, -6 ×3, -7 ×1 |
| forward, `-f -I` | 31 | 31 | 0 | drat_trim-3 ×28, -6 ×3 |

- drat_trim-3: it stops at the first propagation conflict; dratify asks for the written clause.
- drat_trim-4 and -7: backward, it skips an unused lemma, and a RAT candidate not yet used.
- drat_trim-6: it falls back to the other literals as pivot. dratify documents the first.
- drat_trim-8: its parser reads `d 0` and swallows the next token. No seed reached this; the
  self-test pins it.
- drat_trim-10: it reads past its clause database at a final empty clause with no conflict behind
  it, and can segfault: 2 proofs in the default mode in this run, varying between runs. The generator
  confirms the cause each time and judges the answer it gets without the crash, `s NOT VERIFIED`,
  which is dratify's too.

`s DERIVATION`, printed 216 times in `-f`, says every lemma passed and nothing was refuted. It counts as
agreeing with dratify's `ok=False` and no failed step. Text detection does not misfire: its binary
test looks only for characters a text proof does not have, and running without `-I` gave the same
verdict on all 1,593. The exit code is not read, because `s VERIFIED` can come with exit 1 and
`s TIMEOUT` with exit 0. `-t 20` never fired.

No mode honours a unit deletion and also checks a refutation (drat_trim-9). `-S` honours them, but
it checks deletions and skips additions, and its `s VERIFIED` appeared on 190 satisfiable and 79
unsatisfiable formulas, so it is counted and not compared. `-W` stops with exit 80 and no `s` line at
a warning, and at an ignored reason.

The named cases, in every mode:

| Proof | default | `-f` | `-S` | `-W` | dratify |
|---|---|---|---|---|---|
| `(1) (-1 2)`; `d -1 2`, `-2`, `0` | NOT VERIFIED | NOT VERIFIED | NOT VERIFIED | exit 80 | `ok=False`, step 2 |
| `(1) (-1 2) (-2 3)`; `d -1 2`, `2` | NOT VERIFIED | DERIVATION | NOT VERIFIED | exit 80 | `ok=False`, no failed step |

`rate` rejects the first in all four modes.

**The deletion rule.** drat-trim tests identity: is this clause the recorded reason for its first
literal (drat-trim.c line 807)? dratify tests shape: one literal true and the others false. So
dratify keeps more. On `(1) (2) (-1 2)`, `d -1 2` is applied by drat-trim, whose reason for 2 is `(2)`,
and ignored by dratify. The generator lists what drat-trim keeps from its `-v` output, and on each
proof where the two differ it changes the reading on either side and asks again.

| Seed 1 | corpus | look-alikes (`gen_lookalike`) |
|---|---:|---:|
| Proofs where the rules differ | 27 | 677 |
| Clauses only dratify keeps | 57 | 701 |
| Clauses only drat-trim keeps | 0 | 0 |
| Verdict stays: drat-trim without those deletions, default and `-f` | 27 | 677 |
| Verdict stays: dratify honouring those deletions | 27 | 677 |
| dratify accepts | 0 | 197 |

So the rules differ and no verdict moved, on seeds 1, 2 and 3. drat_trim-11 gives the argument that
none can: a clause with every variable set at a root that never shrinks cannot propagate, and as a
RAT candidate it only repeats what the real reason already decides. This is an argument and a test,
not a proof checked by machine. The documents' "approximated" is accurate. One README sentence is
not: "A proof that relies on such a clause being gone can be rejected" holds for a real reason and
not for a look-alike. It is reported there and not changed.

**Real solvers.** In the run, 108 proofs from CaDiCaL and 85 from kissat: drat-trim rejected none of the
unsatisfiable ones in either mode. Past the oracle's limit, 28 more refutations, 29,304 steps, on php up to 7
pigeons and random 3-SAT up to 120 variables: both engines of dratify and both modes of drat-trim
accept all of them. Those two passes are outside the 1,593 and are counted in the results under
`lookalike_` and `large_solver_`.

## What was not checked

- `rate` with no `-p`, and drat-trim's `-p`, `-u` and `-O`, its binary reading, and any commit but
  2e3b2dc.
- Binary DRAT, which dratify does not read.
- Formulas past 16 variables in the campaign, and long proofs. The real-solver check above is the
  only evidence at realistic size.
- The Rust crate's API other than through `cdclkit_native` and `check_proof`, beyond `cargo test`.
- Python 3.10 at runtime: it is not installed here. All files parse under the 3.10 grammar.
- `read_text()` on a proof still rewrites a stray `\r` before dratify sees it. Hidden steps are
  still checked, so this buys nothing.
- `check_step` on an input already refuted counts steps, where `check` reads none. Python `check`
  returns its shared result object.
- Two tests in `test_direct_checker.py` allocate without limit on the unfixed code. They were not
  seen failing first, and a regression there would hang rather than fail.

Each corner's full list is under `not_checked` in `campaign/results/<corner>.json`.

## Before this reaches users

The fixes need a release of dratify. cdclkit-native embeds the crate, so it stays exposed until it
is rebuilt against that release.
