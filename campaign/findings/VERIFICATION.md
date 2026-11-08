# Verification of the campaign's Critical candidates

Independent re-check, written by someone who wrote none of the findings. Every output below
comes from the current tree: branch `campaign/soundness`, commit `18cb747`, dratify 0.1.10.
`src/`, `rust/` and `tests/` were not changed.

## Verdicts

| # | Findings | Verdict | One-line reason |
|---|---|---|---|
| 1 | root-1, deletion-1, api-2, engines-1, ok_empty-1, literals-1, parsing-9, rat-1, drat_trim-1 | **Critical, one defect** | `ok=True` on a satisfiable formula, both engines, default flags, proof text |
| 1 | deletion-2 | **Not a separate Critical**: same defect | Its step can break the literal wording, but it cannot produce a wrong verdict without the RAT step above |
| 2 | parsing-1, literals-4 | **Critical, as a parser defect** | `ok=True` on a file all three installed solvers call SAT, also under `strict=True`. The checker is not at fault |
| 3 | api-1, literals-5 part (b) | **Critical, low reachability** | Exactly the 0.1.7 input and answer, through an exported class |
| 3 | literals-5 parts (a), (c), (d) | **Bug** | No well-formed formula is involved, or it fails closed. The engines disagree |

Scan of the other findings: no new Critical. One rating should change, from Note to Bug: see
"Scan".

Corrections to the findings and to the brief are listed under each candidate.

## Candidate 1: deleted reason clause

### Reproduction

Formula `p cnf 2 2 / 1 0 / -1 2 0`, proof `d -1 2 0 / -2 0 / 0`.

```
python {'ok': True, 'empty': True, 'steps': 3, 'rup': 1, 'rat': 1, 'dels': 1, 'ign': 0, 'res': 0, 'fail': -1, 'reason': 'empty clause derived and every step verified'}
native {'ok': True, 'empty': True, 'steps': 3, 'rup': 1, 'rat': 1, 'dels': 1, 'ign': 0, 'res': 0, 'fail': -1, 'reason': 'empty clause derived and every step verified'}
```

The Rust source in `rust/` gives the same result when run directly, through a scratch crate
with a path dependency. This matters because `cdclkit_native` is a separate build:

```
minimal check_rat=true apply_deletions=true: ok=true empty=true steps=3 rup=1 rat=1 dels=1 ign=0 fail=-1
```

| check_rat | apply_deletions | python | native |
|---|---|---|---|
| True | True | `ok=True` | `ok=True` |
| True | False | `ok=False`, fail 2 | `ok=False`, fail 2 |
| False | True | `ok=False`, fail 2 | `ok=False`, fail 2 |
| False | False | `ok=False`, fail 2 | `ok=False`, fail 2 |

Removing a line: no deletion fails at 1, no `-2` fails at 2, no `0` gives `ok=False` with no
failed step, no clause `(1)` or no clause `(-1 2)` fails at 3.

### Oracle

`oracle.satisfiable` says True.

```
specified   d applied; (-2) rup F rat T implied F psat T; () rup F implied F psat F; final [[1], [-2]]
operational d ignored; (-2) rup F rat F implied F psat F;                     final [[1], [-1, 2]]
length-one  d applied; (-2) rup F rat T implied F psat T; () rup F implied F psat F; final [[1], [-2]]
```

No flavour accepts the proof. `rate` 0.3.0 (the binary the campaign built, re-run here) says
`s NOT VERIFIED` in `-f -p`, `-f -p -d`, `-p` and `-p -d`. `drat-trim` is not installed.

### By hand

- 1 true, 2 true satisfies `(1)` and `(¬1 ∨ 2)`.
- After the deletion the clause set is `(1)`. After adding `(¬2)` it is `(1)(¬2)`, satisfied by
  1 true, 2 false. Propagation there sets those two values and no clause is ever false. So
  the clause set is satisfiable at every point of the proof, and the empty clause cannot be
  RUP at any of them.
- What dratify does instead:
  1. Setup puts `1` and then `2` on the root trail, with `(¬1 ∨ 2)` as the reason for `2`.
  2. `d -1 2` removes that clause from the watches and occurrence lists. `2` stays true.
  3. `-2`: negating it assigns `2`, already true, so no conflict: not RUP. RAT on `¬2` looks
     for clauses containing `2`, finds none and passes vacuously.
  4. `_add_lemma` sees `¬2` false at the root, finds no free literal and sets `_root_conflict`.
  5. `0`: `_is_rup` returns True at its first line.

### Root cause

The clause store shrinks on deletion. The root assignment never does.

| | `src/dratify/proof.py` | `rust/src/checker.rs` |
|---|---|---|
| Only clauses of at most one literal are spared | 619 | 444 |
| Deletion erases the clause and leaves `val` and `trail` alone | 622-626, 524-537 | 451-457, 322-348 |
| RAT candidates come from the live clauses only | 578-581 | 397-401 |
| A lemma false under the stale root sets the conflict | 675-677 | 518 |
| A set conflict passes every later step | 550-551 | 362-364 |

The justification at `proof.py:41-50` and `checker.rs:445-447` is sound for a deletion that is
ignored entirely, and it says a propagated unit "cannot be cleanly retracted". Any reason clause
has that property. The code tests length, so it applies the deletion to RAT and ignores it for
propagation.

### One cause or several

One cause. I tried to separate them and could not.

- ok_empty-1, literals-1 and parsing-9 are the same case with the variables renamed: a unit,
  then a binary reason, deleted, then the negation of the implied literal. The other six use
  the identical formula and proof. All give the same fields, shown here for ok_empty-1:
  `ok True, steps 3, rup 1, rat 1, dels 1`.
- rat-1's variants (`two lemmas`, `longer chain`) reproduce, and take the same path.
- A scratch subclass of `DRATChecker` that ignores a deletion when the clause has one true
  literal and the rest false at the root rejects all of them at the `-2`-style step.

My own sweep, using none of the campaign generators: every set of up to 3 clauses over 2
variables with every proof of up to 3 steps ending in `0`, plus 60,000 random instances (seed
777, up to 5 variables, up to 7 clauses, up to 7 steps).

| Question | Exhaustive (28,244) | Random (60,000) |
|---|---|---|
| `ok=True` on a satisfiable formula | 36 | 167 |
| ...with no deletion in the proof | 0 | 0 |
| ...with no deletion of a clause unit at the root | 0 | 0 |
| ...still accepted under the scratch fix | 0 | 0 |
| ...accepted with `check_rat=False` | 0 | 0 |
| ...accepted with `apply_deletions=False` | 0 | 0 |
| Engines differ on verdict, counters or reason | 0 | 0 |
| Scratch fix differs from `operational` on the first bad step | 0 | 0 |

Limits: tiny formulas, and the scratch fix is Python only, so it says nothing about a Rust fix.
My first run showed 11 instances in the "no reason deletion" row. That was a bug in my tracker,
which removed unit clauses where dratify keeps them. They went to 0 once it followed
dratify's rule, and I checked no other way.

Each of the two flags alone closes this for a reason, not by luck:

- With `apply_deletions=False` the live clauses still support every root literal.
- With `check_rat=False`, by induction, every root literal and lemma is entailed by the input
  plus earlier lemmas. So `ok=True` implies the input is unsatisfiable.

### deletion-2: not separately Critical

The finding reproduces (`rup 1, dels 1, fail -1`, both engines, and `rust/` directly).
`length-one` says `rup False rat False implied False preserves_sat True`.

**Correction.** The finding's reason for Bug is that the step "does preserve satisfiability".
That holds for its example and not in general:

```
F = (1) (-1 2) (-2 3 4) (-2 3 -4) (-2 -3 4) (-2 -3 -4), proof: d -1 2 0 / 2 0
F sat False   F minus the reason sat True
python/native: rup 1, dels 1, fail -1 (also with check_rat=False)
length-one: rup False rat False implied False preserves_sat False
```

So against the clauses present the step is accepted as RUP, is not implied, and turns a
satisfiable clause set into an unsatisfiable one. The rubric's wording, "a RUP step must be
implied", is met literally. That is still not a second Critical:

- It is the same lines and the same cause, and either fix ends it.
- Every such step is entailed by the input, so it cannot refute a satisfiable input alone. The
  false refutation needs the RAT step (the `check_rat=False` row above).

Keep it as a symptom under the one Critical, with its own regression test, because its expected
counters depend on which fix is chosen. Standalone, it would be a Bug: `deletions=1` reports the
clause gone, and `proof.py:473` says each addition is verified "against the clauses present".

Not re-run: the campaign's counts (425, 1,539, 6,275 and so on) and the solver-proof measurements
in rat-1 and drat_trim-1.

## Candidate 2: comment parsing

### Reproduction

`\x0c` is one byte. Solver exit codes: 10 SAT, 20 UNSAT, other is a parse error. Versions: cadical
3.0.1, kissat 4.0.4, minisat from Homebrew.

| | File | `parse_dimacs` | `strict=True` | `ok`, both engines | minisat, cadical, kissat |
|---|---|---|---|---|---|
| A | `p cnf 1 1\nc\x0cp cnf 1 2\n1 0\nc\x0c-1 0\n` | `[[1],[-1]]`, mismatch None | same | True | 10, 10, 10 |
| B | `p cnf 1 1\n1 0\nc\x0c-1 0\n` | `[[1],[-1]]`, mismatch (1, 2) | raises | True | 10, 10, 10 |
| C | `p cnf 1 2\n1 0\nc x\x0c-1 0\n` | `[[1],[-1]]`, mismatch None | same | True | 10, 1, 1 |
| D | `c\x0c-1 0\np cnf 1 1\n1 0\n` | `[[-1],[1]]`, mismatch (1, 2) | raises | True | 10, 10, 10 |
| E | `p cnf 1 1\n1 0\nc x -1 0\n` (control) | `[[1]]` | same | False | 10, 10, 10 |
| F | `c x\r\np cnf 1 1\r\n1 0\r\n` (control) | `[[1]]` | same | False | 10, 10, 10 |

All nine separators (`\r \x0b \x0c \x1c \x1d \x1e \x85    `) give `[[1],[-1]]` and
`ok=True` in form B, with 10, 10, 10 from the solvers. A also goes through `parse_dimacs_file` and
`Path.read_text()`.

### Oracle and by hand

`oracle.satisfiable([[1]])` is True and `oracle.satisfiable([[1],[-1]])` is False. The oracle has
no parser, so it only shows the reading decides the answer. Read a byte at a time, a comment runs
to the next `\n`. So file A is `p cnf 1 1`, a comment, `1 0`, a comment: the single clause `(1)`,
satisfied by 1 true. dratify reads the comment `c`, a second header, `1 0`, the comment `c` and
the clause `-1 0`. `(1)(¬1)` is then correctly refuted by propagation, and the proof is never
looked at.

### Root cause

`text.splitlines()` at `src/dratify/cnf.py:277` and `src/dratify/proof.py:235`. It ends a line at
every Unicode line boundary, then `line[0] == "c"` (`cnf.py:282`) treats the remainder as new. The
overwriting header at `cnf.py:292-293` (parsing-4) is what gets A past `strict=True`. Text is
parsed once in Python, so both engines inherit it. No Rust code is involved.

### Critical or Bug

**The case for Bug.** `check_proof` is right about the `CNF` it receives. No RUP or RAT rule is
wrong. An attacker must control the formula file, not only the proof. No accident reaches it in
practice: text after the break must be clause-shaped. `c page 1\x0cpage 2` raises
`malformed header`, and `c x\x0cc y` stays a comment.

**The case for Critical, which I accept.**

- What the file means: every solver tested ends a comment at `\n` only, and that fits the DIMACS
  convention of comment lines in an ASCII file (recalled from memory, not re-read for this check).
  File D keeps its only comment before the header, the most conservative layout. By that meaning the
  formula is satisfiable and dratify says `ok=True`. That meets the rubric's first line.
- What dratify documents: nothing says a form feed ends a comment. `proof.py:222-223` and CHANGELOG
  say only that lines whose first character is `c` are comments. No documentation mentions line
  endings for these separators.
- dratify's own position: `cnf.py:116-122` treats "the formula in memory is not the formula in the
  file" as the serious failure, after `dubois100`. README's first example is
  `parse_dimacs(Path(...).read_text())` then `check_proof`. `SECURITY.md` says DIMACS files
  "often arrive from elsewhere", and that a satisfying assignment settles a report. Here `1` is one.
- The harm is the one the package exists to prevent. Someone reviews a formula, or a solver answers
  SAT on it, and dratify certifies it unsatisfiable.

Report it separately from Candidate 1, tagged as a parser differential: the fix and the threat
differ. The verdict depends on reading "formula" as the file. If the maintainer defines it as what
`parse_dimacs` returned, this becomes a Bug. That is a decision to state, not a fact I can test.

### Corrections

- **"Even with `strict=True`" needs narrowing.** It holds for A (three solvers say SAT, through the
  hidden header) and C (cadical and kissat refuse that file). In B and D strict raises and lenient
  sets `header_mismatch`, although `check_proof` still accepts because it does not read that field.
- **literals-4's minimal case is C**, where two of the three solvers report a parse error. Its
  headline holds for its one-clause variant (B), where strict raises. Only A combines all of it.
- **`\x85` only arrives as UTF-8 `C2 85`.** A raw `0x85` byte through `parse_dimacs_file` becomes
  U+FFFD and parses correctly, to `[[1]]`.
- **`\r` is the weakest member.** Stray in an LF file, the solvers still say SAT. CR-only files have
  no shared reading: cadical and kissat refuse `p cnf 1 1\r1 0\r` and minisat accepts it. Universal
  newlines also rewrite `\r` before any parser fix can act on the `read_text()` path. The maintainer
  could fairly carve `\r` out as a Bug.
- **The proof side is a Bug.** `c note\x0cd 1 2 0` parses to a deletion. A hidden addition is still
  checked: `c x\x0c1 0` on `(1 2)` fails at step 2 on both engines. So a hidden proof line obtains
  nothing that writing it openly would not.
- Not checked: parsing-1's claim about cdclkit's CLI.

## Candidate 3: direct use of `DRATChecker`

### Reproduction

```
oracle (1) sat: True
DRATChecker.check [(a,-1),(a,())] -> ok True, reached_empty True, steps 2, rup 1, rat 1, res 1, 'empty clause derived and every step verified'
check_step: True True; result.ok False, reached_empty True
check_proof python same list -> ValueError proof step 1: -1 is not an internal literal...
check_proof native same list -> ValueError (same)
check_proof MemoryProof      -> ValueError (same)
DRATChecker with parse_proof("-1 0\n0\n") -> ok False, the safe route

oracle (1 2)(-2 3) sat: True
0.1.7's exact input, DRATChecker -> ok True, 'empty clause derived and every step verified'
0.1.7's exact input, check_proof -> ValueError

CNF.clauses = [(-1,),(-2,),(3,)], check_proof "0\n", python -> ok True, 'input formula is refuted by unit propagation alone'
same, native -> OverflowError out of range integral type conversion attempted
CNF.add([-1]) -> ValueError
```

### By hand

Formula `(1)`, satisfied by 1 true. Read as DIMACS, the step `(¬1)` is neither RUP nor RAT: the
resolvent with `(1)` is `(¬1)` again, and assigning 1 does not conflict. What the code does with the
integer `-1`, confirmed by inspection of `val` and `_occ`:

1. `val[-1]` is `val[1]`, the false literal, so `(-1)` is not satisfied.
2. `-1 ^ 1` is `-2`, and `val[-2]` is `val[0]`, true, so assigning it succeeds. No conflict: not RUP.
3. In `_is_rat`, `occ[-2]` is `occ[0]`, which holds `(1)`. The resolvent is `[-1, 0]`, literal `0` is
   true at the root, so the resolvent counts as RUP and the step as RAT.
4. `_add_lemma` finds `val[-1]` false and no free literal, and sets `_root_conflict`.

### Root cause

`_validate_steps` is called from `check_proof` only (`proof.py:782`). `DRATChecker.check` (684) and
`check_step` (601) index `val` and `_occ` with the raw value. `__init__` (496-500) inserts
`formula.clauses` unchecked, and `_validate_steps` never looks at them.

### Severity

**Public entry point?** Public, though not documented in prose. It is in `dratify.__all__`, has a
class docstring, is re-exported at `cdclkit/__init__.py:52`, and `tests/test_rat.py` drives `check_step`
directly. README and AGENTS.md do not mention it. Their negative-literal warning describes
`check_proof`.

**`DRATChecker.check` and `check_step`: Critical, low reachability.** I tried the off-contract defence:
internal literals are documented as non-negative, so this is misuse. But 0.1.7 rated this same input a
security fix against the same defence, on a formula that is well-formed and satisfiable. CHANGELOG 0.1.7
also says "Every step is now validated before either checker runs", which is false on this route.
Reachability is as narrow as it was then: a caller passing signed integers. Text and `parse_proof` are
safe.

**`CNF.clauses`: Bug.** A negative internal literal has no meaning, so "satisfiable" holds only under a
DIMACS reading the object does not have, and it takes writing past the validating `CNF.add`. The engines
disagree, which is a Bug by definition. The fix belongs in the same change, because AGENTS.md calls this
mistake the most common one.

**literals-5 (c) and (d): Bug.** Case (c), repeats on `CNF.clauses`, fails closed. Case (d), `nvars` past
u32, is an engine disagreement.

### Corrections

- The brief's "native raises OverflowError" applies only to `CNF.clauses` and to (d). `DRATChecker` has no
  native path, step lists through `check_proof` raise `ValueError` on both engines, and Rust's `Lit` is
  `u32`.
- `check_step` alone never gives `ok=True`. It returns True for both steps and sets `reached_empty`, and
  `result.ok` stays False. Only `check` reports `ok=True`.

## Scan of the other findings

I read ok_empty-3, drat_trim-5, root-3, api-5, parsing-2, -3, -4, -6, literals-6, rat-3, drat_trim-2 and
deletion-4. For the rest I checked the title, the proposed severity, and a keyword search for acceptance
or satisfiability claims.

**No other finding reaches `ok=True` on a satisfiable formula.**

**ok_empty-3, drat_trim-5, root-3(b): the sticky conflict. Proposed Note. Should be Bug.**

```
square + proof 1 0 / d -1 2 0 / 0: python and native ok True, rup 2, dels 1. Input sat False.
length-one: () acceptable False, preserves_sat False. operational: acceptable True.
rate -f -p and -f -p -d: s VERIFIED
```

The `0` is accepted though it is not RUP on the clauses present, so the Critical step clause is met
literally, as with deletion-2. It is not Critical: the input really is unsatisfiable, the conflict was
genuine when reached, and no wrong verdict is possible once Candidate 1 is fixed. It should not be a Note
either, because a Note is a disagreement with drat-trim, and here `rate` agrees with dratify. What it
contradicts is dratify's own text: `deletions` reports the clause as applied and `proof.py:473` promises
checking against the clauses present. Either document that a refutation is final or change it. The
pseudo-unit rule alone does not settle this, so it needs its own decision when Candidate 1 is fixed.

**root-3(a): Note stands, with a documentation gap.** A formula refuted by propagation gives `ok=True`,
`reached_empty=True`, `steps=0` on an empty proof or on `2 0`. Correct under the campaign's rubric, since
the formula is unsatisfiable and the reason says what happened. But `SECURITY.md` also calls it Critical
when "the proof does not derive the empty clause", and AGENTS.md describes `reached_empty` as whether it
was "actually derived". Those two sentences need an exception.

**Parser findings stay as rated.** parsing-2, parsing-3's NBSP-before-`c`, and parsing-6 lose clauses, so
they fail closed for the checker. literals-6's digit forms are in files the solvers refuse, per the
findings, so those files have no conventional meaning to contradict. parsing-4 is what lets Candidate 2
pass `strict=True`: fix them together.

## Reproducing

```python
import cdclkit_native
from campaign import oracle
from dratify import check_proof, parse_dimacs, register_native
register_native(cdclkit_native)

f = parse_dimacs("p cnf 2 2\n1 0\n-1 2 0\n")
for e in ("python", "native"):
    print(e, check_proof(f, "d -1 2 0\n-2 0\n0\n", engine=e))
print(oracle.satisfiable([[1], [-1, 2]]))
g = parse_dimacs("p cnf 1 1\nc\x0cp cnf 1 2\n1 0\nc\x0c-1 0\n", strict=True)
print(g.clauses, check_proof(g, "0\n", engine="python").ok)
from dratify import DRATChecker
print(DRATChecker(parse_dimacs("p cnf 1 1\n1 0\n")).check([("a", (-1,)), ("a", ())]))
```

The native engine here is `cdclkit_native` 0.1.7. cdclkit's `native/Cargo.lock` pins registry dratify
0.1.10, and I did not confirm the installed binary was built from that lock. Candidate 1's minimal case
and deletion-2 were also run against `rust/` itself. The sweep compared only the installed binary.
