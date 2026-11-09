# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Soundness campaign, parsing corner: `parse_dimacs` and `parse_proof`.

A parse must either raise a clear `ValueError` or produce exactly the clauses
the text means. "What the text means" comes from a reference reader in this
file, written from the documented grammar and from how DIMACS tools read files:

* a line ends at ``\\n``, with one ``\\r`` before it taken along, and a comment
  runs to the end of its line; a file with no ``\\n`` and a ``\\r`` raises, and so
  does a ``\\r`` left on a line that is not a comment;
* tokens are separated by ASCII whitespace and an integer is ``-?[0-9]+``;
* a ``p cnf V C`` header is exactly four tokens and appears at most once;
* documented tolerances are kept: a clause spanning lines, several clauses on a
  line, a missing header or a wrong one (reported in ``header_mismatch``), the
  SATLIB ``%`` terminator, and a missing final ``0`` outside strict mode. In a
  proof, the rules in `parse_proof`'s docstring.

Every comparison ends at the oracle: the meaning of a formula and a proof go to
`campaign.oracle`, and ``ok=True`` requires that the formula *as meant* is
unsatisfiable.

Labelling is mechanical, not by pattern-matching on the text. Each open finding
is a named quirk the reference reader can be told to imitate. A mismatch carries
the label of the smallest set of quirks that makes the reference agree with what
dratify did, and one no set of quirks explains is UNEXPLAINED. Open findings stay
mismatches and the run exits non-zero until they are fixed. A finding that is
fixed leaves `QUIRKS`, so its return reads UNEXPLAINED; its quirk stays as a stub
in `--self-test`, which must flag it.

    python -m campaign.gen_parsing                 # the reported run
    python -m campaign.gen_parsing --self-test     # wrong stubs must be flagged
"""

from __future__ import annotations

import argparse
import itertools
import json
import pathlib
import random
import re
import sys
import time
from collections import Counter

from campaign import oracle
from dratify import CNF, check_proof, parse_dimacs, parse_proof, register_native
from dratify.lits import from_dimacs, to_dimacs

# --------------------------------------------------------------------------
# known findings, each a quirk the reference reader can imitate
# --------------------------------------------------------------------------

Q_BREAK = "parsing-1"   # any str.splitlines separator ends a line, and a comment
Q_HEADER = "parsing-2"  # p-prefixed first token, and tokens after the fourth
Q_LEX = "parsing-3"     # Python's int() and Unicode whitespace define the tokens
Q_MULTI = "parsing-4"   # later headers replace earlier ones
Q_TAUT = "parsing-5"    # a tautology's literals after the clash do not count
#: what still labels a mismatch: the others are fixed, and kept only for the stubs
QUIRKS = (Q_TAUT,)

FINDINGS = [
    {"id": "parsing-1", "status": "fixed", "severity": "Critical",
     "summary": "Vertical tab, form feed, bare CR, FS/GS/RS, NEL, LS, PS end a "
                "comment, so a clause hidden in a comment is read: a file "
                "minisat, cadical and kissat all call SATISFIABLE gets ok=True, "
                "even through strict=True."},
    {"id": "parsing-2", "status": "fixed", "severity": "Bug",
     "summary": "A header line's tokens after the fourth are ignored, so "
                "`p cnf 1 0 1 0` silently loses a clause, even under "
                "strict=True; `pq cnf 1 1` is also read as a header."},
    {"id": "parsing-3", "status": "fixed", "severity": "Bug",
     "summary": "Tokens are whatever int() and str.split() accept, in both "
                "parsers: `1_0` is variable 10, U+0663 is 3, U+0660 ends a "
                "clause, and U+00A0 separates literals or hides a line as a "
                "comment. All three reference solvers refuse these."},
    {"id": "parsing-4", "status": "fixed", "severity": "Bug",
     "summary": "A second `p cnf` line replaces the first, so strict=True "
                "passes `p cnf 1 1 / 1 0 / p cnf 1 2 / -1 0`, whose first "
                "header disagrees with the clauses."},
    {"id": "parsing-5", "status": "open", "severity": "Note",
     "summary": "header_mismatch has gaps: a tautology's literals after the "
                "clash do not count, so strict depends on literal order, and "
                "CNF.copy() drops the field."},
    {"id": "parsing-6", "status": "open", "severity": "Note",
     "summary": "`%` ends the formula wherever it appears, and real clauses "
                "after it are dropped silently even under strict=True when the "
                "header agrees. Documented as a SATLIB tolerance."},
    {"id": "parsing-7", "status": "open", "severity": "Note",
     "summary": "parse_proof documents reading as drat-trim's fscanf(\" %i \"), "
                "but `010` is 10 here and 8 under %i, and `0x10` raises here "
                "and is 16 under %i."},
    {"id": "parsing-8", "status": "fixed", "severity": "Note",
     "summary": "The documented bound on proof literals counts the text's "
                "length, so a comment or trailing spaces flip `5000 0` from "
                "ValueError to a checked RAT step."},
    {"id": "parsing-9", "status": "fixed", "severity": "Critical",
     "summary": "Not a parsing bug, found here. Deleting a clause that is a "
                "reason at the root leaves its implied value in place, so "
                "`-2 / 2 1` with proof `d 2 1 0, -1 0, 0` gets ok=True though "
                "x1=T, x2=F satisfies it. Every oracle flavour rejects. Both "
                "engines."},
    {"id": "parsing-10", "status": "fixed", "severity": "Bug",
     "summary": "Not a parsing bug, found here. On a rejected step that repeats "
                "a literal, failed_clause is deduplicated by Python and not by "
                "native: (2,) against (2, 2)."},
]

NOT_CHECKED = [
    "drat-trim itself: it is not on PATH, so parsing-7 rests on its documented "
    "fscanf format and a C fscanf(\" %i \") run, not on drat-trim.",
    "Binary DRAT: dratify documents text proofs only.",
    "Non-str inputs to the parsers (bytes, None).",
    "parse_dimacs_file decoding and its newline handling: tested in "
    "tests/test_text_forms.py, not by this generator.",
    "Inputs large enough to hit the header and literal bounds' floor of 2^20, "
    "beyond single over-limit values; memory and time limits are not measured.",
    "The position of a single header relative to clauses is not judged; a "
    "header after clauses is accepted as a tolerance.",
    "Deletion semantics: proofs with deletions are judged only by engine "
    "agreement, re-rendering invariance and ok=True => unsatisfiable. The "
    "deletion corner owns the rest.",
    "cdclkit's use of these parsers, beyond noting that its CLI calls "
    "parse_dimacs_file.",
]

HEADER_VARS_FLOOR = 1 << 20  # the documented floor of the header bound

# --------------------------------------------------------------------------
# the reference reader
# --------------------------------------------------------------------------


class Refused(Exception):
    """The reference says this text must raise."""


_ASCII_WS = " \t\x0b\x0c"
_ASCII_SPLIT = re.compile(r"[ \t\x0b\x0c]+")
_INT = re.compile(r"-?[0-9]+\Z")


def _lines(text, quirks):
    if Q_BREAK in quirks:
        return text.splitlines()
    if "\r" in text and "\n" not in text:
        raise Refused("CR-only")
    return [ln[:-1] if ln.endswith("\r") else ln for ln in text.split("\n")]


def _no_stray_cr(line, quirks):
    if "\r" in line and Q_LEX not in quirks:
        raise Refused("carriage return inside a line")


def _strip(line, quirks):
    return line.strip() if Q_LEX in quirks else line.strip(_ASCII_WS)


def _tokens(line, quirks):
    if Q_LEX in quirks:
        return line.split()
    return [t for t in _ASCII_SPLIT.split(line) if t]


def _int(tok, quirks):
    if Q_LEX not in quirks and not _INT.match(tok):
        raise Refused(f"bad token {tok!r}")
    try:
        return int(tok)
    except ValueError:
        raise Refused(f"bad token {tok!r}") from None


def ref_dimacs(text, strict=False, quirks=frozenset()):
    """(nvars, clauses as DIMACS tuples, header_mismatch truthy), or Refused."""
    nvars = 0
    clauses = []
    pending = []
    tautologies = 0
    declared = None
    limit = max(len(text), HEADER_VARS_FLOOR)

    def finish():
        nonlocal nvars, tautologies
        seen = []
        taut = False
        for d in pending:
            if d in seen:
                continue
            if -d in seen:
                taut = True
                if Q_TAUT in quirks:
                    break
                continue
            seen.append(d)
        reach = seen if taut and Q_TAUT in quirks else pending
        for d in reach:
            nvars = max(nvars, abs(d))
        if taut:
            tautologies += 1
        else:
            clauses.append(tuple(seen))

    for raw in _lines(text, quirks):
        line = _strip(raw, quirks)
        if not line:
            continue
        head = line[0]
        if head == "c":
            continue
        _no_stray_cr(line, quirks)
        if head == "%":
            break
        if head == "p":
            parts = _tokens(line, quirks)
            if len(parts) < 4 or parts[1] != "cnf":
                raise Refused("malformed header")
            if Q_HEADER not in quirks and (parts[0] != "p" or len(parts) != 4):
                raise Refused("malformed header")
            if declared is not None and Q_MULTI not in quirks:
                raise Refused("second header")
            dv, dc = _int(parts[2], quirks), _int(parts[3], quirks)
            if dv < 0 or dv > limit or dc < 0:
                raise Refused("header out of range")
            declared = (dv, dc)
            nvars = max(nvars, dv)
            continue
        for tok in _tokens(line, quirks):
            d = _int(tok, quirks)
            if d == 0:
                finish()
                pending = []
            else:
                if abs(d) > limit:
                    raise Refused("literal out of range")
                pending.append(d)
    if pending:
        if strict:
            raise Refused("unterminated clause")
        finish()
    mismatch = False
    if declared is not None:
        mismatch = (declared[0] != nvars
                    or declared[1] != len(clauses) + tautologies)
        if mismatch and strict:
            raise Refused("header mismatch")
    return nvars, tuple(clauses), mismatch


def ref_proof(text, quirks=frozenset()):
    """Steps as ("a" | "d", DIMACS tuple) exactly as written, or Refused."""
    steps = []
    kind = "a"
    lits = []
    opened = False
    for raw in _lines(text, quirks):
        line = _strip(raw, quirks)
        if not line or line[0] == "c":
            continue
        _no_stray_cr(line, quirks)
        for tok in _tokens(line, quirks):
            num = tok
            if tok[0] == "d":
                if opened:
                    raise Refused("d inside a clause")
                kind, opened = "d", True
                num = tok[1:]
                if not num:
                    continue
            d = _int(num, quirks)
            if d == 0:
                steps.append((kind, tuple(lits)))
                kind, lits, opened = "a", [], False
            else:
                lits.append(d)
                opened = True
    if opened:
        raise Refused("unterminated clause")
    return tuple(steps)


# --------------------------------------------------------------------------
# what is under test, and the wrong stubs for --self-test
# --------------------------------------------------------------------------

RESULT_FIELDS = ("ok", "reason", "steps", "rup_steps", "rat_steps", "deletions",
                 "ignored_deletions", "resolvents_checked", "failed_step",
                 "failed_clause", "reached_empty")


def _dimacs_view(f):
    clauses = tuple(tuple(to_dimacs(l) for l in c) for c in f.clauses)
    return f.nvars, clauses, bool(f.header_mismatch)


def _fields(r):
    return tuple(getattr(r, name) for name in RESULT_FIELDS)


class Real:
    """dratify as it is."""

    name = "dratify"
    check_copy = True

    def parse_dimacs(self, text, strict=False):
        return parse_dimacs(text, strict=strict)

    def parse_proof(self, text):
        return [(k, tuple(to_dimacs(l) for l in c)) for k, c in parse_proof(text)]

    def check(self, f, proof_text, engine):
        return check_proof(f, proof_text, engine=engine)

    def check_steps(self, f, steps, engine):
        internal = [(k, tuple(from_dimacs(d) for d in c)) for k, c in steps]
        return check_proof(f, internal, engine=engine)


class _FromReference(Real):
    """The reference reader behind dratify's API, and the real checkers."""

    check_copy = False
    quirks = frozenset()

    def parse_dimacs(self, text, strict=False):
        try:
            nvars, clauses, mismatch = ref_dimacs(text, strict, self.quirks)
        except Refused as e:
            raise ValueError(str(e)) from None
        f = CNF(nvars)
        for c in clauses:
            f.add_dimacs(c)
        f.header_mismatch = (0, 1) if mismatch else None
        return f

    def parse_proof(self, text):
        try:
            return [(k, tuple(c)) for k, c in ref_proof(text, self.quirks)]
        except Refused as e:
            raise ValueError(str(e)) from None

    def check(self, f, proof_text, engine):
        return self.check_steps(f, self.parse_proof(proof_text), engine)


class CleanStub(_FromReference):
    """Every known parsing finding fixed: the harness must report nothing."""

    name = "clean: reference reader, real checkers"


class AcceptAll(_FromReference):
    name = "wrong: checker accepts everything"

    def check_steps(self, f, steps, engine):
        r = super().check_steps(f, steps, engine)
        r.ok, r.reached_empty, r.failed_step, r.failed_clause = True, True, -1, None
        return r


class RejectAll(_FromReference):
    name = "wrong: checker rejects everything"

    def check_steps(self, f, steps, engine):
        r = super().check_steps(f, steps, engine)
        r.ok, r.reached_empty = False, False
        return r


class DropsLastClause(_FromReference):
    name = "wrong: parse_dimacs drops the last clause"

    def parse_dimacs(self, text, strict=False):
        f = super().parse_dimacs(text, strict)
        f.clauses = f.clauses[:-1]
        return f


class AcceptsAnything(_FromReference):
    name = "wrong: parsers turn every error into an empty result"

    def parse_dimacs(self, text, strict=False):
        try:
            return super().parse_dimacs(text, strict)
        except ValueError:
            return CNF()

    def parse_proof(self, text):
        try:
            return super().parse_proof(text)
        except ValueError:
            return []


class RaisesAlways(_FromReference):
    name = "wrong: parsers raise on everything"

    def parse_dimacs(self, text, strict=False):
        raise ValueError("no")

    def parse_proof(self, text):
        raise ValueError("no")


class WrongException(_FromReference):
    name = "wrong: a parser raises KeyError for a bad token"

    def parse_dimacs(self, text, strict=False):
        try:
            return super().parse_dimacs(text, strict)
        except ValueError:
            raise KeyError("bad token") from None


class FirstZeroOnly(_FromReference):
    name = "wrong: parse_proof stops each line at its first 0 (the 0.1.10 bug)"

    def parse_proof(self, text):
        kept = []
        for line in text.split("\n"):
            toks = line.split()
            if not line.lstrip().startswith("c") and "0" in toks:
                toks = toks[:toks.index("0") + 1]
            kept.append(" ".join(toks) if toks else line)
        return super().parse_proof("\n".join(kept))


class CommentEatsLine(_FromReference):
    name = "wrong: parse_dimacs treats a line with any `c` token as a comment"

    def parse_dimacs(self, text, strict=False):
        lines = ["c" if " c " in f" {l} " else l for l in text.split("\n")]
        return super().parse_dimacs("\n".join(lines), strict)


class LinesEndAnywhere(_FromReference):
    name = "wrong: str.splitlines ends a line and a comment (parsing-1, fixed)"
    quirks = frozenset({Q_BREAK})


class LongHeaders(_FromReference):
    name = "wrong: a header may start with p and run on (parsing-2, fixed)"
    quirks = frozenset({Q_HEADER})


class LenientTokens(_FromReference):
    name = "wrong: int() and str.split() define a token (parsing-3, fixed)"
    quirks = frozenset({Q_LEX})


class LastHeaderWins(_FromReference):
    name = "wrong: a later header replaces an earlier one (parsing-4, fixed)"
    quirks = frozenset({Q_MULTI})


STUBS = (AcceptAll, RejectAll, DropsLastClause, AcceptsAnything, RaisesAlways,
         WrongException, FirstZeroOnly, CommentEatsLine, LinesEndAnywhere, LongHeaders,
         LenientTokens, LastHeaderWins)


# --------------------------------------------------------------------------
# the run's state and the judges
# --------------------------------------------------------------------------


class Run:
    def __init__(self, target, engines):
        self.t = target
        self.engines = engines
        self.c = Counter()
        self.mismatches = Counter()
        self.examples = {}
        self.oracle_checks = 0

    def mismatch(self, label, what, text):
        self.mismatches[label] += 1
        key = (label, what)
        old = self.examples.get(key)
        if old is None or len(text) < len(old):
            self.examples[key] = text

    # -- parse judges -------------------------------------------------------

    def _try(self, fn, *args, **kw):
        """("ok", value) / ("raise", None) / ("wrong-exception", name)."""
        try:
            return "ok", fn(*args, **kw)
        except ValueError:
            return "raise", None
        except Exception as e:  # a caller catching ValueError gets a surprise
            return "wrong-exception", type(e).__name__

    def _explain(self, ref, actual):
        for size in range(1, len(QUIRKS) + 1):
            for subset in itertools.combinations(QUIRKS, size):
                if self._try_ref(ref, subset) == actual:
                    return "+".join(subset)
        return "UNEXPLAINED"

    @staticmethod
    def _try_ref(ref, quirks):
        try:
            return "ok", ref(frozenset(quirks))
        except Refused:
            return "raise", None

    def judge_dimacs(self, text):
        """Compare lenient and strict parses with the reference. Returns the
        lenient label, or None when dratify agreed."""
        label = None
        for strict in (False, True):
            self.c["dimacs_parses_judged"] += 1
            status, value = self._try(self.t.parse_dimacs, text, strict=strict)
            ref = lambda q, s=strict: ref_dimacs(text, s, q)
            if status == "wrong-exception":
                self.mismatch("WRONG-EXCEPTION", f"parse_dimacs raised {value}", text)
                label = label or "WRONG-EXCEPTION"
                continue
            actual = (status, _dimacs_view(value) if status == "ok" else None)
            expected = self._try_ref(ref, ())
            if actual == expected:
                if status == "raise":
                    self.c["dimacs_refused_correctly"] += 1
                continue
            lab = self._explain(ref, actual)
            mode = "strict" if strict else "lenient"
            self.mismatch(lab, f"parse_dimacs({mode}): {expected[0]} expected, "
                               f"{actual[0]} actual", text)
            label = label or lab
        return label

    def judge_proof(self, text):
        self.c["proof_parses_judged"] += 1
        status, value = self._try(self.t.parse_proof, text)
        ref = lambda q: ref_proof(text, q)
        if status == "wrong-exception":
            self.mismatch("WRONG-EXCEPTION", f"parse_proof raised {value}", text)
            return "WRONG-EXCEPTION"
        actual = (status, tuple(value) if status == "ok" else None)
        expected = self._try_ref(ref, ())
        if actual == expected:
            if status == "raise":
                self.c["proof_refused_correctly"] += 1
            return None
        lab = self._explain(ref, actual)
        self.mismatch(lab, f"parse_proof: {expected[0]} expected, {actual[0]} actual",
                      text)
        return lab

    # -- check judge --------------------------------------------------------

    def check_engines(self, f, proof_text, label_text):
        """Run every engine. Returns one result, after insisting they agree."""
        results = []
        for engine in self.engines:
            status, r = self._try(self.t.check, f, proof_text, engine)
            if status != "ok":
                self.mismatch("UNEXPLAINED", f"check_proof {status} {r} on {engine}",
                              label_text)
                return None
            results.append((engine, r))
            self.c[f"checks_{engine}"] += 1
        first = _fields(results[0][1])
        for engine, r in results[1:]:
            self.c["engine_comparisons"] += 1
            if _fields(r) != first:
                differ = [n for n, a, b in zip(RESULT_FIELDS, first, _fields(r))
                          if a != b]
                self.mismatch("UNEXPLAINED", f"engines disagree on {differ}", label_text)
        return results[0][1]

    def judge_end_to_end(self, f, f_text, proof_text, meant, label):
        """`meant` is the formula the text means. ok=True requires it unsat."""
        r = self.check_engines(f, proof_text, f"{f_text!r} / {proof_text!r}")
        if r is None:
            return None
        self.oracle_checks += 1
        if oracle.satisfiable(meant):
            self.c["e2e_meant_satisfiable"] += 1
            if r.ok:
                self.c["ok_true_on_satisfiable_text"] += 1
                self.mismatch(label or "UNEXPLAINED",
                              "ok=True on a text whose meaning is satisfiable",
                              f"{f_text!r} / {proof_text!r}")
        else:
            self.c["e2e_meant_unsatisfiable"] += 1
        return r

    def judge_walk(self, r, meant, steps, text):
        """Compare a deletion-free proof, step by step, with the oracle."""
        expected = _expected_walk(meant, steps)
        self.oracle_checks += expected["judged"]
        self.c["steps_replayed_by_oracle"] += expected["judged"]
        got = {"ok": r.ok, "failed_step": max(r.failed_step, 0), "steps": r.steps,
               "reached_empty": r.reached_empty, "rup": r.rup_steps,
               "rat": r.rat_steps}
        want = {k: expected[k] for k in got}
        if got != want:
            self.mismatch("UNEXPLAINED", f"walk: got {got}, oracle says {want}", text)
        if r.ok:
            self.c["proofs_accepted"] += 1
        else:
            self.c["proofs_rejected"] += 1
        if expected["failed_step"]:
            self.c["steps_rejected"] += 1
        self.c["steps_accepted_by_rup"] += expected["rup"]
        self.c["steps_accepted_by_rat_only"] += expected["rat"]


def _expected_walk(meant, steps):
    out = {"ok": False, "failed_step": 0, "steps": 0, "reached_empty": False,
           "rup": 0, "rat": 0, "judged": 1}
    if oracle.propagate(meant)[0]:
        out["ok"] = out["reached_empty"] = True
        return out
    upto = []
    for s in steps:
        upto.append(s)
        if not s[1]:
            break
    judged, _ = oracle.replay(meant, upto, "specified", stop_at_unacceptable=True)
    out["judged"] += len(judged)
    for step in judged:
        out["steps"] = step.index
        if not step.acceptable:
            out["failed_step"] = step.index
            return out
        if step.rup:
            out["rup"] += 1
        else:
            out["rat"] += 1
        if not step.clause:
            out["ok"] = out["reached_empty"] = True
    return out


# --------------------------------------------------------------------------
# formulas and proofs
# --------------------------------------------------------------------------


def random_clause(rng, nvars, lo=1, hi=3):
    vs = rng.sample(range(1, nvars + 1), min(nvars, rng.randint(lo, hi)))
    return [v if rng.random() < .5 else -v for v in vs]


def random_formula(rng):
    nvars = rng.randint(2, 6)
    clauses = []
    if rng.random() < .5:      # an unsatisfiable core on a few variables
        vs = rng.sample(range(1, nvars + 1), rng.randint(1, min(3, nvars)))
        for mask in range(1 << len(vs)):
            clauses.append([v if mask >> i & 1 else -v for i, v in enumerate(vs)])
    for _ in range(rng.randint(0, 2 * nvars)):
        clauses.append(random_clause(rng, nvars))
    rng.shuffle(clauses)
    return nvars, clauses


def tree_proof(clauses, nvars):
    """A compact tree refutation of an unsatisfiable formula, by the oracle."""
    current = [list(c) for c in clauses]
    steps = []

    def go(prefix, next_var):
        lemma = [-l for l in prefix]
        if not oracle.rup(current, lemma):
            for lit in (next_var, -next_var):
                go(prefix + [lit], next_var + 1)
        steps.append(("a", tuple(lemma)))
        current.append(lemma)

    go([], 1)
    return steps


def mutate_proof(rng, steps, nvars, clauses, c):
    """Lemmas that may be wrong, RAT-only lemmas, repeats, deletions."""
    steps = list(steps)
    used = max([abs(l) for cl in clauses for l in cl] + [1])
    has_deletion = False
    if rng.random() < .25 and steps:
        i = rng.randrange(len(steps))
        steps.insert(i, ("a", tuple(random_clause(rng, nvars))))
        c["proofs_with_inserted_lemma"] += 1
    if rng.random() < .1 and len(steps) > 1:
        del steps[rng.randrange(len(steps))]
        c["proofs_with_dropped_lemma"] += 1
    if rng.random() < .2:      # a definition: RAT on a fresh first literal
        fresh = used + 1
        steps.insert(0, ("a", (fresh, rng.randint(1, nvars))))
        c["proofs_with_fresh_rat"] += 1
    if rng.random() < .15 and steps:
        i = rng.randrange(len(steps))
        k, lits = steps[i]
        if lits:
            steps[i] = (k, lits + (lits[0],))
            c["steps_with_repeated_literal"] += 1
    if rng.random() < .25 and clauses:
        lits = tuple(rng.choice(clauses))
        steps.insert(rng.randrange(len(steps) + 1), ("d", lits))
        has_deletion = True
        c["proofs_with_deletion"] += 1
    return steps, has_deletion


# --------------------------------------------------------------------------
# rendering: the same meaning, written many ways
# --------------------------------------------------------------------------

COMMENTS = ("c", "c plain words", "c 1 0", "c p cnf 9 9", "c %", "c d 1 0",
            "c -1 2 0", "cnf 1 0", "c\t0", "c1 0")


def _literal_text(rng, d, c):
    r = rng.random()
    if r < .06:
        c["token_leading_zero"] += 1
        return f"{'-' if d < 0 else ''}0{abs(d)}"
    return str(d)


def _terminator_text(rng, c):
    r = rng.random()
    if r < .04:
        c["token_zero_spelling"] += 1
        return rng.choice(("00", "-0", "000"))
    return "0"


def _sep(rng, c):
    r = rng.random()
    if r < .15:
        c["whitespace_tabs_and_runs"] += 1
        return rng.choice(("  ", "\t", " \t ", "\t\t", "   "))
    if r < .18:
        c["whitespace_vt_ff_between_tokens"] += 1
        return rng.choice(("\x0b", "\x0c"))
    return " "


class Writer:
    """Accumulates lines, with comments, blanks and stray whitespace."""

    def __init__(self, rng, c, eol):
        self.rng, self.c, self.eol = rng, c, eol
        self.lines = []
        self.cur = ""

    def token(self, tok):
        self.cur += (_sep(self.rng, self.c) if self.cur else "") + tok

    def flush(self):
        if not self.cur:
            return
        line = self.cur
        self.cur = ""
        if self.rng.random() < .06:
            self.c["whitespace_leading"] += 1
            line = self.rng.choice((" ", "\t", "  ")) + line
        if self.rng.random() < .06:
            self.c["whitespace_trailing"] += 1
            line += self.rng.choice((" ", "\t", "  "))
        self.lines.append(line)

    def noise(self, in_clause):
        rng, c = self.rng, self.c
        if rng.random() < .12:
            self.flush()
            self.lines.append(rng.choice(COMMENTS))
            c["comment_inside_open_clause" if in_clause else "comment_lines"] += 1
        if rng.random() < .06:
            self.flush()
            self.lines.append(rng.choice(("", " ", "\t")))
            c["blank_lines"] += 1

    def text(self):
        self.flush()
        body = self.eol.join(self.lines)
        if self.rng.random() < .85:
            body += self.eol
        else:
            self.c["no_final_newline"] += 1
        return body


def _eol(rng, c):
    if rng.random() < .2:
        c["crlf_texts"] += 1
        return "\r\n"
    return "\n"


def render_formula(rng, clauses, nvars, c):
    """DIMACS text meaning `clauses`, in a documented tolerance or two."""
    w = Writer(rng, c, _eol(rng, c))
    if rng.random() < .2:
        w.lines.append(rng.choice(COMMENTS))
        c["comment_lines"] += 1
    used = max([abs(l) for cl in clauses for l in cl] + [0])
    declared_vars, declared_clauses = max(nvars, used), len(clauses)
    r = rng.random()
    if r < .55:
        c["header_correct"] += 1
    elif r < .7:
        declared_vars = None
        c["header_absent"] += 1
    elif r < .8:
        declared_vars += rng.randint(1, 4)
        c["header_declares_unused_vars"] += 1
    elif r < .9:
        declared_clauses += rng.choice((-1, 1, 3)) if clauses else 2
        c["header_wrong_clause_count"] += 1
    elif used > 0:
        declared_vars = max(0, used - 1)
        c["header_too_few_vars"] += 1
    if declared_vars is not None:
        w.lines.append(f"p{_sep(rng, c)}cnf{_sep(rng, c)}{declared_vars}"
                       f"{_sep(rng, c)}{declared_clauses}")
    drop_final_zero = bool(clauses and clauses[-1]) and rng.random() < .1
    for i, clause in enumerate(clauses):
        w.noise(False)
        for j, d in enumerate(clause):
            w.token(_literal_text(rng, d, c))
            if j + 1 < len(clause) and rng.random() < .1:
                w.flush()
                c["clause_split_across_lines"] += 1
                w.noise(True)
        last = i + 1 == len(clauses)
        if last and drop_final_zero:
            c["missing_final_zero"] += 1
            break
        if not clause:
            c["empty_clause_in_formula"] += 1
        w.token(_terminator_text(rng, c))
        if rng.random() < .8 or last:
            w.flush()
        else:
            c["several_clauses_on_a_line"] += 1
    w.flush()
    r = rng.random()
    if r < .15:
        w.lines.extend(("%", "0") if rng.random() < .7 else ("%",))
        c["percent_terminator"] += 1
    return w.text()


def render_proof(rng, steps, c):
    w = Writer(rng, c, _eol(rng, c))
    for kind, lits in steps:
        w.noise(False)
        if kind == "d":
            r = rng.random()
            if r < .2 and lits:
                c["proof_d_without_space"] += 1
                w.token("d" + _literal_text(rng, lits[0], c))
                lits = lits[1:]
            elif r < .35:
                w.token("d")
                w.flush()
                c["proof_d_alone_on_a_line"] += 1
            else:
                w.token("d")
        for j, d in enumerate(lits):
            w.token(_literal_text(rng, d, c))
            if j + 1 < len(lits) and rng.random() < .1:
                w.flush()
                c["proof_clause_split_across_lines"] += 1
                w.noise(True)
        w.token(_terminator_text(rng, c))
        if rng.random() < .8:
            w.flush()
        else:
            c["proof_several_clauses_on_a_line"] += 1
    return w.text()


# --------------------------------------------------------------------------
# hostile text
# --------------------------------------------------------------------------

#: every character str.splitlines breaks on, other than \n
LINE_BREAKS = ("\r", "\x0b", "\x0c", "\x1c", "\x1d", "\x1e", "\x85", " ",
               " ")
#: whitespace to Python, and not to a DIMACS reader
UNICODE_SPACES = ("\x1f", "\xa0", " ", "　", "\x85", " ", "\x1c")
#: decimal digits to int(), and not to anything else
UNICODE_DIGITS = {0: "٠", 1: "١", 2: "٢", 3: "٣",
                  4: "４", 5: "５", 6: "०"}

MUST_RAISE_DIMACS = (
    "p cnf 1 1\nx 0\n", "1.0 0\n", "0x1 0\n", "--1 0\n", "+ 0\n", "- 0\n",
    "1 0 c note\n", "d 1 0\n", "p cnf 99999999999 0\n", "p cnf -5 1\n",
    "p cnf x y\n", "p cnf 1\n", "p dnf 1 1\n", "p\n", "P CNF 1 1\n",
    "﻿p cnf 1 1\n1 0\n", "1 2 0\n\x00", "1 0 %\n", "99999999999 0\n",
    "1 " + "9" * 5000 + " 0\n", "p cnf 1 " + "9" * 5000 + "\n",
    "+1 0\n", "+0\n", "1 +0\n", "p cnf +1 1\n1 0\n",
    "p cnf 1 1\r1 0\r", "c x\r1 0\r", "1 0\r2 0\r", "1 0\r2 0\n", "1 0\r\r\n",
)
MUST_RAISE_PROOF = (
    "%\n", "p cnf 1 1\n", "1 0 junk\n", "1 0 c note\n", "1 0\n2\n", "d\n",
    "1 0 d\n", "1 d 2 0\n", "d d 1 0\n", "dd1 0\n", "x 0\n", "a 1 0\n",
    "D 1 0\n", "1.0 0\n", "0x1 0\n", "d 1\n", "﻿1 0\n", "1\x000\n",
    "1 " + "9" * 5000 + " 0\n",
    "+1 0\n", "d+1 0\n", "1 0\r0\r", "c x\r1 0\r", "1 0\r2 0\n", "1 0\r\r\n",
)
SOUP_TOKENS = ("0", "0", "0", "1", "-1", "2", "-2", "3", "-3", "00", "+1", "-0",
               "d", "d1", "d-2", "d0", "c", "c x", "p", "cnf", "p cnf 3 2",
               "p cnf 2 1 1 0", "pq cnf 1 1", "%", "%%", "x", "1_0", "٣",
               "٠", "１", "1.0", "0x1", "--1", "+", "-")
SOUP_SEPS = (" ", " ", " ", "\t", "  ", "\n", "\n", "\n", "\r\n", "\r", "\x0b",
             "\x0c", "\x1c", "\x1f", "\x85", " ", "\xa0", "　", "\n\n")


def dimacs_text(clauses, nvars, header=True):
    body = "".join(" ".join(map(str, c)) + (" 0\n" if c else "0\n") for c in clauses)
    return (f"p cnf {nvars} {len(clauses)}\n" if header else "") + body


def hostile_dimacs(rng, nvars, clauses, c):
    """A text with a defect, and the category that claims it."""
    base = dimacs_text(clauses, nvars)
    extra = " ".join(map(str, random_clause(rng, nvars)))
    kind = rng.choice(("comment_break", "header_trailing", "header_prefix",
                       "second_header", "underscore", "digits", "spaces",
                       "tautology_order", "junk"))
    if kind == "comment_break":
        ch = rng.choice(LINE_BREAKS)
        c[f"hostile_comment_break_U+{ord(ch):04X}"] += 1
        text = base + f"c note{ch}{extra} 0\n"
    elif kind == "header_trailing":
        text = f"p cnf {nvars} {len(clauses)} {extra} 0\n" + base.split("\n", 1)[1]
    elif kind == "header_prefix":
        text = "p" + rng.choice(("q", "x", "1", "cnf")) + base[1:]
    elif kind == "second_header":
        text = base + f"p cnf {nvars} {len(clauses) + 1}\n{extra} 0\n"
    elif kind == "underscore":
        text = f"p cnf 16 1\n1_{rng.randint(0, 6)} 0\n"
    elif kind == "digits":
        d = rng.randint(1, 6)
        terminator = rng.random() < .3
        text = (f"p cnf 6 1\n{d} {UNICODE_DIGITS[0]}\n" if terminator
                else f"p cnf 6 1\n{UNICODE_DIGITS[d]} 0\n")
    elif kind == "spaces":
        sp = rng.choice(UNICODE_SPACES)
        text = rng.choice((f"p cnf 2 1\n1{sp}2 0\n", f"p{sp}cnf 2 1\n1 2 0\n",
                           f"p cnf 2 1\n1 2 0\n{sp}c {extra} 0\n"))
    elif kind == "tautology_order":
        text = f"p cnf 1 1\n1 -1 {rng.randint(2, 6)} 0\n"
    else:
        text = base + rng.choice(("1 0 c trailing\n", "junk 0\n", "1 2\nnope\n"))
    c[f"hostile_dimacs_{kind}"] += 1
    return text


def hostile_proof(rng, nvars, c):
    lit = rng.randint(1, nvars)
    kind = rng.choice(("comment_break", "underscore", "digits", "spaces", "after_d",
                       "junk"))
    if kind == "comment_break":
        ch = rng.choice(LINE_BREAKS)
        c[f"hostile_comment_break_U+{ord(ch):04X}"] += 1
        text = f"c note{ch}{rng.choice(('', 'd '))}{lit} 0\n0\n"
    elif kind == "underscore":
        text = f"1_{rng.randint(0, 6)} 0\n"
    elif kind == "digits":
        d = rng.randint(1, 6)
        text = rng.choice((f"{UNICODE_DIGITS[d]} 0\n", f"{d} {UNICODE_DIGITS[0]}\n",
                           f"d{UNICODE_DIGITS[d]} 0\n"))
    elif kind == "spaces":
        sp = rng.choice(UNICODE_SPACES)
        text = rng.choice((f"1{sp}2 0\n", f"{sp}c 1 0\n"))
    elif kind == "after_d":
        text = rng.choice(("d1_0 0\n", "d+1 0\n", "d0\n", "d 0\n", "d-1 0\n", "d00\n"))
    else:
        text = rng.choice(("1 0 c trailing\n", "junk 0\n", "1 2\n", "1 d 2 0\n"))
    c[f"hostile_proof_{kind}"] += 1
    return text


def smuggled_refutation(rng, c):
    """A satisfiable meaning, and comments that make dratify read a refutation.

    One form hides a second header too, which is what gets it past strict=True.
    """
    v = rng.randint(1, 4)
    ch = rng.choice(LINE_BREAKS)
    keep = rng.choice((v, -v))
    if rng.random() < .5:
        c["smuggle_with_hidden_header"] += 1
        text = (f"p cnf {v} 1\nc x{ch}p cnf {v} 2\n{keep} 0\n"
                f"c y{ch}{-keep} 0\n")
    else:
        c["smuggle_header_disagrees"] += 1
        text = f"p cnf {v} 1\n{keep} 0\nc y{ch}{-keep} 0\n"
    return text, [(keep,)], "0\n"


def soup(rng):
    parts = []
    for _ in range(rng.randint(1, 10)):
        parts.append(rng.choice(SOUP_TOKENS))
        parts.append(rng.choice(SOUP_SEPS))
    return "".join(parts)


# --------------------------------------------------------------------------
# one instance
# --------------------------------------------------------------------------


def run_instance(run, rng):
    c = run.c
    # a formula and a proof, each written in documented tolerances
    nvars, clauses = random_formula(rng)
    written = [list(cl) for cl in clauses]
    r = rng.random()
    if r < .1 and written:
        i = rng.randrange(len(written))
        written[i] = written[i] + [written[i][0]]
        c["formula_repeated_literal"] += 1
    elif r < .2:
        v = rng.randint(1, nvars)
        written.insert(rng.randrange(len(written) + 1), [v, -v])
        c["formula_tautology"] += 1
    elif r < .23:
        written.insert(rng.randrange(len(written) + 1), [])
        c["formula_empty_clause"] += 1

    f_text = render_formula(rng, written, nvars, c)
    c["texts_well_formed"] += 1
    c["texts"] += 1
    label = run.judge_dimacs(f_text)

    # the reference must itself recover what the generator wrote
    try:
        ref = ref_dimacs(f_text)
    except Refused as e:
        run.mismatch("UNEXPLAINED", f"harness: reference refused its own text: {e}",
                     f_text)
        return
    if [set(cl) for cl in ref[1]] != [set(cl) for cl in written
                                      if not any(-l in cl for l in cl)]:
        run.mismatch("UNEXPLAINED", "harness: reference misread its own text", f_text)
        return

    meant = [list(cl) for cl in ref[1]]
    # the proof
    if oracle.satisfiable(meant):
        base = [("a", tuple(random_clause(rng, nvars))) for _ in range(rng.randint(0, 3))]
        base.append(("a", ()))
    else:
        base = tree_proof(meant, nvars)
    steps, has_deletion = mutate_proof(rng, base, nvars, meant, c)
    p_text = render_proof(rng, steps, c)
    c["proofs_well_formed"] += 1
    p_label = run.judge_proof(p_text)
    try:
        ref_steps = ref_proof(p_text)
    except Refused as e:
        run.mismatch("UNEXPLAINED", f"harness: reference refused its own proof: {e}",
                     p_text)
        return
    if list(ref_steps) != [(k, tuple(l)) for k, l in steps]:
        run.mismatch("UNEXPLAINED", "harness: reference misread its own proof", p_text)
        return

    status, f = run._try(run.t.parse_dimacs, f_text)
    if status == "ok" and p_label is None:
        pair = f"{f_text!r} / {p_text!r}"
        result = run.judge_end_to_end(f, f_text, p_text, meant, label)
        if result is not None:
            if has_deletion:
                c["proofs_with_deletion_judged_e2e_only"] += 1
                c["deletions_applied"] += result.deletions
                c["deletions_ignored"] += result.ignored_deletions
            elif label is None:
                run.judge_walk(result, meant, steps, pair)
            # the same proof given as data must get the same result
            for engine in run.engines:
                got = run._try(run.t.check_steps, f, steps, engine)
                c["text_vs_list_comparisons"] += 1
                if got[0] != "ok" or _fields(got[1]) != _fields(
                        run.t.check(f, p_text, engine)):
                    run.mismatch("UNEXPLAINED", f"text and list differ on {engine}", pair)

    # defects: each must raise or read as the reference does
    d_text = hostile_dimacs(rng, nvars, written or [[1]], c)
    c["texts_hostile"] += 1
    c["texts"] += 1
    run.judge_dimacs(d_text)
    p2 = hostile_proof(rng, nvars, c)
    c["proofs_hostile"] += 1
    run.judge_proof(p2)

    # a refutation hidden in comments, end to end
    s_text, s_meant, s_proof = smuggled_refutation(rng, c)
    c["texts"] += 1
    s_label = run.judge_dimacs(s_text)
    status, s_f = run._try(run.t.parse_dimacs, s_text)
    if status == "ok":
        run.judge_end_to_end(s_f, s_text, s_proof, s_meant, s_label)

    # token soup
    c["soup_texts"] += 1
    text = soup(rng)
    run.judge_dimacs(text)
    run.judge_proof(text)

    # CNF.copy keeps what the parser reported
    if run.t.check_copy:
        g = run.t.parse_dimacs(f"p cnf {nvars} {len(clauses) + 1}\n"
                               + dimacs_text(clauses, nvars, header=False))
        c["copy_checks"] += 1
        if g.header_mismatch and g.copy().header_mismatch != g.header_mismatch:
            run.mismatch(Q_TAUT, "CNF.copy() drops header_mismatch",
                         f"p cnf {nvars} {len(clauses) + 1} / ...")

    # notes: documented behaviour worth a count, not a mismatch
    if run.t.check_copy:
        note_percent(run, rng)
        note_padding(run, rng)


def note_percent(run, rng):
    """`%` ends the formula even with real clauses after it."""
    v = rng.randint(1, 4)
    text = f"p cnf {v} 1\n{v} 0\n%\n{-v} 0\n"
    status, f = run._try(run.t.parse_dimacs, text, strict=True)
    if status == "ok" and len(f.clauses) == 1:
        run.c["note_percent_drops_real_clause_under_strict"] += 1


def note_padding(run, rng):
    """A proof literal's bound reads the steps and not the text: parsing-8, fixed."""
    lit = rng.randint(1000, 4000)
    f = run.t.parse_dimacs("p cnf 2 1\n1 2 0\n")
    bare = run._try(run.t.check, f, f"{lit} 0\n", "python")
    padded = run._try(run.t.check, f, f"c {'x' * 5000}\n{lit} 0\n", "python")
    if bare[0] == padded[0] == "ok":
        run.c["literal_bound_ignores_padding"] += 1
    else:
        run.mismatch("UNEXPLAINED", "padding changes whether a literal is allowed",
                     f"{lit} 0\n")


# --------------------------------------------------------------------------
# driving it
# --------------------------------------------------------------------------

#: categories this generator claims to reach; zero fails the run
REQUIRED = (
    "texts_well_formed", "texts_hostile", "proofs_well_formed", "proofs_hostile",
    "soup_texts", "dimacs_parses_judged", "proof_parses_judged",
    "dimacs_refused_correctly", "proof_refused_correctly", "must_raise_dimacs",
    "must_raise_proof", "comment_lines", "comment_inside_open_clause",
    "blank_lines", "whitespace_tabs_and_runs", "whitespace_vt_ff_between_tokens",
    "whitespace_leading", "whitespace_trailing", "no_final_newline", "crlf_texts",
    "clause_split_across_lines", "several_clauses_on_a_line", "missing_final_zero",
    "header_correct", "header_absent", "header_declares_unused_vars",
    "header_wrong_clause_count", "header_too_few_vars", "percent_terminator",
    "formula_repeated_literal", "formula_tautology", "formula_empty_clause",
    "token_leading_zero", "token_zero_spelling",
    "proof_d_without_space", "proof_d_alone_on_a_line",
    "proof_clause_split_across_lines", "proof_several_clauses_on_a_line",
    "steps_replayed_by_oracle", "steps_accepted_by_rup",
    "steps_accepted_by_rat_only", "steps_rejected", "proofs_accepted",
    "proofs_rejected", "proofs_with_deletion_judged_e2e_only", "deletions_applied",
    "deletions_ignored", "steps_with_repeated_literal", "e2e_meant_satisfiable",
    "e2e_meant_unsatisfiable", "engine_comparisons", "text_vs_list_comparisons",
    "checks_python", "checks_native", "smuggle_with_hidden_header",
    "smuggle_header_disagrees", "hostile_dimacs_comment_break",
    "hostile_dimacs_header_trailing", "hostile_dimacs_header_prefix",
    "hostile_dimacs_second_header", "hostile_dimacs_underscore",
    "hostile_dimacs_digits", "hostile_dimacs_spaces", "hostile_dimacs_tautology_order",
    "hostile_dimacs_junk", "hostile_proof_comment_break", "hostile_proof_underscore",
    "hostile_proof_digits", "hostile_proof_spaces", "hostile_proof_after_d",
    "hostile_proof_junk", "copy_checks",
    "note_percent_drops_real_clause_under_strict",
    "literal_bound_ignores_padding",
) + tuple(f"hostile_comment_break_U+{ord(ch):04X}" for ch in LINE_BREAKS)


def run_harness(target, seed, instances, engines):
    rng = random.Random(seed)
    run = Run(target, engines)
    for text in MUST_RAISE_DIMACS:
        run.c["must_raise_dimacs"] += 1
        if run.judge_dimacs(text) is None and not _refuses(ref_dimacs, text):
            run.mismatch("UNEXPLAINED", "harness: reference accepts a must-raise", text)
    for text in MUST_RAISE_PROOF:
        run.c["must_raise_proof"] += 1
        if run.judge_proof(text) is None and not _refuses(ref_proof, text):
            run.mismatch("UNEXPLAINED", "harness: reference accepts a must-raise", text)
    for _ in range(instances):
        run_instance(run, rng)
    return run


def _refuses(ref, text):
    try:
        ref(text)
    except Refused:
        return True
    return False


def self_test(seed, instances, engines):
    failed = 0
    print(f"self-test: {instances} instances per stub, seed {seed}")
    def parser_side(run):
        return sum(run.mismatches.values())

    for cls in STUBS:
        run = run_harness(cls(), seed, instances, engines)
        flagged = parser_side(run)
        verdict = "flagged" if flagged else "MISSED"
        failed += not flagged
        print(f"  {verdict:8} {flagged:6} mismatches  {cls.name}")
    run = run_harness(CleanStub(), seed, instances, engines)
    flagged = parser_side(run)
    print(f"  {'clean' if not flagged else 'NOISY':8} {flagged:6} mismatches  "
          f"{CleanStub.name}")
    for (label, what), text in sorted(run.examples.items()):
        print(f"    [{label}] {what}: {text!r}")
    failed += bool(flagged)
    return failed


def native_engine():
    try:
        import cdclkit_native
    except ImportError:
        return None
    register_native(cdclkit_native)
    return "native"


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--seed", type=int, default=20261108)
    ap.add_argument("--instances", type=int, default=20000)
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--results", default="campaign/results/parsing.json",
                    help="where to write the results; empty to skip")
    args = ap.parse_args(argv)

    native = native_engine()
    engines = ["python"] + ([native] if native else [])

    if args.self_test:
        failed = self_test(args.seed, min(args.instances, 300), engines)
        print("self-test", "FAILED" if failed else "passed")
        return 1 if failed else 0

    t0 = time.perf_counter()
    run = run_harness(Real(), args.seed, args.instances, engines)
    runtime = time.perf_counter() - t0

    counts = dict(sorted(run.c.items()))
    zero = [name for name in REQUIRED if not run.c[name]]
    unexplained = sum(n for label, n in run.mismatches.items()
                      if label == "UNEXPLAINED" or label == "WRONG-EXCEPTION")
    total = sum(run.mismatches.values())

    print(f"seed {args.seed}, {args.instances} instances, {runtime:.1f}s, "
          f"{run.oracle_checks} oracle checks")
    for name, n in counts.items():
        print(f"  {name}: {n}")
    print("mismatches by label:")
    for label, n in sorted(run.mismatches.items()):
        print(f"  {label}: {n}")
    print("shortest example of each:")
    for (label, what), text in sorted(run.examples.items()):
        print(f"  [{label}] {what}\n      {text!r}")

    if args.results:
        out = {
            "corner": "parsing",
            "seeds": [args.seed],
            "instances": args.instances,
            "steps": run.oracle_checks,
            "per_category_counts": counts,
            "mismatches_by_label": dict(sorted(run.mismatches.items())),
            "runtime_seconds": round(runtime, 1),
            "findings": FINDINGS,
            "not_checked": NOT_CHECKED,
        }
        path = pathlib.Path(args.results)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(out, indent=2, ensure_ascii=True) + "\n",
                        encoding="ascii")

    status = 0
    if zero:
        print(f"FAIL: categories never reached: {zero}")
        status = 1
    if total:
        print(f"FAIL: {total} mismatches, {unexplained} of them unexplained")
        status = 1
    return status


if __name__ == "__main__":
    sys.exit(main())
