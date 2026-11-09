# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Soundness campaign, the literals corner: what a clause is, as written.

Repeated and complementary literals in formulas and lemmas, variables above the
header's count, ``-0`` and the other spellings of a terminator, the bound on a
literal, and the surfaces that take literals without the parser in front.

Every proof is judged by ``campaign/oracle.py`` under ``operational``, the
deletion rule dratify documents, on the formula as ``CNF.add`` documents it
(a clause is a set, tautologies dropped), and on both engines. The end-to-end
question comes first: ``ok=True`` requires ``not oracle.satisfiable(F)``.

Run from the repo root::

    python -m campaign.gen_literals                 # defaults reproduce results
    python -m campaign.gen_literals --seed 7 --instances 500 --no-write
    python -m campaign.gen_literals --self-test

Exit status is non-zero on any mismatch, labelled or not, and on any category
left at zero. Open findings therefore fail the run until they are fixed. A fixed
finding has no label here any more, so one that comes back reads UNEXPLAINED.
"""

from __future__ import annotations

import argparse
import collections
import json
import pathlib
import random
import re
import sys
import time
from unittest import mock

from campaign import oracle
from dratify import (CNF, DRATChecker, check_proof, parse_dimacs, parse_proof,
                     register_native, to_dimacs)
from dratify.cnf import HEADER_VARS_FLOOR
from dratify.proof import CheckResult

RESULTS = pathlib.Path(__file__).parent / "results" / "literals.json"
DEFAULT_SEEDS = (1, 2, 3)
DEFAULT_INSTANCES = 10000          # per seed

FIELDS = ("ok", "reason", "steps", "rup_steps", "rat_steps", "deletions",
          "ignored_deletions", "resolvents_checked", "failed_step",
          "failed_clause", "reached_empty")

#: every category the run claims to reach; zero in any of them fails the run
CATEGORIES = """
formula_repeated_literal formula_unit_by_repeat formula_tautology_dropped
formula_var_above_header formula_empty_clause formula_refuted_by_up
header_clean header_mismatch_reported
lemma_repeat_rup lemma_repeat_rat lemma_repeat_rejected lemma_unit_by_repeat
lemma_pivot_repeated_rat lemma_complementary_accepted
rat_accepted rejected_steps rat_tautological_resolvent_skipped
rat_blocked_by_tautological_d fresh_var_rat fresh_var_rup
del_repeat_applied del_unit_by_repeat_ignored del_unit_ignored
del_tautological_lemma_applied del_formula_tautology_absent del_absent
del_fresh_var del_empty_clause del_shuffled_applied
minus_zero_formula minus_zero_proof other_zero_spelling
bound_at_limit_accepted bound_with_a_gap_accepted bound_above_limit_refused
bound_huge_refused bound_padded_still_refused formula_floor_accepted formula_floor_plus_one_refused
token_leading_zero token_lenient token_bad_refused
comment_formula comment_proof
surface_add_normalises surface_add_negative_refused surface_negative_formula
surface_repeat_formula surface_checker_negative_step
variant_no_rat variant_no_deletions list_form_compared roundtrip
ok_true_unsat ok_false_no_empty ok_false_rejected del_reason_ignored
engines_compared
""".split()

#: mismatch labels that stand for a written-up finding, and nothing else does
KNOWN = {
    "nvars-tautology": ("literals-7", "Note",
                        "CNF.add stops growing nvars at the literal that makes "
                        "a tautology, so nvars and strict parsing depend on "
                        "literal order."),
}

#: written up, and fixed. These labels no longer explain anything, so a mismatch
#: that earns one again reads UNEXPLAINED and fails the run.
FIXED = {
    "stale-root": "literals-1", "failed-clause-repeats": "literals-2",
    "bound-refuses-valid": "literals-3", "comment-split": "literals-4",
    "unvalidated-surface": "literals-5", "repeat-surface": "literals-5",
    "token-lenient": "literals-6",
}

NOT_CHECKED = [
    "binary DRAT: dratify reads text only",
    "drat-trim: not run in this corner (gen_drat_trim.py runs it); what is said of it here comes from "
    "this repo's docs and the oracle's flavours",
    "octal readings: fscanf %i takes 010 as 8 and dratify as 10, not compared",
    "the % terminator and clauses after it, and headers with extra tokens "
    "(parsing corner)",
    "proofs from a real solver: every proof is generated against the oracle",
    "formulas past 10 variables plus fresh ones: the oracle's table stays small "
    "on purpose",
    "variables near 2^32 or memory exhaustion on native: a CNF built with "
    "nvars >= 2^32 is checked once for one answer, never allocated",
    "the Rust API directly: native is reached through cdclkit_native and "
    "check_proof, so Checker::new and check_step are not called on their own",
    "the literal bound on the list and MemoryProof shapes above the floor: "
    "compared on fresh variables within the bound, and one huge-literal case",
    "a proof long enough for its occurrences to raise the literal bound past the "
    "floor: that takes a million literals, and is tested on the rule itself",
]


# ---------------------------------------------------------------------------
# what the documentation says a formula is
# ---------------------------------------------------------------------------


def as_set(clause):
    return tuple(dict.fromkeys(clause))


def is_taut(clause):
    s = set(clause)
    return any(-l in s for l in s)


def normalise(raw):
    """`CNF.add`: duplicates collapse, first occurrences keep their order, and
    tautologies are dropped entirely."""
    return [list(as_set(c)) for c in raw if not is_taut(c)]


class Unreadable(ValueError):
    """Text a C DIMACS reader would refuse."""


_ASCII_INT = re.compile(r"-?[0-9]+\Z")
_C_SPACE = " \t\x0b\x0c"


def _reference_lines(text):
    """`\\n` ends a line and one `\\r` before it goes with it. A file with a `\\r`
    and no `\\n` is not read, and neither is a `\\r` left on a clause line."""
    if "\r" in text and "\n" not in text:
        raise Unreadable("CR-only")
    for line in text.split("\n"):
        yield (line[:-1] if line.endswith("\r") else line).strip(_C_SPACE)


def reference_read(text):
    """DIMACS as dratify documents it: `\\n` ends a line, ASCII whitespace
    separates tokens, a token is an ASCII integer, a comment runs to the `\\n`.

    Returns (clauses as written, declared variables, declared clauses).
    """
    clauses, pending = [], []
    nv = nc = None
    for line in _reference_lines(text):
        if not line or line[0] == "c":
            continue
        if line[0] == "p":
            parts = line.split()
            nv, nc = int(parts[2]), int(parts[3])
            continue
        for tok in re.split(r"[ \t\x0b\x0c]+", line):
            if not _ASCII_INT.match(tok):
                raise Unreadable(tok)
            d = int(tok)
            if d == 0:
                clauses.append(pending)
                pending = []
            else:
                pending.append(d)
    if pending:
        clauses.append(pending)
    return clauses, nv, nc


def reference_read_proof(text):
    """The same for a proof: `(kind, literals as written)`."""
    steps, pending, kind = [], [], "a"
    for line in _reference_lines(text):
        if not line or line[0] == "c":
            continue
        for tok in re.split(r"[ \t\x0b\x0c]+", line):
            if tok[0] == "d":
                kind, tok = "d", tok[1:]
                if not tok:
                    continue
            if not _ASCII_INT.match(tok):
                raise Unreadable(tok)
            d = int(tok)
            if d == 0:
                steps.append((kind, pending))
                pending, kind = [], "a"
            else:
                pending.append(d)
    return steps


# ---------------------------------------------------------------------------
# the system under test, behind a seam the self-test can replace
# ---------------------------------------------------------------------------


def as_row(r):
    if isinstance(r, Exception):
        return {"exception": type(r).__name__, "message": str(r)}
    return {f: getattr(r, f) for f in FIELDS}


class Real:
    """dratify itself, on both engines."""

    engines = ("python", "native")

    def __init__(self):
        import cdclkit_native
        register_native(cdclkit_native)

    def parse(self, text, strict=False):
        return parse_dimacs(text, strict=strict)

    def check(self, engine, formula, proof, **kw):
        return check_proof(formula, proof, engine=engine, **kw)


# ---------------------------------------------------------------------------
# generation
# ---------------------------------------------------------------------------


class Instance:
    __slots__ = ("raw", "header", "formula_text", "steps", "proof_text", "tags",
                 "fresh")

    def __init__(self, raw, header, formula_text, steps, proof_text, tags, fresh):
        self.raw = raw
        self.header = header
        self.formula_text = formula_text
        self.steps = steps
        self.proof_text = proof_text
        self.tags = tags
        self.fresh = fresh


def random_clause(rng, variables, lo=1, hi=3):
    n = min(rng.randint(lo, hi), len(variables))
    return [v if rng.random() < 0.5 else -v for v in rng.sample(variables, n)]


def gen_raw_formula(rng):
    """Clause lists shaped to give the checker root units, RAT candidates and
    refutations, then decorated with the things this corner is about."""
    nv = rng.randint(2, 7)
    variables = list(range(1, nv + 1))
    style = rng.choice(("random", "chain", "chain", "block", "block"))
    clauses = []
    if style == "chain":
        order = rng.sample(variables, nv)
        lit = order[0] if rng.random() < 0.5 else -order[0]
        if rng.random() < 0.6:
            clauses.append([lit])
        else:
            # a unit that takes propagation to find, so its reason is non-unit
            clauses.append([lit, order[-1]])
            clauses.append([-order[-1]])
        for v in order[1:rng.randint(2, nv)]:
            nxt = v if rng.random() < 0.5 else -v
            clauses.append([-lit, nxt])
            lit = nxt
    elif style == "block":
        k = rng.randint(2, min(3, nv))
        vs = rng.sample(variables, k)
        patterns = [[v if m >> i & 1 else -v for i, v in enumerate(vs)]
                    for m in range(1 << k)]
        if rng.random() < 0.3:
            patterns.pop(rng.randrange(len(patterns)))
        clauses.extend(patterns)
    for _ in range(rng.randint(0, nv)):
        clauses.append(random_clause(rng, variables))
    if rng.random() < 0.05:
        clauses.append([])

    raw = []
    for c in clauses:
        c = list(c)
        roll = rng.random()
        if c and roll < 0.2:
            for _ in range(rng.randint(1, 2)):
                c.insert(rng.randint(0, len(c)), rng.choice(c))
        elif c and roll < 0.3:
            c.insert(rng.randint(0, len(c)), -rng.choice(c))
        raw.append(c)
    rng.shuffle(raw)
    if rng.random() < 0.3:
        raw.append([rng.choice(variables)] * rng.randint(2, 3))
    return raw, nv


def spell_zero(rng, tags, where):
    roll = rng.random()
    if roll < 0.85:
        return "0"
    if roll < 0.94:
        tags[where] += 1
        return "-0"
    tags["other_zero_spelling"] += 1
    return rng.choice(("000", "00", "-00"))


def render_formula(rng, raw, nv, tags):
    """(text, header) with a truthful header, unless a variable is meant to be
    above it. A multi-clause line and a `-0` are both ordinary here."""
    roll = rng.random()
    used = max((abs(l) for c in raw for l in c), default=0)
    if roll < 0.15:
        header = None
    elif roll < 0.3 and used >= 2:
        header = (rng.randint(1, used - 1), len(raw))
        tags["formula_var_above_header"] += 1
    elif roll < 0.4:
        header = (used + rng.randint(1, 3), len(raw))
    else:
        header = (used, len(raw))
    lines = [] if header is None else [f"p cnf {header[0]} {header[1]}"]
    for c in raw:
        body = " ".join(map(str, c))
        lines.append(f"{body} {spell_zero(rng, tags, 'minus_zero_formula')}".strip())
    return "\n".join(lines) + "\n", header


def resolvents(rng, cur, tries=6):
    out = []
    for _ in range(tries):
        if len(cur) < 2:
            break
        a, b = rng.sample(cur, 2)
        pivots = [l for l in a if -l in b]
        if pivots:
            p = rng.choice(pivots)
            out.append(list(as_set([*(l for l in a if l != p),
                                    *(l for l in b if l != -p)])))
    return out


def decorate_lemma(rng, clause):
    """Repeat literals without moving any first occurrence: the pivot stays."""
    out = list(clause)
    if out and rng.random() < 0.45:
        for _ in range(rng.randint(1, 3)):
            lit = rng.choice(out)
            first = out.index(lit)
            out.insert(rng.randint(first + 1, len(out)), lit)
    return out


def decorate_deletion(rng, clause):
    """A deletion is matched as a set, so its order and repeats are free."""
    out = list(clause)
    if out and rng.random() < 0.45:
        for _ in range(rng.randint(1, 2)):
            out.insert(rng.randint(0, len(out)), rng.choice(out))
    if rng.random() < 0.5:
        rng.shuffle(out)
    return out


def gen_steps(rng, raw, nv):
    """A proof built against the oracle, so most steps are worth accepting."""
    cur = normalise(raw)
    used = max((abs(l) for c in raw for l in c), default=0)
    variables = list(range(1, max(nv, used, 1) + 1))
    fresh = max(variables) + 1
    fresh_seen = []
    steps = []

    def add(clause):
        steps.append(("a", decorate_lemma(rng, clause)))
        cur.append(list(as_set(clause)))

    def rup_candidate():
        pool = resolvents(rng, cur) + [random_clause(rng, variables)
                                       for _ in range(10)]
        rng.shuffle(pool)
        for c in pool:
            if not is_taut(c) and oracle.rup(cur, c):
                return c
        return None

    def rat_candidate():
        nonlocal fresh
        roll = rng.random()
        if roll < 0.3:
            # a definition over a fresh variable: vacuous, or nearly
            pivot = fresh if rng.random() < 0.5 else -fresh
            c = [pivot, *random_clause(rng, variables, 0, 2)]
            fresh += 1
            fresh_seen.append(abs(pivot))
            return c
        if roll < 0.55:
            root = sorted(oracle.propagate(cur)[1], key=abs)
            if root:
                return [-rng.choice(root), *random_clause(rng, variables, 0, 1)]
        for _ in range(12):
            c = random_clause(rng, variables)
            if is_taut(c) or len(set(c)) != len(c):
                continue
            if not oracle.rup(cur, c) and oracle.rat(cur, c, c[0]):
                return c
        return None

    def strand():
        """Delete a non-unit reason, then ask for the negation of what it gave."""
        conflict, root = oracle.propagate(cur)
        if conflict:
            return
        reasons = [c for c in cur if len(c) >= 2
                   and sum(1 for l in c if l in root) == 1
                   and all(l in root or -l in root for l in c)]
        if reasons:
            c = rng.choice(reasons)
            given = next(l for l in c if l in root)
            steps.append(("d", decorate_deletion(rng, c)))
            cur.remove(c)
            add([-given])

    for _ in range(rng.randint(0, 7)):
        if oracle.propagate(cur)[0]:
            break
        action = rng.choices(
            ("rup", "rat", "taut", "taut_d", "del", "del_unit", "del_absent",
             "del_fresh", "del_empty", "del_taut", "strand", "bad"),
            (30, 25, 8, 4, 16, 6, 4, 2, 2, 3, 6, 4))[0]
        if action == "rup":
            c = rup_candidate()
            if c is not None:
                add(c)
        elif action == "rat":
            c = rat_candidate()
            if c is not None:
                add(c)
        elif action == "taut":
            lit = rng.choice(variables)
            c = [lit, -lit, *random_clause(rng, variables, 0, 1)]
            rng.shuffle(c)
            add(c)
        elif action == "taut_d":
            # (p -p) on the multiset blocks a later RAT on p, by the definition
            lit = rng.choice(variables)
            add([-lit, lit])
            steps.append(("a", [lit]))
            cur.append([lit])
        elif action == "del":
            live = [c for c in cur if len(c) >= 2]
            if live:
                c = rng.choice(live)
                steps.append(("d", decorate_deletion(rng, c)))
                cur.remove(c)
        elif action == "del_unit":
            units = [c for c in cur if len(c) == 1]
            if units:
                # ignored, so it stays in `cur`
                c = rng.choice(units)
                steps.append(("d", c * rng.randint(1, 3)))
        elif action == "del_absent":
            c = random_clause(rng, variables, 2, 3)
            if not any(set(d) == set(c) for d in cur):
                steps.append(("d", c))
        elif action == "del_fresh":
            steps.append(("d", [fresh, *random_clause(rng, variables, 1, 2)]))
            fresh += 1
        elif action == "del_empty":
            steps.append(("d", []))
        elif action == "del_taut":
            # a tautology in the input was dropped, so this usually finds nothing
            lit = rng.choice(variables)
            c = [lit, -lit]
            steps.append(("d", c))
            for d in cur:
                if set(d) == set(c):
                    cur.remove(d)
                    break
        elif action == "strand":
            strand()
        elif action == "bad":
            for _ in range(10):
                c = random_clause(rng, variables)
                if not is_taut(c) and not oracle.rup(cur, c) \
                        and not oracle.rat(cur, c, c[0]):
                    steps.append(("a", decorate_lemma(rng, c)))
                    return steps, fresh_seen
    # finish with a refutation when one is near
    for _ in range(4):
        if oracle.rup(cur, ()):
            break
        units = [[s * v] for v in variables for s in (1, -1)
                 if oracle.rup(cur, [s * v])]
        if not units:
            break
        add(rng.choice(units))
    if oracle.rup(cur, ()) or rng.random() < 0.5:
        steps.append(("a", []))
    return steps, fresh_seen


def render_proof(rng, steps, tags):
    out = []
    for kind, lits in steps:
        body = " ".join(map(str, lits))
        zero = spell_zero(rng, tags, "minus_zero_proof")
        text = f"{body} {zero}".strip()
        if kind == "d":
            text = f"d{text}" if lits and rng.random() < 0.1 else f"d {text}"
        out.append(text)
    # whitespace is not a line structure, and two clauses may share a line
    sep = " " if rng.random() < 0.1 else "\n"
    return sep.join(out) + ("\n" if out else "")


def make_instance(rng):
    tags = collections.Counter()
    raw, nv = gen_raw_formula(rng)
    text, header = render_formula(rng, raw, nv, tags)
    steps, fresh = gen_steps(rng, raw, nv)
    return Instance(raw, header, text, steps, render_proof(rng, steps, tags),
                    tags, fresh)


# ---------------------------------------------------------------------------
# the harness
# ---------------------------------------------------------------------------


class Harness:
    def __init__(self, sut, rng):
        self.sut = sut
        self.rng = rng
        self.counts = collections.Counter()
        self.mismatches = collections.Counter()
        self.witness = {}
        self.steps_judged = 0

    # -- reporting ---------------------------------------------------------

    def flag(self, label, **detail):
        self.mismatches[label] += 1
        size = len(repr(detail))
        if label not in self.witness or size < self.witness[label][0]:
            self.witness[label] = (size, detail)

    # -- running -----------------------------------------------------------

    def run_engine(self, engine, formula, proof, **kw):
        try:
            return self.sut.check(engine, formula, proof, **kw)
        except Exception as e:     # a verdict is expected; the caller judges this
            return e

    def run_engines(self, formula, proof, ftext, **kw):
        """Both engines, every field; a disagreement is always a finding."""
        out = {e: self.run_engine(e, formula, proof, **kw)
               for e in self.sut.engines}
        rows = [as_row(r) for r in out.values()]
        self.counts["engines_compared"] += 1
        if len(rows) == 2 and rows[0] != rows[1]:
            diff = {k for k in {*rows[0], *rows[1]}
                    if rows[0].get(k) != rows[1].get(k)}
            if diff == {"failed_clause"} and self._only_repeats(*rows):
                self.flag("failed-clause-repeats", formula=ftext, proof=proof,
                          rows=rows)
            else:
                self.flag("engine-disagreement", formula=ftext, proof=proof,
                          rows=rows, kw=kw)
        return out

    @staticmethod
    def _only_repeats(a, b):
        fa, fb = a["failed_clause"], b["failed_clause"]
        return fa is not None and fb is not None and as_set(fa) == as_set(fb)

    # -- the formula -------------------------------------------------------

    def judge_parse(self, inst):
        """The parser against the documented normalisation."""
        try:
            f = self.sut.parse(inst.formula_text)
        except Exception as e:
            self.flag("parse-mismatch", formula=inst.formula_text, error=str(e))
            return None
        got = [[to_dimacs(l) for l in c] for c in f.clauses]
        want = normalise(inst.raw)
        if got != want:
            self.flag("parse-mismatch", formula=inst.formula_text, got=got,
                      want=want)
            return None
        seen = [l for c in inst.raw for l in c]
        declared = inst.header[0] if inst.header else 0
        expected_nvars = max([declared, *(abs(l) for l in seen)])
        if f.nvars != expected_nvars:
            if any(is_taut(c) for c in inst.raw):
                self.flag("nvars-tautology", formula=inst.formula_text,
                          got=f.nvars, want=expected_nvars)
            else:
                self.flag("parse-mismatch", formula=inst.formula_text,
                          got_nvars=f.nvars, want=expected_nvars)
        elif inst.header:
            clean = (inst.header[0] == f.nvars and inst.header[1] == len(inst.raw))
            if clean != (f.header_mismatch is None):
                self.flag("parse-mismatch", formula=inst.formula_text,
                          header_mismatch=f.header_mismatch, clean=clean)
            self.counts["header_clean" if clean else "header_mismatch_reported"] += 1
            try:
                self.sut.parse(inst.formula_text, strict=True)
                if not clean:
                    self.flag("parse-mismatch", formula=inst.formula_text,
                              strict="accepted a mismatch")
            except ValueError:
                if clean:
                    self.flag("parse-mismatch", formula=inst.formula_text,
                              strict="refused a clean file")
        for key, hit in (
            ("formula_repeated_literal",
             any(len(set(c)) != len(c) for c in inst.raw)),
            ("formula_unit_by_repeat",
             any(len(set(c)) == 1 and len(c) > 1 for c in inst.raw)),
            ("formula_tautology_dropped", any(is_taut(c) for c in inst.raw)),
            ("formula_empty_clause", any(not c for c in inst.raw)),
        ):
            self.counts[key] += hit
        return f

    # -- the proof ---------------------------------------------------------

    def walk(self, F0, steps, check_rat, apply_deletions):
        """What the oracle says of each step, with every addition kept so a
        checker can be followed past the point it should have stopped."""
        rows = []
        if any(not c for c in F0) or oracle.propagate(F0)[0]:
            return rows, True
        cur = [list(c) for c in F0]
        for index, (kind, lits) in enumerate(steps, 1):
            distinct = as_set(lits)
            if kind == "d":
                row = dict(index=index, kind="d", lits=lits, distinct=distinct,
                           applied=False, present=False, cur=cur, ignored=False)
                if len(distinct) <= 1:
                    row["ignored"] = True
                elif apply_deletions:
                    [st], cur = oracle.replay(cur, [("d", lits)], "operational",
                                              stop_at_unacceptable=False)
                    row["applied"], row["present"] = st.applied, st.present
                    row["ignored"] = not st.applied
                rows.append(row)
                continue
            [st], next_cur = oracle.replay(cur, [("a", lits)], "operational",
                                           stop_at_unacceptable=False)
            acceptable = bool(st.rup) or (check_rat and bool(st.rat_on_first))
            rows.append(dict(index=index, kind="a", lits=lits, distinct=distinct,
                             step=st, acceptable=acceptable, cur=cur))
            cur = next_cur
            if not lits and acceptable:
                break
        return rows, False

    def expected(self, rows):
        e = dict(ok=False, steps=0, rup_steps=0, rat_steps=0, deletions=0,
                 ignored_deletions=0, failed_step=-1, failed_clause=None,
                 reached_empty=False)
        lo = hi = 0                # resolvents_checked may stop early on a failure
        for row in rows:
            e["steps"] += 1
            if row["kind"] == "d":
                e["deletions"] += row["applied"]
                e["ignored_deletions"] += row["ignored"]
                continue
            st = row["step"]
            total = self._resolvents(row)
            if st.rup:
                e["rup_steps"] += 1
            elif row["acceptable"]:
                e["rat_steps"] += 1
                lo += total
                hi += total
            else:
                e["failed_step"] = row["index"]
                e["failed_clause"] = tuple(row["lits"])
                hi += total
                break
            if not row["lits"]:
                e["reached_empty"] = e["ok"] = True
                break
        return e, lo, hi

    @staticmethod
    def _resolvents(row):
        """How many resolvents RAT has to look at for this step."""
        d = row["distinct"]
        if not d:
            return 0
        clause = set(d)
        n = 0
        for c in row["cur"]:
            if -d[0] in c and not any(-l in clause for l in c if l != -d[0]):
                n += 1
        return n

    def judge_result(self, inst, F0, result, engine, kw, rows, refuted_at_start):
        ctx = dict(formula=inst.formula_text, proof=inst.proof_text, engine=engine, **kw)
        if isinstance(result, Exception):
            msg = str(result)
            if isinstance(result, ValueError) and "can account for at most" in msg:
                self.flag("bound-refuses-valid", error=msg, **ctx)
            else:
                self.flag("unexpected-exception", error=repr(result), **ctx)
            return
        a = result
        if a.ok and not a.reached_empty:
            self.flag("ok-without-empty", **ctx)

        # the end-to-end question, before anything else
        if a.ok and oracle.satisfiable(inst.raw):
            self.flag("sat-accepted", **ctx)

        if refuted_at_start:
            if not a.ok or not a.reached_empty or a.steps != 0:
                self.flag("field-mismatch", want="refuted by unit propagation",
                          got=as_row(a), **ctx)
            return

        # step by step: nothing RUP or RAT is rejected, nothing else accepted
        for row in rows:
            if row["index"] > a.steps:
                break
            if row["kind"] != "a":
                continue
            if a.failed_step == row["index"]:
                if row["acceptable"]:
                    self.flag("rejects-acceptable", step=row["index"], **ctx)
                break
            if not row["acceptable"]:
                self.flag("accepts-unacceptable", step=row["index"], **ctx)

        want, lo, hi = self.expected(rows)
        got = {k: getattr(a, k) for k in want}
        if got["failed_clause"] is not None:
            # which clause it was, as DIMACS, and as the proof wrote it
            got["failed_clause"] = tuple(to_dimacs(l) for l in got["failed_clause"])
        if got != want:
            self.flag("field-mismatch", got=got, want=want, **ctx)
        if not lo <= a.resolvents_checked <= hi:
            self.flag("field-mismatch", resolvents=a.resolvents_checked,
                      want=(lo, hi), **ctx)

    def count_steps(self, inst, a, rows):
        """Counts only what the checker actually reached."""
        formula_vars = {abs(l) for c in inst.raw for l in c}
        input_taut = {frozenset(c) for c in inst.raw if is_taut(c)}
        seen = set(formula_vars)
        c = self.counts
        for row in rows:
            if row["index"] > a.steps:
                break
            self.steps_judged += 1
            lits, distinct = row["lits"], row["distinct"]
            vs = {abs(l) for l in lits}
            repeated = len(lits) != len(distinct)
            if row["kind"] == "d":
                if not lits:
                    c["del_empty_clause"] += 1
                if vs - seen:
                    c["del_fresh_var"] += 1
                if len(distinct) == 1:
                    c["del_unit_by_repeat_ignored" if repeated else "del_unit_ignored"] += 1
                elif row["applied"]:
                    if repeated:
                        c["del_repeat_applied"] += 1
                    if is_taut(distinct):
                        c["del_tautological_lemma_applied"] += 1
                    if list(distinct) not in row["cur"]:
                        c["del_shuffled_applied"] += 1
                elif row["present"]:
                    c["del_reason_ignored"] += 1
                elif len(distinct) > 1:
                    c["del_absent"] += 1
                    if frozenset(distinct) in input_taut:
                        c["del_formula_tautology_absent"] += 1
                continue
            if a.failed_step == row["index"]:
                c["rejected_steps"] += 1
                if repeated:
                    c["lemma_repeat_rejected"] += 1
                if distinct and any(-distinct[0] in d and distinct[0] in d
                                    for d in row["cur"]):
                    c["rat_blocked_by_tautological_d"] += 1
                break
            st = row["step"]
            by_rup = bool(st.rup)
            if not by_rup and distinct:
                c["rat_accepted"] += 1
                if distinct and lits.count(distinct[0]) > 1:
                    c["lemma_pivot_repeated_rat"] += 1
                clause = set(distinct)
                if any(-distinct[0] in d
                       and any(-l in clause for l in d if l != -distinct[0])
                       for d in row["cur"]):
                    c["rat_tautological_resolvent_skipped"] += 1
            if repeated:
                c["lemma_repeat_rup" if by_rup else "lemma_repeat_rat"] += 1
            if repeated and len(distinct) == 1:
                c["lemma_unit_by_repeat"] += 1
            if is_taut(distinct):
                c["lemma_complementary_accepted"] += 1
            if vs - seen:
                c["fresh_var_rup" if by_rup else "fresh_var_rat"] += 1
            seen |= vs

    # -- families ----------------------------------------------------------

    def family_proofs(self):
        inst = make_instance(self.rng)
        self.counts.update(inst.tags)
        f = self.judge_parse(inst)
        if f is None:
            return
        F0 = normalise(inst.raw)
        self.counts["formula_refuted_by_up"] += bool(
            any(not c for c in F0) or oracle.propagate(F0)[0])
        steps = [(k, list(l)) for k, l in inst.steps]
        self.judge_config(inst, f, F0, steps, {})
        roll = self.rng.random()
        if roll < 0.12:
            self.counts["variant_no_rat"] += 1
            self.judge_config(inst, f, F0, steps, {"check_rat": False})
        elif roll < 0.24:
            self.counts["variant_no_deletions"] += 1
            self.judge_config(inst, f, F0, steps, {"apply_deletions": False})
        elif roll < 0.4:
            self.judge_list_form(inst, f)
        elif roll < 0.5:
            self.judge_roundtrip(inst, f)

    def judge_config(self, inst, f, F0, steps, kw):
        results = self.run_engines(f, inst.proof_text, inst.formula_text, **kw)
        rows, refuted = self.walk(F0, steps, kw.get("check_rat", True),
                                  kw.get("apply_deletions", True))
        for engine, res in results.items():
            self.judge_result(inst, F0, res, engine, kw, rows, refuted)
        first = next(iter(results.values()))
        if not isinstance(first, Exception):
            if kw:
                self.steps_judged += sum(r["index"] <= first.steps for r in rows)
            else:
                self.count_steps(inst, first, rows)
                if first.ok and not oracle.satisfiable(inst.raw):
                    self.counts["ok_true_unsat"] += 1
                elif not first.ok and first.failed_step > 0:
                    self.counts["ok_false_rejected"] += 1
                elif not first.ok:
                    self.counts["ok_false_no_empty"] += 1

    def judge_list_form(self, inst, f):
        """The same proof as a list of steps must give the same answer."""
        steps = parse_proof(inst.proof_text)
        self.counts["list_form_compared"] += 1
        for engine in self.sut.engines:
            text = self.run_engine(engine, f, inst.proof_text)
            shape = self.run_engine(engine, f, steps)
            if as_row(text) != as_row(shape):
                if isinstance(shape, ValueError) and "at most" in str(shape):
                    self.flag("bound-refuses-valid", formula=inst.formula_text,
                              proof=inst.proof_text, engine=engine,
                              list_form=str(shape))
                else:
                    self.flag("field-mismatch", list_form=as_row(shape),
                              text=as_row(text), formula=inst.formula_text,
                              proof=inst.proof_text)

    def judge_roundtrip(self, inst, f):
        self.counts["roundtrip"] += 1
        again = self.sut.parse(f.to_dimacs())
        if again.clauses != f.clauses or again.nvars != f.nvars:
            self.flag("parse-mismatch", roundtrip=f.to_dimacs(),
                      formula=inst.formula_text)

    def family_bound(self):
        """Fresh variables with a gap, just past the documented bound, and far past.

        A fresh variable's number means nothing, so the oracle's verdict does not
        move with it; only the guard can, and the guard reads only the formula and
        the steps. Past it, refusing is what tests/test_untrusted_input.py asks.
        A comment must not change either answer. The exact limit allocates a
        million variables, so it is run once, in `family_floor`.
        """
        rng = self.rng
        nv = rng.randint(1, 4)
        raw = [random_clause(rng, list(range(1, nv + 1)), 1, 2)
               for _ in range(rng.randint(1, 4))]
        ftext = f"p cnf {nv} {len(raw)}\n" + "".join(
            " ".join(map(str, c)) + " 0\n" for c in raw)
        f = self.sut.parse(ftext)
        pad = "c " + "x" * rng.randint(0, 40) + "\n" if rng.random() < 0.5 else ""

        sign = 1 if rng.random() < 0.5 else -1

        def proof(v):
            return f"{pad}{sign * v} 0\n"

        gap = f.nvars + rng.randint(1, 3000)
        above = f.nvars + HEADER_VARS_FLOOR + 1
        huge = above + 1 + rng.randint(0, 1000)
        F0 = normalise(raw)
        refuted = oracle.propagate(F0)[0]

        for var, where in ((gap, "gap"), (above, "above"), (huge, "huge")):
            text = proof(var)
            if not oracle.rat(F0, [sign * var], sign * var):
                self.flag("generator-error", formula=ftext, proof=text)
            results = self.run_engines(f, text, ftext)
            for engine, res in results.items():
                raised = isinstance(res, ValueError) and "at most" in str(res)
                if where == "gap":
                    if raised:
                        self.flag("bound-refuses-valid", formula=ftext, proof=text,
                                  engine=engine, error=str(res))
                    elif isinstance(res, Exception):
                        self.flag("unexpected-exception", error=repr(res),
                                  formula=ftext, proof=text)
                    elif (res.ok, res.rat_steps, res.failed_step) != (
                            (True, 0, -1) if refuted else (False, 1, -1)):
                        self.flag("rejects-acceptable", formula=ftext, proof=text,
                                  engine=engine)
                    else:
                        self.counts["bound_with_a_gap_accepted"] += 1
                elif raised:
                    self.counts["bound_above_limit_refused" if where == "above"
                                else "bound_huge_refused"] += 1
                else:
                    self.flag("huge-literal-not-refused", formula=ftext,
                              proof=text, engine=engine, got=as_row(res))
            self.steps_judged += 1
            # the same number after a comment longer than it: the guard must not read it
            if where == "above":
                padded = "c " + "x" * (var + 2) + "\n" + text
                res = self.run_engine(self.sut.engines[0], f, padded)
                if isinstance(res, ValueError) and "at most" in str(res):
                    self.counts["bound_padded_still_refused"] += 1
                else:
                    self.flag("bound-reads-the-layout", formula=ftext, got=as_row(res))

    def family_tokens(self):
        rng = self.rng
        kind = rng.choice(("ok", "lenient", "bad"))
        if kind == "ok":
            tok, val = rng.choice((("1", 1), ("01", 1), ("-01", -1), ("02", 2),
                                   ("-2", -2)))
            ftext = f"p cnf 2 1\n{tok} 0\n"
            ptext = f"{tok} 0\n"
            got = [[to_dimacs(l) for l in c] for c in self.sut.parse(ftext).clauses]
            if got != [[val]] or \
                    [to_dimacs(l) for l in parse_proof(ptext)[0][1]] != [val]:
                self.flag("parse-mismatch", token=tok, got=got)
            self.counts["token_leading_zero"] += 1
        elif kind == "lenient":
            tok = rng.choice(("1_0", "1_1", "٣", "１", "١٢",
                              "1\xa02", "2 1"))
            self.counts["token_lenient"] += 1
            for name, fn in (("parse_dimacs", self.sut.parse), ("parse_proof", parse_proof)):
                try:
                    reference_read(f"{tok} 0\n")
                except Unreadable:
                    try:
                        fn(f"{tok} 0\n")
                    except ValueError:
                        pass
                    else:
                        self.flag("token-lenient", token=tok, reader=name)
        else:
            tok = rng.choice(("--1", "- 1", "+-1", "1.0", "0x1", "1e1", "1-", "x",
                              "+1", "+0"))
            for name, fn in (("parse_dimacs", self.sut.parse), ("parse_proof", parse_proof)):
                try:
                    fn(f"{tok} 0\n")
                except ValueError:
                    self.counts["token_bad_refused"] += 1
                else:
                    self.flag("bad-token-accepted", token=tok, reader=name)
        self.family_comment()

    def family_comment(self):
        """A DIMACS comment ends at a newline. Text after a form feed is still
        comment to every C reader, and a clause to `str.splitlines`."""
        rng = self.rng
        sep = rng.choice(("\x0b", "\x0c", "\r", "\x1c", "\x1d", "\x1e", "\x85",
                          " ", " "))
        v = rng.randint(1, 3)
        # (v) with (-v) hidden in a comment: satisfiable as written
        count = rng.choice((1, 2))
        ftext = f"p cnf 3 {count}\n{v} 0\nc note{sep}-{v} 0\n"
        clauses, _, _ = reference_read(ftext)
        self.counts["comment_formula"] += 1
        f = self.sut.parse(ftext)
        got = [[to_dimacs(l) for l in c] for c in f.clauses]
        want = normalise(clauses)
        if got != want:
            results = self.run_engines(f, "0\n", ftext)
            first = next(iter(results.values()))
            refuted = not isinstance(first, Exception) and first.ok
            sat_refuted = refuted and oracle.satisfiable(clauses)
            self.counts["comment_refuted_satisfiable"] += sat_refuted
            self.flag("comment-split", formula=ftext, got=got, want=want,
                      ok_on_satisfiable=sat_refuted,
                      header_mismatch=f.header_mismatch)
        # and the same in a proof: a comment that runs a step
        ptext = f"c note{sep}{v} 0\n"
        self.counts["comment_proof"] += 1
        want_steps = reference_read_proof(ptext)
        got_steps = [[to_dimacs(l) for l in s] for _, s in parse_proof(ptext)]
        if got_steps != [s for _, s in want_steps]:
            self.flag("comment-split", proof=ptext, got=got_steps,
                      want=[s for _, s in want_steps])

    def family_surfaces(self):
        """The ways in that do not go through the parser."""
        rng = self.rng
        roll = rng.random()
        if roll < 0.15:
            self.surface_add()
        elif roll < 0.55:
            self.surface_negative_formula()
        elif roll < 0.85:
            self.surface_repeat_formula()
        else:
            self.surface_checker_step()

    def surface_add(self):
        rng = self.rng
        f = CNF(3)
        body = [rng.randint(0, 5) for _ in range(rng.randint(1, 4))]
        kept = f.add(body)
        ints = [to_dimacs(l) for l in body]
        if kept != (not is_taut(ints)) or \
                (kept and [to_dimacs(l) for l in f.clauses[0]] != list(as_set(ints))):
            self.flag("parse-mismatch", add=body, got=f.clauses, kept=kept)
        self.counts["surface_add_normalises"] += 1
        try:
            f.add([-rng.randint(1, 9)])
        except ValueError:
            self.counts["surface_add_negative_refused"] += 1
        else:
            self.flag("parse-mismatch", add="negative literal accepted")
        try:
            CNF().add_dimacs([0])
        except ValueError:
            pass
        else:
            self.flag("parse-mismatch", add_dimacs="0 accepted as a literal")

    def surface_negative_formula(self):
        """DIMACS integers placed on `CNF.clauses`: AGENTS.md's commonest mistake."""
        rng = self.rng
        n = rng.randint(2, 4)
        vs = list(range(1, n + 1))
        raw = [[-v] for v in vs]
        # a satisfiable formula read as DIMACS; positive to size the arrays
        raw.append([n + 1])
        rng.shuffle(raw)
        f = CNF(n + 1)
        f.clauses = [tuple(c) for c in raw]
        self.counts["surface_negative_formula"] += 1
        res = {e: self.run_engine(e, f, "0\n") for e in self.sut.engines}
        for engine, r in res.items():
            if not isinstance(r, ValueError):
                self.flag("unvalidated-surface", clauses=raw, engine=engine,
                          got=as_row(r), satisfiable_as_dimacs=oracle.satisfiable(raw))
        rows = [as_row(r) for r in res.values()]
        if len(rows) == 2 and rows[0] != rows[1]:
            self.flag("unvalidated-surface", clauses=raw, rows=rows)

    def surface_repeat_formula(self):
        """A repeated literal placed on `CNF.clauses`; `CNF.add` would collapse it."""
        rng = self.rng
        v = rng.randint(1, 3)
        raw = [[v, v], [-v, -v]]
        f = CNF(3)
        f.clauses = [tuple((abs(l) - 1) * 2 + (l < 0) for l in c) for c in raw]
        self.counts["surface_repeat_formula"] += 1
        for engine in self.sut.engines:
            r = self.run_engine(engine, f, "0\n")
            if isinstance(r, Exception) or not r.ok:
                # unsatisfiable by unit propagation once a clause is a set
                self.flag("repeat-surface", clauses=raw, engine=engine,
                          got=as_row(r))

    def surface_checker_step(self):
        """`DRATChecker` is exported, and `check_proof` holds the only validation."""
        f = CNF(0)
        f.add_dimacs([1, 2])
        f.add_dimacs([-2, 3])
        self.counts["surface_checker_negative_step"] += 1
        for name, drive in (("check", lambda c: c.check([("a", (-5,)), ("a", ())])),
                            ("check_step", lambda c: c.check_step("a", (-5,)))):
            try:
                drive(DRATChecker(f))
            except ValueError:
                continue
            except Exception as e:
                self.flag("unvalidated-surface", direct=name, error=repr(e))
            else:
                self.flag("unvalidated-surface", direct=name,
                          satisfiable=oracle.satisfiable([[1, 2], [-2, 3]]))

    def family_floor(self):
        """The formula's bound, once a run: it allocates."""
        floor = HEADER_VARS_FLOOR
        f = self.sut.parse(f"1 {floor} 0\n")
        if f.nvars != floor:
            self.flag("parse-mismatch", floor=f.nvars)
        else:
            self.counts["formula_floor_accepted"] += 1
        for text in (f"1 {floor + 1} 0\n", f"-{floor + 1} 0\n"):
            try:
                self.sut.parse(text)
            except ValueError:
                self.counts["formula_floor_plus_one_refused"] += 1
            else:
                self.flag("parse-mismatch", above_floor=text)
        # at the floor both engines still answer, and agree
        self.run_engines(f, "-1 0\n", f"1 {floor} 0\n")
        # the proof bound exactly, on both engines: a million variables each
        small = self.sut.parse("p cnf 2 1\n1 2 0\n")
        at = small.nvars + floor
        res = self.run_engines(small, f"{at} 0\n", "p cnf 2 1\n1 2 0\n")
        for engine, r in res.items():
            if isinstance(r, Exception) or r.rat_steps != 1:
                self.flag("bound-refuses-valid", at_limit=at, engine=engine,
                          got=as_row(r))
            else:
                self.counts["bound_at_limit_accepted"] += 1
        # a CNF past u32: the checkers size by what is used, so it is one answer
        huge = CNF(1 << 32)
        huge.add_dimacs([1])
        res = {e: self.run_engine(e, huge, "") for e in self.sut.engines}
        rows = [as_row(r) for r in res.values()]
        if len(rows) == 2 and rows[0] != rows[1]:
            self.flag("unvalidated-surface", nvars=1 << 32, rows=rows)

    # -- a run -------------------------------------------------------------

    def run(self, instances, families=None):
        started = time.perf_counter()
        table = families or ((self.family_proofs, 80), (self.family_bound, 8),
                             (self.family_tokens, 6), (self.family_surfaces, 6))
        fns, weights = zip(*table)
        if families is None:
            self.family_floor()
        for _ in range(instances):
            self.rng.choices(fns, weights)[0]()
        return time.perf_counter() - started


# ---------------------------------------------------------------------------
# self-test: the harness against checkers known to be wrong
# ---------------------------------------------------------------------------


def stub_result(**kw):
    r = CheckResult()
    for k, v in kw.items():
        setattr(r, k, v)
    return r


class AcceptAll(Real):
    engines = ("python",)

    def check(self, engine, formula, proof, **kw):
        return stub_result(ok=True, reached_empty=True, reason="stub",
                           steps=len(parse_proof(proof)))


class RejectAll(Real):
    engines = ("python",)

    def check(self, engine, formula, proof, **kw):
        return stub_result(ok=False, reason="stub", steps=1, failed_step=1,
                           failed_clause=())


class CountsOccurrences(Real):
    """The 0.1.8 mistake: a clause as a list of occurrences, in a tiny checker."""

    engines = ("python",)

    def check(self, engine, formula, proof, check_rat=True, apply_deletions=True):
        clauses = [list(c) for c in formula.clauses]
        r = stub_result(reason="stub")
        if any(not c for c in clauses) or self._rup(clauses, []):
            return stub_result(ok=True, reached_empty=True, reason="stub")
        for kind, lits in parse_proof(proof):
            r.steps += 1
            lits = list(lits)
            if kind == "d":
                if len(lits) <= 1:
                    r.ignored_deletions += 1
                elif apply_deletions and sorted(lits) in map(sorted, clauses):
                    clauses.remove(next(c for c in clauses if sorted(c) == sorted(lits)))
                    r.deletions += 1
                else:
                    r.ignored_deletions += 1
                continue
            if self._rup(clauses, lits):
                r.rup_steps += 1
            elif check_rat and lits and self._rat(clauses, lits):
                r.rat_steps += 1
            else:
                r.failed_step, r.failed_clause = r.steps, tuple(lits)
                return r
            if not lits:
                r.ok = r.reached_empty = True
                return r
            clauses.append(lits)
        return r

    @staticmethod
    def _rup(clauses, lits):
        value = {l ^ 1: True for l in lits}
        if any(l in value and l ^ 1 in value for l in value):
            return True
        changed = True
        while changed:
            changed = False
            for c in clauses:
                if any(value.get(l) for l in c):
                    continue
                free = [l for l in c if not value.get(l ^ 1)]
                if not free:
                    return True
                if len(free) == 1:       # occurrences: `x x` has two
                    value[free[0]] = True
                    changed = True
        return False

    def _rat(self, clauses, lits):
        pivot = lits[0]
        for c in clauses:
            if pivot ^ 1 in c:
                res = lits + [l for l in c if l != pivot ^ 1 and l not in lits]
                if not self._rup(clauses, res):
                    return False
        return True


class NativeOffByOne(Real):
    """Two engines that differ on one counter."""

    def check(self, engine, formula, proof, **kw):
        r = check_proof(formula, proof, engine="python", **kw)
        if engine == "native":
            r.rup_steps += 1
        return r


class KeepsTautologies(Real):
    engines = ("python",)

    def parse(self, text, strict=False):
        f = CNF()
        for c in reference_read(text)[0]:
            f.clauses.append(tuple((abs(l) - 1) * 2 + (l < 0) for l in c))
        return f

    def check(self, engine, formula, proof, **kw):
        return check_proof(formula, proof, engine="python", **kw)


class MinusZeroIsALiteral(Real):
    """A parser for which `-0` is not a terminator."""

    engines = ("python",)

    def parse(self, text, strict=False):
        if re.search(r"(^|\s)-0+(\s|$)", text):
            raise ValueError("bad literal -0")
        return parse_dimacs(text, strict=strict)

    def check(self, engine, formula, proof, **kw):
        return check_proof(formula, proof, engine="python", **kw)


class LengthOnlyDeletion(Real):
    """The old rule, which refuted satisfiable formulas: length alone spares a clause."""

    engines = ("python",)

    def check(self, engine, formula, proof, **kw):
        with mock.patch.object(DRATChecker, "_unit_at_root", lambda self, lits: False):
            return check_proof(formula, proof, engine="python", **kw)


class NoBound(Real):
    """A checker with no bound on a literal: answers instead of refusing."""

    engines = ("python",)

    def check(self, engine, formula, proof, **kw):
        return stub_result(ok=False, reason="stub", rat_steps=1, steps=1)


def self_test():
    """Each stub must be caught, and by a label no open finding can supply."""
    failures = []

    def expect(name, sut, labels, instances=400, families=None):
        h = Harness(sut, random.Random(11))
        fam = None
        if families:
            fam = [(getattr(h, families), 1)]
        else:
            fam = [(h.family_proofs, 1)]
        h.run(instances, fam)
        caught = {k: h.mismatches[k] for k in labels if h.mismatches[k]}
        print(f"self-test {name}: {'caught' if caught else 'MISSED'} {caught}")
        if not caught:
            failures.append(name)

    expect("accepts everything", AcceptAll(), ["sat-accepted", "accepts-unacceptable"])
    expect("rejects everything", RejectAll(), ["rejects-acceptable"])
    expect("counts occurrences (0.1.8)", CountsOccurrences(),
           ["rejects-acceptable", "field-mismatch"])
    expect("engines differ on one counter", NativeOffByOne(), ["engine-disagreement"])
    expect("parser keeps tautologies", KeepsTautologies(), ["parse-mismatch"])
    expect("parser refuses -0", MinusZeroIsALiteral(), ["parse-mismatch"])
    expect("spares clauses by length alone", LengthOnlyDeletion(),
           ["sat-accepted", "accepts-unacceptable", "field-mismatch"], instances=1500)
    expect("no bound on a literal", NoBound(), ["huge-literal-not-refused"],
           instances=30, families="family_bound")

    # the zero guard: a short run cannot pass by reaching nothing
    h = Harness(Real(), random.Random(11))
    h.run(1, [(h.family_proofs, 1)])
    missing = [c for c in CATEGORIES if not h.counts[c]]
    print(f"self-test zero guard: {len(missing)} of {len(CATEGORIES)} categories "
          f"at zero after one instance, so a run that short fails")
    if not missing:
        failures.append("zero guard")

    if failures:
        print("SELF-TEST FAILED:", ", ".join(failures))
        return 1
    print("self-test passed: every stub was flagged")
    return 0


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--seed", type=int, default=None,
                    help=f"one seed; the default is {DEFAULT_SEEDS}")
    ap.add_argument("--instances", type=int, default=DEFAULT_INSTANCES,
                    help="instances per seed")
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--no-write", action="store_true",
                    help="do not write campaign/results/literals.json")
    args = ap.parse_args(argv)
    if args.self_test:
        return self_test()

    seeds = [args.seed] if args.seed is not None else list(DEFAULT_SEEDS)
    h = Harness(Real(), None)
    runtime = 0.0
    for seed in seeds:
        h.rng = random.Random(seed)
        runtime += h.run(args.instances)
    total = args.instances * len(seeds)
    missing = [c for c in CATEGORIES if not h.counts[c]]
    unexplained = {k: v for k, v in h.mismatches.items() if k not in KNOWN}

    print(f"seeds {seeds}, {total} instances, {h.steps_judged} steps "
          f"judged, {runtime:.1f}s")
    print("categories:", json.dumps({c: h.counts[c] for c in CATEGORIES}))
    for label, n in sorted(h.mismatches.items()):
        tag = KNOWN[label][0] if label in KNOWN else "UNEXPLAINED"
        print(f"MISMATCH {label} [{tag}] x{n}")
        print("  smallest:", json.dumps(h.witness[label][1], default=str,
                                        ensure_ascii=True)[:600])
    if missing:
        print("CATEGORIES AT ZERO:", ", ".join(missing))

    if not args.no_write:
        seen = {}
        for label in h.mismatches:
            if label in KNOWN:
                fid, severity, summary = KNOWN[label]
                seen.setdefault(fid, dict(id=fid, severity=severity, summary=summary,
                                          occurrences=0))
                seen[fid]["occurrences"] += h.mismatches[label]
        RESULTS.parent.mkdir(exist_ok=True)
        RESULTS.write_text(json.dumps(dict(
            corner="literals",
            seeds=seeds,
            instances=total,
            steps=h.steps_judged,
            per_category_counts={c: h.counts[c] for c in CATEGORIES},
            mismatch_counts=dict(sorted(h.mismatches.items())),
            runtime_seconds=round(runtime, 1),
            findings=[seen[k] for k in sorted(seen)],
            fixed=sorted(set(FIXED.values())),
            not_checked=NOT_CHECKED,
        ), indent=2) + "\n")

    if unexplained:
        print("FAILED: unexplained mismatches:", sorted(unexplained))
    if h.mismatches or missing:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
