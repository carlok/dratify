# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""A generator aimed at deletion: what happens to clauses, and to what they implied.

    python -m campaign.gen_deletion                  # the reported run
    python -m campaign.gen_deletion --seed 7 --instances 500
    python -m campaign.gen_deletion --self-test

Aimed at: unit and reason clauses, clauses not present, multiset semantics
(added twice, deleted once), delete then re-add, and deletions whose literals
are reordered or repeated. Every family runs on both engines and in all four
combinations of ``check_rat`` and ``apply_deletions``.

What counts as right comes from ``campaign.oracle`` and from what dratify
documents, which is the oracle's ``length-one`` reading: "Deletion lines are
honoured, with the one exception that deletions of unit clauses are ignored".
The walk below keeps that multiset, ``M``, and judges each step against it.

The walk also keeps ``S``, every literal top-level propagation has ever
derived, because dratify never retracts its root assignment. ``S`` is used to
*label* a mismatch as a known finding, never to excuse one: known findings
remain mismatches and the run exits non-zero until they are fixed.
"""

from __future__ import annotations

import argparse
import collections
import json
import random
import sys
import time
from dataclasses import dataclass
from pathlib import Path

from campaign import oracle
from dratify import CheckResult, MemoryProof, check_proof, parse_dimacs, register_native
from dratify.lits import from_dimacs, to_dimacs

FIELDS = ("ok", "reason", "steps", "rup_steps", "rat_steps", "deletions",
          "ignored_deletions", "resolvents_checked", "failed_step",
          "failed_clause", "reached_empty")

#: (check_rat, apply_deletions)
MODES = ((True, True), (False, True), (True, False), (False, False))

FAMILIES = ("reason", "multiset", "readd", "reorder", "absent", "unit",
            "refute", "mixed")

#: what the labels on mismatches refer to, in campaign/findings/
KNOWN = {
    "ok_on_sat_after_stale_pivot": "deletion-1",
    "breaks_sat_after_stale_pivot": "deletion-1",
    "accepted_downstream_of_stale_pivot": "deletion-1",
    "not_acceptable_on_present_clauses": "deletion-2",
    "rat_step_counted_as_rup": "deletion-2",
    "failed_clause_keeps_repeats": "deletion-3",
}

FINDINGS = [
    {"id": "deletion-1", "severity": "Critical",
     "summary": "ok=True on a satisfiable formula, both engines: deleting a "
                "reason clause leaves its literal in the root assignment but "
                "removes it from the RAT candidates, so a clause falsified at "
                "the root passes as vacuously RAT. (1)(-1 2), `d -1 2 0, -2 0, 0`"},
    {"id": "deletion-2", "severity": "Bug",
     "summary": "Both engines accept, and count as RUP, a clause not RUP or RAT "
                "on the clauses present, using a literal whose reason was "
                "deleted; docs say clauses present. Same root cause; implied by "
                "the input, so it does not by itself refute anything"},
    {"id": "deletion-3", "severity": "Bug",
     "summary": "Engines disagree on failed_clause when the failing step "
                "repeats a literal: Python removes repeats, native keeps them"},
    {"id": "deletion-4", "severity": "Note",
     "summary": "ignored_deletions also counts deletions of clauses not present, "
                "including input tautologies CNF.add dropped, while report() "
                "calls them all unit deletions"},
]

NOT_CHECKED = [
    "resolvents_checked is compared between engines only; the oracle has no "
    "opinion on the count",
    "reason strings are compared between engines only",
    "real solver proofs (cadical, kissat): every proof here is generated",
    "drat-trim itself: it is not on PATH, so its behaviour is taken from the "
    "oracle's operational flavour, which over-approximates its reason test",
    "the operational flavour is not replayed step by step; dratify documents "
    "length-one",
    "formulas above 10 variables, and long proofs: these are tiny by design",
    "the Rust crate's own API other than through cdclkit_native and "
    "check_proof, so Checker::check_step is reached only via check",
    "binary DRAT, which dratify does not read",
]


# --------------------------------------------------------------------------
# instances
# --------------------------------------------------------------------------


@dataclass
class Instance:
    family: str
    nvars: int
    clauses: list            # DIMACS, as written, repeats and tautologies included
    steps: list              # ("a" | "d", tuple of DIMACS literals), as written

    def formula_text(self) -> str:
        body = "".join(" ".join(map(str, c)) + " 0\n" for c in self.clauses)
        return f"p cnf {self.nvars} {len(self.clauses)}\n{body}"

    def proof_text(self) -> str:
        out = []
        for kind, lits in self.steps:
            head = "d " if kind == "d" else ""
            out.append(head + "".join(f"{l} " for l in lits) + "0\n")
        return "".join(out)

    def show(self) -> str:
        return (f"[{self.family}] " +
                self.formula_text().replace("\n", " / ") + " || " +
                self.proof_text().replace("\n", " / "))


def _is_taut(clause) -> bool:
    lits = set(clause)
    return any(-l in lits for l in lits)


def _key(clause) -> frozenset:
    return frozenset(clause)


def _rand_clause(rng, nvars, lo=1, hi=3):
    size = min(rng.randint(lo, hi), nvars)
    return [v if rng.random() < 0.5 else -v
            for v in rng.sample(range(1, nvars + 1), size)]


def _dress(rng, clause, p_shuffle=0.5, p_repeat=0.25):
    """The same clause written differently: shuffled, with literals repeated."""
    out = list(clause)
    if rng.random() < p_shuffle:
        rng.shuffle(out)
    if out and rng.random() < p_repeat:
        for _ in range(rng.randint(1, 2)):
            out.insert(rng.randint(0, len(out)), rng.choice(out))
    return tuple(out)


class Builder:
    """Grows a proof while tracking, by the oracle only, what it should mean.

    The proof is aimed using the oracle's view of the multiset ``M`` and of the
    root literals ``S``. dratify is never consulted, so a generator bug cannot
    be steered around by a checker bug.
    """

    def __init__(self, rng, nvars, clauses):
        self.rng = rng
        self.nvars = nvars
        self.m = [list(dict.fromkeys(c)) for c in clauses if not _is_taut(c)]
        self.dropped = [list(c) for c in clauses if _is_taut(c)]
        self.steps = []
        self.deleted = []
        self.s = set()
        self.conflict = False
        self.done = False
        self.reprop()

    def reprop(self):
        conflict, s = oracle.propagate(self.m + [[l] for l in self.s])
        self.conflict = self.conflict or conflict
        self.s |= set(s)

    # -- deletions ----------------------------------------------------------

    def d_present(self):
        longer = [c for c in self.m if len(set(c)) >= 2]
        if longer:
            self._delete(self.rng.choice(longer))

    def d_reason(self):
        """Delete a clause that is unit under the root assignment."""
        reasons = [c for c in self.m if _unit_under(c, self.s)]
        if reasons:
            self._delete(self.rng.choice(reasons))

    def d_unit(self):
        units = [c for c in self.m if len(set(c)) == 1]
        if units and self.rng.random() < 0.8:
            self._delete(self.rng.choice(units))
        else:
            self._delete(_rand_clause(self.rng, self.nvars, 1, 1))

    def d_copy(self):
        counts = collections.Counter(_key(c) for c in self.m if len(set(c)) >= 2)
        copies = [c for c in self.m if counts.get(_key(c), 0) >= 2]
        if copies:
            self._delete(self.rng.choice(copies))
        else:
            self.d_present()

    def d_absent(self):
        rng = self.rng
        present = {_key(c) for c in self.m}
        how = rng.randrange(5)
        base = list(rng.choice(self.m)) if self.m else _rand_clause(rng, self.nvars)
        if how == 0 and len(base) >= 3:
            cand = base[:-1]                       # a subset
        elif how == 1:
            spare = [v for v in range(1, self.nvars + 1)
                     if v not in {abs(l) for l in base}]
            cand = base + [rng.choice(spare)] if spare else base  # a superset
        elif how == 2 and base:
            i = rng.randrange(len(base))
            cand = base[:i] + [-base[i]] + base[i + 1:]  # a literal flipped
        elif how == 3:
            cand = [self.nvars + 1, -(self.nvars + 2)]   # variables never seen
        elif self.deleted:
            cand = list(rng.choice(self.deleted))        # deleted once already
        else:
            cand = _rand_clause(rng, self.nvars, 2, 3)
        if _key(cand) in present and len(set(cand)) >= 2:
            cand = _rand_clause(rng, self.nvars, 2, 3)
        self._delete(cand)

    def d_dropped_tautology(self):
        """Delete a tautology the input held, which CNF.add does not keep."""
        if self.dropped:
            self._delete(self.rng.choice(self.dropped))

    def _delete(self, clause):
        written = _dress(self.rng, clause)
        if not written:
            return
        self.steps.append(("d", written))
        if len(set(written)) >= 2:
            before = len(self.m)
            self.m, _ = oracle.remove_one(self.m, written)
            if len(self.m) != before:
                self.deleted.append(list(dict.fromkeys(written)))

    # -- additions ----------------------------------------------------------

    def _add(self, written):
        """Add a step; a clause the checker should reject ends the proof."""
        clause = list(written)
        self.steps.append(("a", tuple(written)))
        units = [[l] for l in self.s]
        if not clause:
            self.done = True
        elif not (self.conflict or oracle.rup(self.m + units, clause)
                  or oracle.rat(self.m, clause, clause[0])
                  or _stale_rat(self.m, units, clause)):
            self.done = True
        else:
            self.m.append(list(dict.fromkeys(clause)))
            self.reprop()

    def a_readd(self):
        if self.deleted:
            self._add(_dress(self.rng, self.rng.choice(self.deleted)))
        else:
            self.d_present()

    def a_dup(self):
        if self.m:
            self._add(_dress(self.rng, self.rng.choice(self.m)))

    def a_rup(self):
        """A resolvent, usually RUP, sometimes needing what has been deleted."""
        rng = self.rng
        pairs = [(c, d, l) for c in self.m for l in c for d in self.m if -l in d]
        if not pairs:
            return
        c, d, l = rng.choice(pairs)
        res = {x for x in c if x != l} | {x for x in d if x != -l}
        if not _is_taut(res) and res:
            self._add(_dress(rng, sorted(res, key=abs)))

    def a_rat(self):
        rng = self.rng
        for _ in range(12):
            clause = _rand_clause(rng, self.nvars + 1, 1, 3)
            if not oracle.rup(self.m, clause) and oracle.rat(self.m, clause, clause[0]):
                self._add(clause)
                return

    def a_stale_pivot(self):
        """A clause whose first literal is false at the root."""
        rng = self.rng
        if not self.s:
            return
        pivot = -rng.choice(sorted(self.s))
        rest = [l for l in _rand_clause(rng, self.nvars, 0, 2) if abs(l) != abs(pivot)]
        self._add((pivot, *rest))

    def a_tautology(self):
        v = self.rng.randint(1, self.nvars)
        self._add((v, -v))

    def a_junk(self):
        self._add(_rand_clause(self.rng, self.nvars))

    def a_empty(self):
        self._add(())

    def run(self, weights, length):
        actions = [getattr(self, name) for name in weights]
        for _ in range(length):
            if self.done:
                return
            self.rng.choices(actions, list(weights.values()))[0]()


def _unit_under(clause, assigned) -> bool:
    """One literal true and the rest false, on a clause of at least two literals."""
    lits = set(clause)
    return (len(lits) >= 2 and len(lits & assigned) == 1
            and all(l in assigned or -l in assigned for l in lits))


def _stale_rat(m, units, clause):
    """RAT with candidates from M and resolvents RUP under M plus the root."""
    lits = set(clause)
    pivot = clause[0]
    full = m + units
    for d in m:
        if -pivot in d and not oracle.rup(full, lits | (set(d) - {-pivot})):
            return False
    return True


def _random_formula(rng, nvars, lo, hi):
    return [_rand_clause(rng, nvars, 2, 3) for _ in range(rng.randint(lo, hi))]


def _implications(rng, nvars):
    """A unit and a chain from it, so that some clauses are reasons at the root."""
    order = rng.sample(range(1, nvars + 1), nvars)
    signs = [v if rng.random() < 0.5 else -v for v in order]
    length = rng.randint(1, max(1, nvars - 1))
    out = [[signs[0]]]
    for a, b in zip(signs, signs[1:length + 1]):
        out.append([-a, b])
    return out, signs[length + 1:]


def _refutation(rng, nvars, k):
    """All sign patterns on k variables, and a resolution proof that uses them."""
    names = rng.sample(range(1, nvars + 1), k)

    def patterns(vs):
        if not vs:
            return [[]]
        return [[s * vs[0], *p] for s in (1, -1) for p in patterns(vs[1:])]

    formula = patterns(names)
    return formula, names, patterns


def generate(rng, family) -> Instance:
    nvars = rng.randint(2, 8)
    if family == "reason":
        nvars = max(nvars, 3)
        clauses, _ = _implications(rng, nvars)
        clauses += _random_formula(rng, nvars, 0, 2)
        b = Builder(rng, nvars, clauses)
        b.run({"d_reason": 5, "a_stale_pivot": 4, "a_rup": 1, "a_rat": 1,
               "d_present": 1, "a_readd": 1}, rng.randint(2, 7))
    elif family == "multiset":
        base = _random_formula(rng, nvars, 2, 5)
        clauses = list(base)
        for c in rng.sample(base, rng.randint(1, min(2, len(base)))):
            for _ in range(rng.randint(1, 2)):
                clauses.append(list(_dress(rng, c)))
        rng.shuffle(clauses)
        b = Builder(rng, nvars, clauses)
        b.run({"d_copy": 6, "a_dup": 3, "a_rup": 2, "a_readd": 2,
               "d_present": 1}, rng.randint(2, 9))
    elif family == "readd":
        clauses = _random_formula(rng, nvars, 2, 7)
        b = Builder(rng, nvars, clauses)
        b.run({"d_present": 5, "a_readd": 5, "a_rup": 2, "a_rat": 1,
               "a_tautology": 1}, rng.randint(2, 9))
    elif family == "reorder":
        clauses = _random_formula(rng, nvars, 2, 7)
        b = Builder(rng, nvars, clauses)
        b.run({"d_present": 6, "a_dup": 1, "a_rup": 2, "a_readd": 1}, rng.randint(2, 8))
    elif family == "absent":
        clauses = _random_formula(rng, nvars, 1, 6)
        b = Builder(rng, nvars, clauses)
        b.run({"d_absent": 6, "d_present": 2, "a_rup": 2, "a_rat": 1}, rng.randint(2, 8))
    elif family == "unit":
        clauses = _random_formula(rng, nvars, 1, 4)
        for _ in range(rng.randint(1, 2)):
            clauses.append(_rand_clause(rng, nvars, 1, 1))
        b = Builder(rng, nvars, clauses)
        b.run({"d_unit": 6, "a_rup": 3, "d_present": 1, "a_junk": 1,
               "a_stale_pivot": 1}, rng.randint(2, 7))
    elif family == "refute":
        nvars = rng.randint(3, 6)
        k = rng.randint(2, min(3, nvars))
        square, names, patterns = _refutation(rng, nvars, k)
        noise = _random_formula(rng, nvars, 0, 2)
        clauses = square + noise
        rng.shuffle(clauses)
        b = Builder(rng, nvars, clauses)
        # one in four deletes a parent too many, which should cost the proof
        reckless = rng.random() < 0.25
        for m in range(k - 1, -1, -1):
            for p in patterns(names[:m]):
                if b.done:
                    continue
                b._add(_dress(rng, p) if p else ())
                for parent in ([*p, names[m]], [*p, -names[m]]):
                    if not b.done and len(parent) >= 2 and rng.random() < 0.7:
                        b._delete(parent)
                if reckless and not b.done and b.m:
                    b.d_present()
    else:
        assert family == "mixed"
        clauses = _random_formula(rng, nvars, 1, 7)
        if rng.random() < 0.5:
            clauses += _implications(rng, nvars)[0]
        if rng.random() < 0.2:
            v = rng.randint(1, nvars)
            clauses.append([v, -v, *_rand_clause(rng, nvars, 0, 1)])
        if rng.random() < 0.3 and clauses:
            clauses.append(list(_dress(rng, rng.choice(clauses))))
        b = Builder(rng, nvars, clauses)
        b.run({"d_present": 3, "d_reason": 2, "d_unit": 2, "d_absent": 2,
               "d_copy": 1, "a_readd": 2, "a_dup": 1, "a_rup": 3, "a_rat": 2,
               "a_stale_pivot": 1, "a_junk": 1, "a_tautology": 1,
               "d_dropped_tautology": 2}, rng.randint(1, 10))
    if not b.done and rng.random() < 0.7:
        b.steps.append(("a", ()))
    return Instance(family, nvars + 2, clauses, b.steps)


# --------------------------------------------------------------------------
# the checkers under judgement, behind one interface
# --------------------------------------------------------------------------


def internal(steps):
    return [(k, tuple(from_dimacs(l) for l in lits)) for k, lits in steps]


class Real:
    """One dratify engine."""

    def __init__(self, engine):
        self.engine = engine
        self.name = engine

    def __call__(self, inst, cnf, steps, check_rat, apply_deletions):
        return check_proof(cnf, internal(steps), check_rat=check_rat,
                           apply_deletions=apply_deletions, engine=self.engine)


class Stub:
    """A checker written from the oracle, correct unless told to be otherwise.

    ``flaw`` picks what is wrong with it. With no flaw it is the length-one
    reading done by definition, and the harness must find nothing to say.
    """

    def __init__(self, flaw=None, name=None, skew=0):
        self.flaw = flaw
        self.name = name or (flaw or "reference")
        self.skew = skew

    def __call__(self, inst, cnf, steps, check_rat, apply_deletions):
        r = CheckResult()
        m = [list(dict.fromkeys(c)) for c in inst.clauses if not _is_taut(c)]
        flaw = self.flaw
        r.resolvents_checked = self.skew
        if flaw != "accept_all" and oracle.propagate(m)[0]:
            r.ok = r.reached_empty = True
            r.reason = "input formula is refuted by unit propagation alone"
            return r
        for kind, lits in steps:
            r.steps += 1
            clause = list(dict.fromkeys(lits))
            if kind == "d":
                self._delete(r, m, list(lits), clause, apply_deletions)
                continue
            if flaw == "accept_all":
                r.rup_steps += 1
            elif flaw == "reject_all":
                return self._fail(r, clause)
            elif oracle.rup(m, clause):
                r.rup_steps += 1
            elif check_rat and clause and oracle.rat(m, clause, clause[0]):
                r.rat_steps += 1
            else:
                return self._fail(r, clause)
            if not clause:
                r.reached_empty = True
                break
            m.append(clause)
        if flaw == "truncated_ok":
            r.ok = True
            r.reason = "looks fine"
        else:
            r.ok = r.reached_empty
            r.reason = "stub"
        if flaw == "accept_all":
            r.ok = r.reached_empty = True
        return r

    def _delete(self, r, m, written, clause, apply_deletions):
        flaw = self.flaw
        if len(clause) <= 1 and flaw != "honour_unit_deletions":
            r.ignored_deletions += 1
            return
        if not apply_deletions:
            return
        if flaw == "never_delete":
            r.deletions += 1
            return
        if flaw == "order_sensitive":
            hit = next((c for c in m if list(c) == written), None)
            if hit is None:
                r.ignored_deletions += 1
            else:
                m.remove(hit)
                r.deletions += 1
            return
        remaining, present = oracle.remove_one(m, clause)
        if flaw == "delete_all_copies" and present:
            m[:] = [c for c in m if _key(c) != _key(clause)]
            r.deletions += 1
            return
        if present:
            m[:] = remaining
            r.deletions += 1
        else:
            r.ignored_deletions += 1

    @staticmethod
    def _fail(r, clause):
        r.failed_step = r.steps
        r.failed_clause = tuple(from_dimacs(l) for l in clause)
        r.reason = "stub rejected"
        return r


# --------------------------------------------------------------------------
# the judge
# --------------------------------------------------------------------------


class Tally:
    def __init__(self):
        self.counts = collections.Counter()
        self.mismatches = collections.Counter()
        self.examples = {}
        self.steps = 0

    def flag(self, label, inst, detail):
        self.mismatches[label] += 1
        text = f"{inst.show()} :: {detail}"
        if label not in self.examples or len(text) < len(self.examples[label]):
            self.examples[label] = text


def _same(a, b, field) -> bool:
    return getattr(a, field) == getattr(b, field)


def compare_engines(ta, inst, ra, rb, context):
    for field in FIELDS:
        if _same(ra, rb, field):
            continue
        a, b = getattr(ra, field), getattr(rb, field)
        if (field == "failed_clause" and a is not None and b is not None
                and tuple(dict.fromkeys(a)) == tuple(dict.fromkeys(b))):
            ta.flag("failed_clause_keeps_repeats", inst, f"{context}: {a} vs {b}")
        else:
            ta.flag("engine_field", inst, f"{context}: {field}: {a!r} vs {b!r}")


def judge(ta, inst, engines):
    """Walk one instance through every mode. Every verdict goes past the oracle."""
    a, b = engines
    cnf = parse_dimacs(inst.formula_text())
    input_clauses = [list(dict.fromkeys(c)) for c in inst.clauses if not _is_taut(c)]
    if any(_is_taut(c) for c in inst.clauses):
        ta.counts["formulas_with_a_dropped_tautology"] += 1
    sat = oracle.satisfiable(input_clauses)

    for check_rat, apply_deletions in MODES:
        ctx = f"check_rat={check_rat} apply_deletions={apply_deletions}"
        try:
            ra = a(inst, cnf, inst.steps, check_rat, apply_deletions)
            rb = b(inst, cnf, inst.steps, check_rat, apply_deletions)
        except Exception as e:             # a crash is an answer, and a wrong one
            ta.flag("exception", inst, f"{ctx}: {e!r}")
            continue
        compare_engines(ta, inst, ra, rb, ctx)
        for r, runner in ((ra, a), (rb, b)):
            seen = _judge_walk(ta, inst, cnf, r, runner, input_clauses, sat,
                               check_rat, apply_deletions, ctx)
            _judge_end_to_end(ta, inst, r, sat, seen, ctx)
    if isinstance(a, Real):
        _judge_paths(ta, inst, cnf)


def _judge_end_to_end(ta, inst, r, sat, stale_pivot_seen, ctx):
    if r.ok and not r.reached_empty:
        ta.flag("ok_without_empty", inst, ctx)
    if r.failed_step != -1 and r.ok:
        ta.flag("ok_with_failed_step", inst, ctx)
    if r.reached_empty and r.failed_step == -1 and not r.ok:
        ta.flag("empty_but_not_ok", inst, ctx)
    if r.ok and sat:
        ta.counts["ok_true_on_sat"] += 1
        # primary, and labelled known only if the walk saw the known cause
        ta.flag("ok_on_sat_after_stale_pivot" if stale_pivot_seen else "ok_on_sat",
                inst, ctx)
    elif r.ok:
        ta.counts["ok_true_on_unsat"] += 1
    elif sat:
        ta.counts["ok_false_on_sat"] += 1
    else:
        ta.counts["ok_false_on_unsat"] += 1


def _judge_walk(ta, inst, cnf, full, runner, input_clauses, sat, check_rat,
                apply_deletions, ctx) -> bool:
    """Judge each step, reading the verdicts off the checker's prefix results.

    Returns whether a RAT step with its pivot false at the root was accepted.
    """
    m = [list(c) for c in input_clauses]
    conflict, s = oracle.propagate(m)
    s = set(s)
    if conflict:
        ta.counts["input_refuted_by_up"] += 1
        if not (full.ok and full.reached_empty and full.steps == 0):
            ta.flag("input_refuted_not_ok", inst, ctx)
        return False

    prev = CheckResult()
    stale_pivot_seen = False
    deleted_keys = set()
    for k, (kind, lits) in enumerate(inst.steps, 1):
        try:
            r = runner(inst, cnf, inst.steps[:k], check_rat, apply_deletions)
        except Exception as e:
            ta.flag("exception", inst, f"{ctx}: step {k}: {e!r}")
            return stale_pivot_seen
        ta.steps += 1
        clause = list(dict.fromkeys(lits))
        if r.steps != k:
            ta.flag("steps_field", inst, f"{ctx}: step {k}: steps={r.steps}")
            return stale_pivot_seen
        if kind == "d":
            ta.counts["deletions_walked"] += 1
            _judge_deletion(ta, inst, r, prev, m, s, list(lits), clause,
                            apply_deletions, deleted_keys, ctx, k)
            if r.failed_step != -1:
                ta.flag("rejected_a_deletion", inst, f"{ctx}: step {k}")
                return stale_pivot_seen
            prev = r
            continue

        rup = oracle.rup(m, clause)
        rat = bool(clause) and oracle.rat(m, clause, clause[0])
        acceptable = rup or (check_rat and rat)
        rejected = r.failed_step == k
        grew_rup = r.rup_steps - prev.rup_steps
        grew_rat = r.rat_steps - prev.rat_steps
        readding = _key(clause) in deleted_keys

        if rejected:
            ta.counts["additions_rejected"] += 1
            if readding:
                ta.counts["readd_rejected"] += 1
            if acceptable:
                ta.flag("false_rejection", inst, f"{ctx}: step {k}: {clause}")
            if tuple(sorted(map(to_dimacs, set(r.failed_clause or ())))) != tuple(sorted(clause)):
                ta.flag("failed_clause_wrong", inst, f"{ctx}: step {k}: {r.failed_clause}")
            if r.ok:
                ta.flag("ok_with_failed_step", inst, ctx)
            return stale_pivot_seen
        if grew_rup + grew_rat != 1:
            ta.flag("counters", inst, f"{ctx}: step {k}: +{grew_rup} rup +{grew_rat} rat")
            return stale_pivot_seen
        if r.failed_step != -1:
            ta.flag("failed_step_field", inst, f"{ctx}: step {k}: {r.failed_step}")
            return stale_pivot_seen

        if grew_rup:
            ta.counts["additions_rup"] += 1
        else:
            ta.counts["additions_rat_only"] += 1
        if readding:
            ta.counts["readd_accepted"] += 1
        if rup and grew_rat:
            ta.flag("rup_step_counted_as_rat", inst, f"{ctx}: step {k}: {clause}")
        if grew_rup and rat and not rup:
            ta.counts["rat_on_M_but_rup_via_root"] += 1
            ta.flag("rat_step_counted_as_rup", inst, f"{ctx}: step {k}: {clause}")
        if grew_rat and not check_rat:
            ta.flag("rat_while_disabled", inst, f"{ctx}: step {k}")

        units = [[l] for l in sorted(s)]
        if not acceptable:
            supported = (conflict or oracle.rup(m + units, clause)
                         or (check_rat and bool(clause) and _stale_rat(m, units, clause)))
            if stale_pivot_seen:
                ta.flag("accepted_downstream_of_stale_pivot", inst,
                        f"{ctx}: step {k}: {clause}")
            elif conflict and not sat:
                # Top-level propagation has refuted the formula. The oracle's
                # operational flavour stops honouring deletions here, and the
                # verdict is right whichever flavour is read.
                ta.counts["accepted_after_root_conflict"] += 1
            elif supported:
                ta.counts["accepted_only_via_stale_root"] += 1
                ta.flag("not_acceptable_on_present_clauses", inst,
                        f"{ctx}: step {k}: {clause}")
            else:
                ta.flag("unexplained_acceptance", inst, f"{ctx}: step {k}: {clause}")

        # A RAT step whose pivot is false at the root, its reason gone. By the
        # definition, on M, this step is fine: it is counted and not flagged.
        # What goes wrong is what a checker that keeps the root does next, and
        # that is judged at the later steps and at the end. This only labels it.
        if grew_rat and clause and -clause[0] in s:
            stale_pivot_seen = True
            ta.counts["accepted_rat_pivot_false_at_root"] += 1

        if not oracle.preserves_sat(m, clause):
            if stale_pivot_seen:
                ta.flag("breaks_sat_after_stale_pivot", inst, f"{ctx}: step {k}: {clause}")
            elif conflict and not sat:
                ta.counts["accepted_empty_after_refutation"] += 1
            else:
                ta.flag("breaks_sat", inst, f"{ctx}: step {k}: {clause}")
        if not check_rat and not oracle.implies(input_clauses, clause):
            # with RAT off everything accepted must follow from the input
            ta.flag("rup_mode_not_implied_by_input", inst, f"{ctx}: step {k}: {clause}")

        if not clause:
            ta.counts["empty_clause_accepted"] += 1
            if not r.reached_empty or not r.ok:
                ta.flag("empty_not_reached", inst, f"{ctx}: step {k}")
            return stale_pivot_seen
        m.append(clause)
        c2, s2 = oracle.propagate(m + [[l] for l in sorted(s)])
        if c2 and not conflict:
            ta.counts["root_conflict_reached"] += 1
        conflict = conflict or c2
        s |= set(s2)
        prev = r
    return stale_pivot_seen


def _judge_deletion(ta, inst, r, prev, m, s, written, clause, apply_deletions,
                    deleted_keys, ctx, k):
    grew_del = r.deletions - prev.deletions
    grew_ign = r.ignored_deletions - prev.ignored_deletions
    if len(written) != len(clause):
        ta.counts["deletions_with_repeated_literals"] += 1
    if len(clause) <= 1:
        ta.counts["deletions_unit_ignored"] += 1
        if clause and [clause[0]] in m:
            ta.counts["deletions_unit_present_ignored"] += 1
        expect = (0, 1)
    elif not apply_deletions:
        ta.counts["deletions_off"] += 1
        expect = (0, 0)
    else:
        remaining, present = oracle.remove_one(m, clause)
        if present:
            expect = (1, 0)
            ta.counts["deletions_applied"] += 1
            if _is_taut(clause):
                ta.counts["deletions_of_tautological_lemmas"] += 1
            copies = sum(1 for c in m if _key(c) == _key(clause))
            ta.counts["deletions_one_of_several_copies" if copies > 1
                      else "deletions_last_copy"] += 1
            stored = next(c for c in m if _key(c) == _key(clause))
            if stored != clause:
                ta.counts["deletions_reordered"] += 1
            if _unit_under(clause, s):
                ta.counts["deletions_of_reason_clauses"] += 1
            m[:] = remaining
            deleted_keys.add(_key(clause))
        else:
            expect = (0, 1)
            ta.counts["deletions_absent"] += 1
            if _is_taut(clause) and _key(clause) in {_key(c) for c in inst.clauses}:
                ta.counts["deletions_of_dropped_input_tautologies"] += 1
            if _key(clause) in deleted_keys:
                ta.counts["deletions_already_deleted"] += 1
    if (grew_del, grew_ign) != expect:
        ta.flag("deletion_counters", inst,
                f"{ctx}: step {k}: {clause}: +{grew_del} deleted +{grew_ign} "
                f"ignored, expected +{expect[0]} +{expect[1]}")


def _judge_paths(ta, inst, cnf):
    """A list of steps, proof text and a MemoryProof must read the same."""
    steps = internal(inst.steps)
    proof = MemoryProof()
    for kind, lits in steps:
        (proof.delete if kind == "d" else proof.add)(lits)
    for engine in ("python", "native"):
        base = check_proof(cnf, steps, engine=engine)
        for name, given in (("text", inst.proof_text()), ("memory", proof),
                            ("memory text", proof.to_text())):
            other = check_proof(cnf, given, engine=engine)
            for field in FIELDS:
                if not _same(base, other, field):
                    ta.flag("input_path", inst, f"{engine} {name}: {field}: "
                            f"{getattr(base, field)!r} vs {getattr(other, field)!r}")
        ta.counts["input_paths_compared"] += 1


# --------------------------------------------------------------------------
# driving
# --------------------------------------------------------------------------

#: categories this generator claims to reach; zero in any of them fails the run
CLAIMED = (
    "additions_rup", "additions_rat_only", "additions_rejected",
    "deletions_applied", "deletions_unit_ignored",
    "deletions_unit_present_ignored", "deletions_absent",
    "deletions_already_deleted", "deletions_of_reason_clauses",
    "deletions_one_of_several_copies", "deletions_last_copy",
    "deletions_reordered", "deletions_with_repeated_literals", "deletions_off",
    "deletions_of_tautological_lemmas",
    "deletions_of_dropped_input_tautologies",
    "readd_accepted", "readd_rejected",
    "ok_true_on_unsat", "ok_false_on_unsat", "ok_false_on_sat",
    "root_conflict_reached", "formulas_with_a_dropped_tautology",
    "input_refuted_by_up", "accepted_rat_pivot_false_at_root",
)


def sweep(seed, instances, engines):
    rng = random.Random(seed)
    ta = Tally()
    for i in range(instances):
        family = FAMILIES[i % len(FAMILIES)]
        inst = generate(rng, family)
        ta.counts[f"family_{family}"] += 1
        judge(ta, inst, engines)
    return ta


def real_engines():
    try:
        import cdclkit_native
    except ImportError:
        sys.exit("cdclkit_native is not installed, so the native engine cannot "
                 "run. This generator runs both engines or none.")
    register_native(cdclkit_native)
    return Real("python"), Real("native")


def self_test() -> int:
    """Show the harness has teeth, and that it is quiet about a correct checker."""
    n = 320
    failed = 0
    reference = Stub()
    ta = sweep(1, n, (reference, reference))
    print(f"reference (length-one by definition): "
          f"{sum(ta.mismatches.values())} mismatches, {ta.steps} steps")
    if ta.mismatches:
        failed += 1
        print("  FAILED: a correct checker must not be flagged")
        for label, text in ta.examples.items():
            print(f"  {label}: {text}")
    for flaw, expected in (
        ("accept_all", {"ok_on_sat", "unexplained_acceptance"}),
        ("reject_all", {"false_rejection"}),
        ("delete_all_copies", {"deletion_counters", "unexplained_acceptance",
                               "false_rejection"}),
        ("order_sensitive", {"deletion_counters"}),
        ("honour_unit_deletions", {"deletion_counters"}),
        ("never_delete", {"deletion_counters", "unexplained_acceptance"}),
        ("truncated_ok", {"ok_without_empty"}),
    ):
        stub = Stub(flaw)
        ta = sweep(1, n, (stub, stub))
        hit = expected & set(ta.mismatches)
        print(f"{flaw}: flagged {dict(ta.mismatches)}")
        if not hit:
            failed += 1
            print(f"  FAILED: expected one of {sorted(expected)}")
    skew = (Stub(), Stub(name="skewed", skew=1))
    ta = sweep(1, n, skew)
    print(f"engines disagreeing on one field: flagged {dict(ta.mismatches)}")
    if "engine_field" not in ta.mismatches:
        failed += 1
        print("  FAILED: expected engine_field")
    print("SELF-TEST FAILED" if failed else "self-test passed")
    return 1 if failed else 0


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--instances", type=int, default=40000)
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--no-write", action="store_true",
                    help="do not write campaign/results/deletion.json")
    args = ap.parse_args(argv)
    if args.self_test:
        return self_test()

    engines = real_engines()
    start = time.perf_counter()
    ta = sweep(args.seed, args.instances, engines)
    elapsed = time.perf_counter() - start

    missing = [c for c in CLAIMED if not ta.counts[c]]
    unexplained = {k: v for k, v in ta.mismatches.items() if k not in KNOWN}
    known = {k: v for k, v in ta.mismatches.items() if k in KNOWN}

    print(f"seed {args.seed}, {args.instances} instances, {ta.steps} steps judged, "
          f"{elapsed:.1f}s")
    for name in sorted(ta.counts):
        print(f"  {name}: {ta.counts[name]}")
    for label in sorted(ta.mismatches):
        tag = KNOWN.get(label, "UNEXPLAINED")
        print(f"MISMATCH {label} [{tag}]: {ta.mismatches[label]}")
        print(f"  shortest: {ta.examples[label]}")
    if missing:
        print(f"CATEGORIES NEVER REACHED: {missing}")

    if not args.no_write:
        results = {
            "corner": "deletion",
            "seeds": [args.seed],
            "instances": args.instances,
            "steps": ta.steps,
            "per_category_counts": dict(sorted(ta.counts.items())),
            "mismatches": {k: {"count": v, "label": KNOWN.get(k, "UNEXPLAINED")}
                           for k, v in sorted(ta.mismatches.items())},
            "runtime_seconds": round(elapsed, 1),
            "findings": FINDINGS,
            "not_checked": NOT_CHECKED,
        }
        out = Path(__file__).parent / "results" / "deletion.json"
        out.write_text(json.dumps(results, indent=2) + "\n", encoding="ascii")

    if unexplained or known or missing:
        print(f"exit 1: {sum(known.values())} labelled, "
              f"{sum(unexplained.values())} unexplained, "
              f"{len(missing)} categories at zero")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
