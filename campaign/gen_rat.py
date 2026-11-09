# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Soundness campaign, the RAT corner of dratify.

    python -m campaign.gen_rat                      # the reported run
    python -m campaign.gen_rat --self-test          # does the harness catch anything?
    python -m campaign.gen_rat --seed 7 --instances 500 --no-shrink

Aimed at: the pivot being the first literal and only the first literal; RAT
candidates deleted earlier, including a surviving copy and a "deleted" unit;
tautological resolvents and tautological candidates; RAT steps after deletions,
including deletions of the clause that made a root literal true.

The reference is ``campaign.oracle`` under the ``operational`` flavour, the one
dratify documents: a deletion applies unless the clause is unit under the root
assignment, or the root has already conflicted. Formulas
go through ``parse_dimacs``, whose ``CNF.add`` documents dropping tautologies, so
the oracle judges that normalised formula. Where the literal formula would have
answered differently the case is counted as a note, as the oracle's own
limitations say to.

The primary question is end to end: ``ok=True`` requires ``not satisfiable(F)``.

Half the point is that mismatches are not filtered. The findings this was written
to catch, rat-1, rat-2 and rat-4, are fixed and carry no label now: any mismatch
reads ``unexplained`` and makes the run exit 1, and ``model_check(stale=True)``, the
model of rat-1, is a stub the self-test must flag. The ``stale`` part of the instances
goes on deleting the clauses root literals rest on, to keep aiming at that rule.
"""

from __future__ import annotations

import argparse
import collections
import json
import pathlib
import random
import sys
import time

from campaign import oracle

from dratify import check_proof, parse_dimacs, register_native
from dratify.lits import from_dimacs, to_dimacs

CORNER = "rat"
DEFAULT_SEED = 20261108
DEFAULT_INSTANCES = 10000
MAX_VAR = 14  # the oracle stops at 16

#: Each must be above zero or the run fails: a generator that never reaches its
#: corner reads as evidence and is not.
REQUIRED = (
    "steps_rup_accepted",
    "steps_rat_only_accepted",
    "steps_rejected",
    "rat_vacuous",
    "rat_all_resolvents_tautological",
    "rat_nontrivial_resolvents",
    "rat_fresh_variable_pivot",
    "rat_only_on_first_literal",
    "rat_after_deletion",
    "rat_enabled_by_deletion",
    "rat_with_root_false_literal",
    "rat_unit_at_root_on_arrival",
    "rejected_rat_on_a_later_literal",
    "rejected_candidate_copy_survived",
    "rejected_unit_candidate_survived",
    "rejected_tautological_candidate",
    "tautological_lemma_accepted",
    "tautological_candidate_seen",
    "repeated_literal_steps",
    "deletions_applied",
    "deletions_ignored_unit",
    "deletions_absent",
    "deletions_of_a_root_reason",
    "refutation_accepted_unsat",
    "refutation_with_rat_steps_accepted",
    "refutation_with_deletions_accepted",
    "bogus_refutation_on_sat_attempted",
    "no_empty_clause_proofs",
    "input_refuted_by_propagation",
    "formula_tautology_dropped",
    "runs_rat_disabled",
    "runs_rat_disabled_rat_step_rejected",
    "runs_deletions_disabled",
    "instances_no_stale",
    "instances_stale",
)


# --------------------------------------------------------------------------
# the case
# --------------------------------------------------------------------------


def cnf_text(clauses):
    used = [abs(l) for c in clauses for l in c]
    head = f"p cnf {max(used, default=1)} {len(clauses)}\n"
    return head + "".join(" ".join(map(str, c)) + (" 0\n" if c else "0\n")
                          for c in clauses)


def proof_text(steps):
    out = []
    for kind, lits in steps:
        body = " ".join(map(str, lits))
        out.append(("d " if kind == "d" else "") + (body + " 0\n" if lits else "0\n"))
    return "".join(out)


def normalised(clauses):
    """What ``CNF.add`` documents: tautologies gone, repeats collapsed."""
    out = []
    for c in clauses:
        s = set(c)
        if any(-l in s for l in s):
            continue
        out.append(list(dict.fromkeys(c)))
    return out


def cut_at_empty(steps):
    """A checker stops at the empty clause, so nothing after it is judged."""
    out = []
    for kind, lits in steps:
        out.append((kind, list(lits)))
        if kind == "a" and not lits:
            break
    return out


# --------------------------------------------------------------------------
# what the oracle expects
# --------------------------------------------------------------------------


def candidates(current, clause):
    pivot = clause[0]
    return [d for d in current if -pivot in set(d)]


def non_tautological(cands, clause):
    """Candidates whose resolvent with ``clause`` is not a tautology via C."""
    lits = set(clause)
    pivot = clause[0]
    return [d for d in cands
            if not any(-l in lits for l in set(d) if l != -pivot)]


def oracle_walk(clauses, steps, check_rat=True, apply_deletions=True,
                flavour="operational"):
    """Every field a checker reports, from the oracle alone."""
    fn = normalised(clauses)
    want = dict(ok=False, reached_empty=False, steps=0, rup_steps=0, rat_steps=0,
                deletions=0, ignored_deletions=0, failed_step=-1,
                failed_lits=None, res_lo=0, res_hi=0)
    if oracle.propagate(fn)[0]:
        want.update(ok=True, reached_empty=True)
        return want
    steps = cut_at_empty(steps)
    numbered = list(enumerate(steps, 1))
    if not apply_deletions:
        numbered = [(i, s) for i, s in numbered if s[0] == "a"]
    judged, _ = oracle.replay(fn, [s for _, s in numbered], flavour,
                              stop_at_unacceptable=False)
    current = [list(c) for c in fn]
    last = 0
    for (index, _), step in zip(numbered, judged):
        # deletions that were switched off still count as steps
        last = index
        if step.kind == "d":
            if step.applied:
                want["deletions"] += 1
                current, _ = oracle.remove_one(current, step.clause)
            else:
                want["ignored_deletions"] += 1
            continue
        good = step.rup or (check_rat and step.rat_on_first)
        if not good:
            want["failed_step"] = index
            want["failed_lits"] = frozenset(step.clause)
            if check_rat and step.clause:
                want["res_lo"] += 1
                want["res_hi"] += len(non_tautological(
                    candidates(current, step.clause), step.clause))
            break
        if step.rup:
            want["rup_steps"] += 1
        else:
            want["rat_steps"] += 1
            n = len(non_tautological(candidates(current, step.clause), step.clause))
            want["res_lo"] += n
            want["res_hi"] += n
        if not step.clause:
            want["reached_empty"] = True
            want["ok"] = True
            break
        current.append(list(step.clause))
    if want["failed_step"] != -1:
        want["steps"] = want["failed_step"]
    elif want["reached_empty"]:
        want["steps"] = last
    else:
        want["steps"] = len(steps)
    if not apply_deletions:
        want["ignored_deletions"] = None  # undocumented here; engines still compared
    return want


def model_check(clauses, steps, check_rat=True, apply_deletions=True, *,
                stale=False, apply_unit_deletions=False, any_pivot=False,
                keep_deleted_candidates=False, tautology_fails=False):
    """A checker written from the definitions on the oracle's primitives.

    With no options it is correct, and the self-test holds the harness to
    finding nothing wrong with it. Each option is one way to be wrong. ``stale``
    is the model of finding rat-1, now fixed: only clauses of at most one literal
    are spared, and the root assignment and any root conflict outlive the clauses
    they rest on.
    """
    fn = normalised(clauses)
    r = dict(ok=False, reason="model", steps=0, rup_steps=0, rat_steps=0,
             deletions=0, ignored_deletions=0, resolvents_checked=0,
             failed_step=-1, failed_clause=None, reached_empty=False)
    conflict, root = oracle.propagate(fn)
    if conflict:
        r.update(ok=True, reached_empty=True)
        return r
    current = [list(c) for c in fn]
    graveyard = []
    sticky = False

    def is_rup(lits):
        if not stale:
            return oracle.rup(current, lits)
        return sticky or oracle.propagate(
            current, set(root) | {-l for l in lits})[0]

    def is_rat(clause, pivot):
        lits = set(clause)
        for d in current + (graveyard if keep_deleted_candidates else []):
            ds = set(d)
            if -pivot not in ds:
                continue
            if any(-l in lits for l in ds if l != -pivot):
                if tautology_fails:
                    return False
                continue
            r["resolvents_checked"] += 1
            if not is_rup(lits | (ds - {-pivot})):
                return False
        return True

    for kind, lits in cut_at_empty(steps):
        r["steps"] += 1
        clause = list(dict.fromkeys(lits))
        if kind == "d":
            if len(clause) <= 1 and not apply_unit_deletions:
                r["ignored_deletions"] += 1
            elif apply_deletions:
                spared = (not stale and not (apply_unit_deletions and len(clause) <= 1)
                          and (oracle.propagate(current)[0]
                               or oracle.is_pseudo_unit(current, clause)))
                new, present = oracle.remove_one(current, clause)
                if spared:
                    r["ignored_deletions"] += 1
                elif present:
                    graveyard.append(clause)
                    current = new
                    r["deletions"] += 1
                else:
                    r["ignored_deletions"] += 1
            continue
        if is_rup(clause):
            r["rup_steps"] += 1
        elif check_rat and clause and (
                any(is_rat(clause, p) for p in clause) if any_pivot
                else is_rat(clause, clause[0])):
            r["rat_steps"] += 1
        else:
            r["failed_step"] = r["steps"]
            r["failed_clause"] = tuple(clause)
            return r
        if not clause:
            r.update(ok=True, reached_empty=True)
            return r
        current.append(clause)
        if stale:
            conflict, root = oracle.propagate(current, root)
            sticky = sticky or conflict
    return r


# --------------------------------------------------------------------------
# comparing
# --------------------------------------------------------------------------

EXACT = ("ok", "reached_empty", "steps", "rup_steps", "rat_steps", "deletions",
         "ignored_deletions", "failed_step")
ALL_FIELDS = EXACT + ("reason", "resolvents_checked", "failed_clause")


def diff_oracle(got, want):
    """The fields on which a checker's result contradicts the oracle's walk."""
    out = []
    for field in EXACT:
        if want[field] is not None and got[field] != want[field]:
            out.append(field)
    got_lits = None if got["failed_clause"] is None else frozenset(got["failed_clause"])
    if got_lits != want["failed_lits"]:
        out.append("failed_clause")
    if not want["res_lo"] <= got["resolvents_checked"] <= want["res_hi"]:
        out.append("resolvents_checked")
    return out


def judge_case(clauses, steps, engines, flavour="operational"):
    """Every mismatch in one case: a list of (label, kind)."""
    found = []
    runs = 0
    judged = 0
    fn = normalised(clauses)
    sat = oracle.satisfiable(fn)
    configs = ((True, True, engines),
               (False, True, engines[:2]),
               (True, False, engines[:2]))
    results = {}
    for check_rat, apply_deletions, group in configs:
        want = oracle_walk(clauses, steps, check_rat, apply_deletions, flavour)
        judged += want["steps"]
        base = None
        for name, fn_engine in group:
            got = fn_engine(clauses, steps, check_rat, apply_deletions)
            runs += 1
            if "raised" in got:
                # A raise is not a verdict.
                found.append(("unexplained", f"{name}: raised ValueError instead of a verdict"))
                continue
            if got["ok"] and sat:
                found.append(("unexplained", "ok-true-on-satisfiable-formula"))
            bad = diff_oracle(got, want)
            for field in bad:
                found.append(("unexplained", f"{name}: {field} contradicts the oracle"))
            if base is None:
                base = got
                results[check_rat, apply_deletions] = got
                continue
            split = [f for f in ALL_FIELDS if got[f] != base[f]]
            if split:
                for field in split:
                    found.append(("unexplained", f"engines disagree on {field}"))
    return found, runs, judged, results, sat


# --------------------------------------------------------------------------
# coverage: what the case actually reached, from the oracle and not the intent
# --------------------------------------------------------------------------


def shrinks_root(before, after):
    b_conf, b_true = oracle.propagate(before)
    a_conf, a_true = oracle.propagate(after)
    if b_conf:
        return not a_conf
    return a_conf is False and not b_true <= a_true


def count_coverage(clauses, steps, results, sat, tally):
    fn = normalised(clauses)
    if len(fn) != len(clauses):
        tally["formula_tautology_dropped"] += 1
    if oracle.propagate(fn)[0]:
        tally["input_refuted_by_propagation"] += 1
        return
    steps = cut_at_empty(steps)
    current = [list(c) for c in fn]
    original_vars = {abs(l) for c in clauses for l in c}
    graveyard = []
    unit_deleted = set()
    applied = 0
    rat_ok = 0
    finished_clean = True
    for kind, lits in steps:
        clause = list(dict.fromkeys(lits))
        if len(clause) < len(lits):
            tally["repeated_literal_steps"] += 1
        s = frozenset(clause)
        if kind == "d":
            if len(s) <= 1:
                tally["deletions_ignored_unit"] += 1
                unit_deleted.add(s)
                continue
            new, present = oracle.remove_one(current, clause)
            if oracle.propagate(current)[0]:
                tally["deletions_ignored_after_conflict"] += 1
                continue
            if oracle.is_pseudo_unit(current, clause):
                if present:
                    tally["deletions_of_a_root_reason"] += 1
                continue
            if not present:
                tally["deletions_absent"] += 1
                continue
            tally["deletions_applied"] += 1
            graveyard.append(clause)
            current = new
            applied += 1
            continue
        conflict, root = oracle.propagate(current)
        rup = oracle.rup(current, clause)
        rat = bool(clause) and oracle.rat(current, clause, clause[0])
        if any(-l in s for l in s) and rup:
            tally["tautological_lemma_accepted"] += 1
        cands = candidates(current, clause) if clause else []
        if any(any(-l in set(d) for l in set(d)) for d in cands):
            tally["tautological_candidate_seen"] += 1
        if rup:
            tally["steps_rup_accepted"] += 1
        elif rat:
            tally["steps_rat_only_accepted"] += 1
            rat_ok += 1
            pivot = clause[0]
            if not cands:
                tally["rat_vacuous"] += 1
            elif not non_tautological(cands, clause):
                tally["rat_all_resolvents_tautological"] += 1
            else:
                tally["rat_nontrivial_resolvents"] += 1
            if abs(pivot) not in original_vars:
                tally["rat_fresh_variable_pivot"] += 1
            if any(not oracle.rat(current, clause, l) for l in clause[1:]):
                tally["rat_only_on_first_literal"] += 1
            if applied:
                tally["rat_after_deletion"] += 1
            if graveyard and not oracle.rat(current + graveyard, clause, pivot):
                tally["rat_enabled_by_deletion"] += 1
            false_at_root = [l for l in clause if -l in root]
            if false_at_root:
                tally["rat_with_root_false_literal"] += 1
                if len(false_at_root) == len(clause) - 1 and not (s & root):
                    tally["rat_unit_at_root_on_arrival"] += 1
        else:
            tally["steps_rejected"] += 1
            finished_clean = False
            if clause:
                if any(oracle.rat(current, clause, l) for l in clause[1:]):
                    tally["rejected_rat_on_a_later_literal"] += 1
                failing = [d for d in cands if not oracle.rup(
                    current, s | (set(d) - {-clause[0]}))]
                dead = {frozenset(d) for d in graveyard}
                if any(frozenset(d) in dead for d in failing):
                    tally["rejected_candidate_copy_survived"] += 1
                if any(frozenset(d) in unit_deleted for d in failing):
                    tally["rejected_unit_candidate_survived"] += 1
                if any(any(-l in set(d) for l in set(d)) for d in failing):
                    tally["rejected_tautological_candidate"] += 1
            break
        if not clause:
            break
        current.append(clause)
    # end to end
    last_empty = bool(steps) and steps[-1] == ("a", [])
    want = oracle_walk(clauses, steps)
    if last_empty and sat:
        tally["bogus_refutation_on_sat_attempted"] += 1
    if not last_empty:
        tally["no_empty_clause_proofs"] += 1
    primary = results.get((True, True))
    if want["ok"] and primary and primary["ok"] and finished_clean:
        tally["refutation_accepted_unsat"] += 1
        if rat_ok:
            tally["refutation_with_rat_steps_accepted"] += 1
        if applied:
            tally["refutation_with_deletions_accepted"] += 1
    # the configurations, and whether they said anything
    tally["runs_rat_disabled"] += 1
    off = oracle_walk(clauses, steps, check_rat=False)
    if off["failed_step"] > 0 and oracle_walk(clauses, steps)["failed_step"] != off["failed_step"]:
        tally["runs_rat_disabled_rat_step_rejected"] += 1
    tally["runs_deletions_disabled"] += 1
    # Notes, not failures: where the flavours part company, and the literal
    # reading of a tautological candidate.
    documented, _ = oracle.replay(fn, steps, "operational")
    for flavour, key in (("length-one", "note_verdict_differs_length_one"),
                         ("specified", "note_verdict_differs_specified")):
        other, _ = oracle.replay(fn, steps, flavour)
        if [x.acceptable for x in other] != [x.acceptable for x in documented]:
            tally[key] += 1
    if len(fn) != len(clauses):
        literal, _ = oracle.replay([list(c) for c in clauses], steps, "operational")
        if [x.acceptable for x in literal] != [x.acceptable for x in documented]:
            tally["note_literal_tautological_candidate_differs"] += 1
            bad = next((x for x in literal if not x.acceptable), None)
            if bad is not None and bad.preserves_sat:
                tally["note_literal_rat_false_but_preserves_sat"] += 1


# --------------------------------------------------------------------------
# the generator
# --------------------------------------------------------------------------


class Abort(Exception):
    pass


class Gen:
    """Builds one formula and proof, tracking a multiset that honours deletions of
    two or more literals, so that it goes on to try what a kept reason forbids."""

    def __init__(self, rng, mode):
        self.rng = rng
        self.mode = mode
        self.nvars = rng.randint(3, 10)
        self.max_var = self.nvars
        self.steps = []
        self.formula = self.make_formula()
        self.current = normalised(self.formula)

    # -- formula ---------------------------------------------------------

    def lit(self, top=None):
        v = self.rng.randint(1, top or self.max_var)
        return v if self.rng.random() < .5 else -v

    def clause_of(self, size, top=None):
        top = top or self.max_var
        vs = self.rng.sample(range(1, top + 1), min(size, top))
        return [v if self.rng.random() < .5 else -v for v in vs]

    def make_formula(self):
        """Refuted by propagation alone ends a check at once, so keep that rare."""
        for _ in range(30):
            f = self.one_formula()
            if self.rng.random() < .03 or not oracle.propagate(normalised(f))[0]:
                return f
        return f

    def one_formula(self):
        rng = self.rng
        kind = rng.choice(("planted", "planted", "random", "unsat", "unsat"))
        model = {v: rng.random() < .5 for v in range(1, self.nvars + 1)}
        f = []
        for _ in range(rng.randint(2, 3 * self.nvars)):
            c = self.clause_of(rng.choice((1, 2, 2, 2, 3, 3, 3, 4, 4, 6)), self.nvars)
            if kind == "planted" and not any((l > 0) == model[abs(l)] for l in c):
                c[0] = -c[0]
            f.append(c)
        if kind == "unsat":
            k = rng.randint(2, 3)
            core = rng.sample(range(1, self.nvars + 1), k)
            for mask in range(1 << k):
                f.append([v if mask >> i & 1 else -v for i, v in enumerate(core)])
        if rng.random() < .6 or self.mode == "stale":
            # a chain, so root literals exist that rest on non-unit clauses
            a, b, c = rng.sample(range(1, self.nvars + 1), 3)
            a, b, c = [(x if model[x] else -x) for x in (a, b, c)]
            f += [[a], [-a, b], [-b, c]]
        if rng.random() < .15:
            f.append(list(rng.choice(f)))
        if rng.random() < .1:
            v = rng.randint(1, self.nvars)
            f.append(rng.sample([v, -v, self.lit(self.nvars)], 2))
        if rng.random() < .1:
            v = rng.randint(1, self.nvars)
            f.append([v, -v])
        if rng.random() < .1:
            f.append([])
        rng.shuffle(f)
        return f

    # -- emitting --------------------------------------------------------

    def wrap(self, clause):
        """Sometimes repeat a literal, never in front of the pivot."""
        if clause and self.rng.random() < .07:
            return clause + [self.rng.choice(clause)]
        return list(clause)

    def add(self, clause):
        self.steps.append(("a", self.wrap(clause)))
        if clause:
            self.current.append(list(dict.fromkeys(clause)))

    def delete(self, clause):
        """False when the mode forbids it: ``no-stale`` keeps every root literal."""
        s = set(clause)
        written = self.rng.sample(sorted(s), len(s))
        if len(s) <= 1:
            self.steps.append(("d", self.wrap(written)))
            return True
        new, present = oracle.remove_one(self.current, clause)
        if present and self.mode == "no-stale" and shrinks_root(self.current, new):
            return False
        self.current = new
        self.steps.append(("d", self.wrap(written)))
        return True

    def fresh(self):
        if self.max_var >= MAX_VAR:
            raise Abort
        self.max_var += 1
        return self.max_var

    def with_cands(self, p):
        return [d for d in self.current if -p in set(d)]

    def rup(self, c):
        return oracle.rup(self.current, c)

    def rat(self, c):
        return oracle.rat(self.current, c, c[0])

    def order_rest(self, c):
        rest = c[1:]
        self.rng.shuffle(rest)
        return c[:1] + rest

    # -- acceptable steps ------------------------------------------------

    def s_blocked(self):
        """Every resolvent tautological: a blocked clause, pivot first."""
        p = self.lit()
        c = [p]
        for d in self.with_cands(p):
            others = [l for l in d if l != -p and l != p]
            if not others:
                return
            l = self.rng.choice(others)
            if -l not in c:
                c.append(-l)
        if len(set(map(abs, c))) == len(c):
            self.add(self.order_rest(c))

    def s_vacuous(self):
        for _ in range(10):
            p = self.lit()
            if not self.with_cands(p):
                c = [p] + [l for l in self.clause_of(self.rng.randint(0, 2))
                           if abs(l) != abs(p)]
                self.add(c)
                return

    def s_extension(self):
        """Extended resolution: a definition on a variable nothing mentions."""
        a, b = self.clause_of(2)
        x = self.fresh()
        lines = [[x, -a, -b], [-x, a], [-x, b]]
        for c in lines:
            if self.rup(c) or self.rat(c):
                self.add(c)

    def s_search_rat(self):
        """RAT with real resolvents to check. Found by asking the oracle."""
        for _ in range(25):
            c = self.clause_of(self.rng.randint(1, 3))
            if self.with_cands(c[0]) and not self.rup(c) and self.rat(c):
                if non_tautological(self.with_cands(c[0]), c):
                    self.add(c)
                    return

    def s_enabled_by_deleting(self):
        """Not RAT now; delete the candidates in the way; RAT then."""
        for _ in range(12):
            c = self.clause_of(self.rng.randint(1, 3))
            if self.rup(c) or self.rat(c):
                continue
            cands = self.with_cands(c[0])
            if not cands or len(cands) > 4 or any(len(set(d)) < 2 for d in cands):
                continue
            for d in cands:
                if not self.delete(d):
                    break
            if self.rup(c) or self.rat(c):
                self.add(c)
            return

    def s_unit_at_root(self):
        """A RAT lemma with every literal but the pivot false at the root."""
        conflict, root = oracle.propagate(self.current)
        if conflict or not root:
            return
        for _ in range(10):
            p = self.lit()
            if p in root or -p in root:
                continue
            c = [p, *(-t for t in self.rng.sample(
                sorted(root), min(len(root), self.rng.randint(1, 2))))]
            if not self.rup(c) and self.rat(c):
                self.add(c)
                return

    def s_tautology(self):
        v = self.rng.randint(1, self.max_var)
        c = [v, -v]
        if self.rng.random() < .5:
            w = self.lit()
            if abs(w) != v:
                c.append(w)
        self.rng.shuffle(c)
        self.add(c)

    def s_rup(self):
        """A resolvent, or a copy of a clause present."""
        if not self.current:
            return
        d = self.rng.choice(self.current)
        if self.rng.random() < .2 or not d:
            if d:
                self.add(self.rng.sample(d, len(d)))
            return
        p = self.rng.choice(d)
        others = self.with_cands(p)
        if others:
            e = self.rng.choice(others)
            c = list({*d, *e} - {p, -p})
            if c and self.rup(c):
                self.add(c)

    def s_delete(self):
        roll = self.rng.random()
        if roll < .7 and self.current:
            d = self.rng.choice(self.current)
            if d:
                self.delete(d)
        elif roll < .85:
            units = [d for d in self.current if len(set(d)) == 1]
            if units:
                self.delete(self.rng.choice(units))
        else:
            self.delete(self.clause_of(self.rng.randint(0, 3)))  # likely absent

    def s_readd(self):
        """Delete a clause, then write it back."""
        pool = [d for d in self.current if len(set(d)) >= 2]
        if pool:
            d = self.rng.choice(pool)
            if self.delete(d) and (self.rup(d) or self.rat(d)):
                self.add(d)

    # -- steps meant to be rejected, each of which ends the proof ---------

    def t_copy_survives(self):
        """Two copies of a candidate; deleting one must not free the pivot."""
        pool = [d for d in self.current if len(set(d)) >= 2]
        if not pool:
            return
        d = self.rng.choice(pool)
        self.add(list(d))  # a copy of a clause present is RUP
        if not self.delete(d):
            return
        p = -self.rng.choice(d)
        for _ in range(8):
            c = [p] + [l for l in self.clause_of(self.rng.randint(0, 2))
                       if abs(l) != abs(p) and l not in d and -l not in d]
            if not self.rup(c) and not self.rat(c):
                self.steps.append(("a", self.wrap(c)))
                return

    def t_unit_survives(self):
        """A deleted unit is ignored, so it stays a candidate."""
        units = [d for d in self.current if len(set(d)) == 1]
        if not units:
            for _ in range(5):
                c = [self.lit()]
                if self.rup(c) or self.rat(c):
                    self.add(c)
                    units = [c]
                    break
        if not units:
            return
        u = self.rng.choice(units)
        self.delete(u)
        p = -u[0]
        for _ in range(8):
            c = [p] + [l for l in self.clause_of(self.rng.randint(0, 2))
                       if abs(l) != abs(p)]
            if not self.rup(c) and not self.rat(c):
                self.steps.append(("a", self.wrap(c)))
                return

    def t_pivot_order(self):
        """RAT on another literal, not on the one written first."""
        for _ in range(25):
            c = self.clause_of(self.rng.randint(2, 3))
            if self.rup(c) or self.rat(c):
                continue
            for i, l in enumerate(c[1:], 1):
                if oracle.rat(self.current, c, l):
                    if self.rng.random() < .3:
                        # the control: the same clause with the good pivot
                        self.add([l] + c[:i] + c[i + 1:])
                    else:
                        self.steps.append(("a", self.wrap(c)))
                    return

    def t_tautological_candidate(self):
        """A tautological lemma is a candidate: its resolvent is C itself."""
        v = self.rng.randint(1, self.max_var)
        self.add([v, -v])
        for _ in range(8):
            c = [-v] + [l for l in self.clause_of(self.rng.randint(0, 2))
                        if abs(l) != v]
            if not self.rup(c):
                self.steps.append(("a", self.wrap(c)))
                return

    def t_random(self):
        self.steps.append(("a", self.wrap(self.clause_of(self.rng.randint(1, 4)))))

    # -- aimed at a root literal's reason ---------------------------------

    def s_delete_reason(self):
        """Delete what a root literal rests on, then lean on its absence."""
        pool = [d for d in self.current if len(set(d)) >= 2]
        self.rng.shuffle(pool)
        for d in pool:
            before = oracle.propagate(self.current)
            new, _ = oracle.remove_one(self.current, d)
            if shrinks_root(self.current, new):
                self.delete(d)
                after = oracle.propagate(self.current)
                gone = sorted(before[1] - after[1])
                roll = self.rng.random()
                if roll < .65 and gone:
                    t = self.rng.choice(gone)
                    for e in self.with_cands(-t):
                        if len(set(e)) >= 2:
                            self.delete(e)
                    c = [-t]
                    if self.rng.random() < .3:
                        w = self.lit()
                        if abs(w) != abs(t):
                            c.append(w)
                    if self.rup(c) or self.rat(c):
                        self.add(c)
                elif roll < .85:
                    self.steps.append(("a", self.wrap(list(d))))
                    if not (self.rup(d) or self.rat(d)):
                        raise Abort
                    self.current.append(list(d))
                return

    # -- finishing --------------------------------------------------------

    def refute(self, budget=120):
        """A DPLL tree written as RUP lemmas, children deleted now and then."""
        emitted = [0]

        def rec(path):
            emitted[0] += 1
            if emitted[0] > budget:
                raise Abort
            lemma = [-l for l in path]
            conflict, assigned = oracle.propagate(self.current, path)
            if conflict:
                if path:
                    self.add(lemma)
                return lemma
            free = sorted({abs(l) for c in self.current for l in c}
                          - {abs(l) for l in assigned})
            left = rec(path + [free[0]])
            right = rec(path + [-free[0]])
            if path:
                self.add(lemma)
                if self.rng.random() < .25:
                    # the parent stands in for its children from here on
                    self.delete(left)
                    self.delete(right)
            return lemma

        rec([])
        self.steps.append(("a", []))

    def finish(self):
        rng = self.rng
        unsat = not oracle.satisfiable(self.current)
        roll = rng.random()
        if unsat and roll < .85:
            snapshot = (list(self.steps), [list(c) for c in self.current])
            try:
                self.refute()
            except Abort:
                self.steps, self.current = snapshot
                self.steps.append(("a", []))
        elif not unsat and roll < .8:
            self.steps.append(("a", []))
        # otherwise the proof stops short, with no empty clause

    def build(self):
        rng = self.rng
        weighted = ((self.s_blocked, 3), (self.s_vacuous, 2), (self.s_extension, 1),
                    (self.s_search_rat, 3), (self.s_enabled_by_deleting, 3),
                    (self.s_unit_at_root, 2), (self.s_tautology, 1), (self.s_rup, 2),
                    (self.s_delete, 3), (self.s_readd, 1))
        moves = [f for f, w in weighted for _ in range(w)]
        terminal = (self.t_copy_survives, self.t_unit_survives, self.t_pivot_order,
                    self.t_tautological_candidate, self.t_random)
        try:
            for _ in range(rng.randint(1, 6)):
                rng.choice(moves)()
            if self.mode == "stale":
                self.s_delete_reason()
                for _ in range(rng.randint(0, 2)):
                    rng.choice(moves)()
            if rng.random() < .4:
                rng.choice(terminal)()
            else:
                self.finish()
        except Abort:
            pass
        return self.formula, self.steps


# --------------------------------------------------------------------------
# the engines
# --------------------------------------------------------------------------


def _fields(r):
    return dict(
        ok=r.ok, reason=r.reason, steps=r.steps, rup_steps=r.rup_steps,
        rat_steps=r.rat_steps, deletions=r.deletions,
        ignored_deletions=r.ignored_deletions,
        resolvents_checked=r.resolvents_checked, failed_step=r.failed_step,
        failed_clause=(None if r.failed_clause is None
                       else tuple(to_dimacs(l) for l in r.failed_clause)),
        reached_empty=r.reached_empty)


def _real(engine, route):
    def run(clauses, steps, check_rat, apply_deletions):
        proof = proof_text(steps) if route == "text" else [
            (k, tuple(from_dimacs(l) for l in lits)) for k, lits in steps]
        formula = parse_dimacs(cnf_text(clauses))
        try:
            return _fields(check_proof(formula, proof, check_rat=check_rat,
                                       apply_deletions=apply_deletions, engine=engine))
        except ValueError as e:
            occurrences = sum(len(lits) for _, lits in steps)
            room = max(occurrences, len(proof) if route == "text" else 0)
            top = max((abs(l) for _, lits in steps for l in lits), default=0)
            return dict(raised=str(e), over_bound=top > formula.nvars + room)
    return run


def real_engines():
    """Python first, then native, by text and by list. Native is required."""
    try:
        import cdclkit_native
    except ImportError:
        sys.exit("no native checker: cdclkit_native is needed to run both engines")
    register_native(cdclkit_native)
    return [("python-text", _real("python", "text")),
            ("native-text", _real("native", "text")),
            ("python-list", _real("python", "list")),
            ("native-list", _real("native", "list"))]


# --------------------------------------------------------------------------
# the run
# --------------------------------------------------------------------------


def shrink(clauses, steps, still_fails):
    """Greedily remove steps, clauses and literals while the failure holds."""
    clauses = [list(c) for c in clauses]
    steps = [(k, list(l)) for k, l in steps]
    changed = True
    while changed:
        changed = False
        for i in range(len(steps) - 1, -1, -1):
            trial = steps[:i] + steps[i + 1:]
            if still_fails(clauses, trial):
                steps = trial
                changed = True
        for i in range(len(clauses) - 1, -1, -1):
            trial = clauses[:i] + clauses[i + 1:]
            if still_fails(trial, steps):
                clauses = trial
                changed = True
        for i, (kind, lits) in enumerate(steps):
            for j in range(len(lits) - 1, -1, -1):
                trial = list(steps)
                trial[i] = (kind, lits[:j] + lits[j + 1:])
                if still_fails(clauses, trial):
                    steps = trial
                    lits = trial[i][1]
                    changed = True
        for i, c in enumerate(clauses):
            for j in range(len(c) - 1, -1, -1):
                trial = list(clauses)
                trial[i] = c[:j] + c[j + 1:]
                if still_fails(trial, steps):
                    clauses = trial
                    c = trial[i]
                    changed = True
    return clauses, steps


def run_campaign(seed, instances, engines, want_examples=False, flavour="operational"):
    rng = random.Random(seed)
    tally = collections.Counter()
    mismatches = collections.Counter()
    examples = {}
    total_steps = 0
    for _ in range(instances):
        mode = "stale" if rng.random() < .3 else "no-stale"
        tally[f"instances_{mode.replace('-', '_')}"] += 1
        clauses, steps = Gen(rng, mode).build()
        found, runs, judged, results, sat = judge_case(clauses, steps, engines, flavour)
        total_steps += judged
        tally["checker_runs"] += runs
        count_coverage(clauses, steps, results, sat, tally)
        for label, kind in found:
            mismatches[label, kind] += 1
            if want_examples and (label, kind) not in examples:
                examples[label, kind] = (clauses, steps, mode)
    zero = [c for c in REQUIRED if not tally[c]]
    return dict(tally=tally, mismatches=mismatches, examples=examples,
                steps=total_steps, instances=instances, seed=seed,
                zero_categories=zero)


def print_report(rep):
    print(f"seed {rep['seed']}  instances {rep['instances']}  "
          f"steps judged {rep['steps']}  checker runs {rep['tally']['checker_runs']}")
    print("categories:")
    for key in sorted(rep["tally"]):
        print(f"  {key:50s} {rep['tally'][key]}")
    for label in ("unexplained",):
        lines = {k: v for (l, k), v in rep["mismatches"].items() if l == label}
        if lines:
            print(f"mismatches labelled {label}:")
            for kind, n in sorted(lines.items()):
                print(f"  {n:7d}  {kind}")
    if rep["zero_categories"]:
        print("CATEGORY NEVER REACHED: " + ", ".join(rep["zero_categories"]))


def print_examples(rep, engines, flavour="operational"):
    seen = set()
    for (label, kind), (clauses, steps, _) in sorted(rep["examples"].items()):
        if label in seen and label != "unexplained":
            continue
        seen.add(label)

        def holds(c, s, label=label, kind=kind):
            try:
                return any(x == (label, kind) for x in judge_case(c, s, engines, flavour)[0])
            except ValueError:
                return False

        c, s = shrink(clauses, steps, holds)
        print(f"smallest [{label}] {kind}\n  formula {c}\n  proof   {s}")


def stubs():
    """Each must be flagged. ``model_check`` with no options must not be."""

    def wrap(**options):
        return lambda c, s, r, a: model_check(c, s, r, a, **options)

    def accept_all(c, s, r, a):
        return dict(model_check(c, s, r, a), ok=True, reached_empty=True,
                    failed_step=-1, failed_clause=None)

    def reject_all(c, s, r, a):
        return dict(model_check(c, s, r, a), ok=False, reached_empty=False,
                    failed_step=1, failed_clause=None)

    def skewed(c, s, r, a):
        out = model_check(c, s, r, a)
        return dict(out, reason=out["reason"] + " ")

    good = wrap()

    def pair(fn):
        return [("stub-a", fn), ("stub-b", fn)]

    return {
        "accepts everything": pair(accept_all),
        "rejects everything": pair(reject_all),
        "tries every pivot": pair(wrap(any_pivot=True)),
        "RAT disabled": pair(lambda c, s, r, a: model_check(c, s, False, a)),
        "keeps deleted candidates": pair(wrap(keep_deleted_candidates=True)),
        "applies unit deletions": pair(wrap(apply_unit_deletions=True)),
        "treats a tautological resolvent as a failure": pair(wrap(tautology_fails=True)),
        "stale root (finding rat-1)": pair(wrap(stale=True)),
        "two engines that differ": [("stub-a", good), ("stub-b", skewed)],
        "raises instead of answering": pair(
            lambda c, s, r, a: dict(raised="stub", over_bound=False)),
    }


def self_test(seed, instances):
    failed = False
    good = lambda c, s, r, a: model_check(c, s, r, a)  # noqa: E731
    reference = run_campaign(seed, instances,
                             [("stub-a", good), ("stub-b", good)])
    clean = not reference["mismatches"] and not reference["zero_categories"]
    print(f"correct reference: {sum(reference['mismatches'].values())} mismatches, "
          f"zero categories {reference['zero_categories']} -> "
          f"{'clean, as it must be' if clean else 'FAIL'}")
    if reference["mismatches"]:
        for (label, kind), n in reference["mismatches"].most_common(6):
            print(f"    {n} [{label}] {kind}")
    failed |= not clean
    for name, group in stubs().items():
        rep = run_campaign(seed, instances, group)
        n = sum(rep["mismatches"].values())
        verdict = "flagged" if n else "NOT FLAGGED"
        print(f"{name}: {n} mismatches -> {verdict}")
        failed |= not n
    empty = run_campaign(seed, 0, [("stub-a", good), ("stub-b", good)])
    print(f"zero instances: {len(empty['zero_categories'])} categories at zero -> "
          f"{'flagged' if empty['zero_categories'] else 'NOT FLAGGED'}")
    failed |= not empty["zero_categories"]
    print("self-test " + ("FAILED" if failed else "passed"))
    return 1 if failed else 0


FINDINGS = [
    {"id": "rat-1", "status": "fixed", "severity": "Critical",
     "summary": "ok=True on a satisfiable formula: the root assignment outlives "
                "a deleted non-unit reason, so a RAT lemma falsified by the stale "
                "assignment sets root_conflict. F = 1 / -1 2, proof "
                "`d -1 2 0`, `-2 0`, `0`. Both engines."},
    {"id": "rat-2", "status": "fixed", "severity": "Bug",
     "summary": "Engines disagree on failed_clause for a rejected step that "
                "repeats a literal: Python reports it deduplicated, native as "
                "written."},
    {"id": "rat-4", "status": "fixed", "severity": "Bug",
     "summary": "A proof naming a fresh variable above the literal bound raises "
                "ValueError instead of being checked: `8 0` on a one-variable "
                "formula is vacuously RAT. The bound depends on the proof's text "
                "length, so a comment line changes the outcome, and a list of "
                "steps gets a tighter bound than the same proof as text."},
    {"id": "rat-3", "status": "fixed", "severity": "Note",
     "summary": "A reason-clause deletion splits dratify's documented flavour "
                "from drat-trim's operational one, and ignored_deletions and "
                "report() call absent-clause deletions 'unit deletions ignored'."},
]

NOT_CHECKED = [
    "drat-trim itself: it is not installed here. The operational flavour is the "
    "oracle's approximation of it, and dratify's rule is that same test.",
    "steps after the empty clause: the generator cuts there, as the checkers do.",
    "ok=False reasons, beyond requiring the engines to agree on the text.",
    "failed_step and resolvents_checked when deletions are disabled are compared; "
    "ignored_deletions in that configuration is compared only between engines.",
    "resolvents_checked on a rejected step is checked against bounds (1 to the "
    "number of non-tautological candidates), not exactly, because the oracle "
    "fixes no candidate order.",
    "proofs from real solvers: every proof here is generated.",
    "binary DRAT, which dratify does not read, and header or parser edge cases, "
    "which belong to other corners.",
    "the Rust crate's public API directly: native runs go through cdclkit_native "
    "and dratify's check_proof.",
]


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--seed", type=int, default=DEFAULT_SEED)
    ap.add_argument("--instances", type=int, default=DEFAULT_INSTANCES)
    ap.add_argument("--self-test", action="store_true",
                    help="run the harness against deliberately wrong checkers")
    ap.add_argument("--no-shrink", action="store_true",
                    help="skip shrinking one example per mismatch label")
    ap.add_argument("--flavour", default="operational", choices=oracle.FLAVOURS,
                    help="the deletion rule to judge against. operational is what "
                         "dratify documents")
    ap.add_argument("--write-results", action="store_true",
                    help=f"write campaign/results/{CORNER}.json")
    args = ap.parse_args(argv)
    if args.self_test:
        return self_test(args.seed, min(args.instances, 400))
    engines = real_engines()
    t0 = time.monotonic()
    rep = run_campaign(args.seed, args.instances, engines,
                       want_examples=not args.no_shrink, flavour=args.flavour)
    runtime = time.monotonic() - t0
    print_report(rep)
    if not args.no_shrink:
        print_examples(rep, engines, args.flavour)
    print(f"runtime {runtime:.1f}s")
    if args.write_results:
        counts = {k: rep["tally"][k] for k in sorted(rep["tally"])}
        for (label, kind), n in sorted(rep["mismatches"].items()):
            counts[f"mismatch[{label}] {kind}"] = n
        path = pathlib.Path(__file__).parent / "results" / f"{CORNER}.json"
        path.write_text(json.dumps(dict(
            corner=CORNER, seeds=[args.seed], instances=args.instances,
            steps=rep["steps"], per_category_counts=counts,
            runtime_seconds=round(runtime, 1), findings=FINDINGS,
            not_checked=NOT_CHECKED), indent=2) + "\n", encoding="utf-8")
        print(f"wrote {path}")
    if rep["zero_categories"]:
        return 2
    return 1 if rep["mismatches"] else 0


if __name__ == "__main__":
    sys.exit(main())
