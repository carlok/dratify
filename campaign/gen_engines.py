# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Python against native: every field of CheckResult, under all four flag pairs.

For each random formula and proof, and each of (check_rat, apply_deletions):

1. the two engines must agree on every field;
2. ``ok=True`` must mean the oracle finds the formula unsatisfiable;
3. each engine must match a reference built on the oracle's ``rup`` and ``rat``
   under the semantics dratify documents: every deletion happens, except that
   a clause with at most one distinct literal stays (the oracle's "length-one"
   flavour), and the proof is over once top-level propagation conflicts.

When an engine differs from that reference it is compared with a second one,
which also keeps every literal once assigned at the top level, after the clause
that implied it is deleted. That is what dratify does, so a mismatch explained
by it is labelled engines-1. It is still a mismatch and the run still fails.

    python -m campaign.gen_engines [--seed N] [--instances N] [--write-results]
    python -m campaign.gen_engines --self-test
"""

from __future__ import annotations

import argparse
import collections
import json
import os
import random
import sys
import time

import dratify
from dratify import from_dimacs, parse_dimacs, parse_proof, register_native, to_dimacs
from dratify.proof import MemoryProof

from campaign import oracle

DEFAULT_SEED = 20261108
DEFAULT_INSTANCES = 80000
COMBOS = ((True, True), (True, False), (False, True), (False, False))

FIELDS = ("ok", "reason", "steps", "rup_steps", "rat_steps", "deletions",
          "ignored_deletions", "resolvents_checked", "failed_step",
          "failed_clause", "reached_empty")

REFUTED = "input formula is refuted by unit propagation alone"
VERIFIED = "empty clause derived and every step verified"
NO_EMPTY = "every step verified, but the proof never derives the empty clause"
NOT_RAT = ("clause is neither RUP nor RAT with respect to the clauses "
           "available at this point")
NOT_RUP = "clause is not RUP (RAT checking disabled)"

FINDINGS = {
    "engines-1": ("Critical", "ok=True on satisfiable formulas: deleting a "
                  "clause that implied a root literal keeps the literal but "
                  "drops the clause from RAT candidates; both engines"),
    "engines-2": ("Bug", "failed_clause differs between engines when the "
                  "failed step repeats a literal: native returns the step "
                  "undeduplicated"),
    "engines-3": ("Bug", "valid proofs raise ValueError when a fresh variable "
                  "index exceeds the formula's count plus the proof's length; "
                  "both engines"),
}

# Every category this generator claims to reach. Zero in any fails the run.
REQUIRED = (
    "instances", "steps_judged", "field_comparisons",
    "accepted", "rejected", "accepted_by_a_proof",
    "accepted_by_a_proof_with_rat", "accepted_by_a_proof_with_deletion",
    "sticky_additions_past_a_deletion", "header_declares_unused_variables",
    "rejected_after_resolvents_and_deletion",
    "TT.accepted", "TT.rejected", "TF.accepted", "TF.rejected",
    "FT.accepted", "FT.rejected", "FF.accepted", "FF.rejected",
    "rup_steps", "rat_steps", "rat_nonvacuous", "rat_vacuous",
    "resolvents_checked", "rejected_after_resolvents",
    "rejected_rat_disabled", "rejected_empty_claim",
    "deletions_applied", "ignored_length_le_one", "ignored_absent",
    "deletions_skipped_by_flag", "root_reason_deleted",
    "gen.repeated_literals", "gen.long_repeated_literals", "gen.empty_formula",
    "gen.repeat_step", "gen.garbage",
    "gen.fresh_variable", "gen.tautological_lemma", "gen.flipped",
    "gen.after_empty", "gen.refutation", "gen.truncated",
    "accepted_with_fresh_variable", "accepted_with_rat_and_deletion",
    "failed_clause_with_repeat", "input_refuted_by_propagation",
    "input_tautology_dropped", "auto_engine_compared",
    "list_path_compared", "memoryproof_path_compared",
    "replay_crosschecks", "sat_formulas", "unsat_formulas",
)


# --------------------------------------------------------------------------
# the reference, in the oracle's terms
# --------------------------------------------------------------------------


def _distinct(lits):
    return list(dict.fromkeys(lits))


def _judge_rat(current, formula, clause):
    """(all resolvents RUP over `formula`, candidates that are not tautologies).

    Candidates come from `current` only: a retained literal is an assignment,
    not a clause, and RAT is defined over the clauses present.
    """
    pivot = clause[0]
    lits = set(clause)
    verdict = True
    candidates = 0
    for d in current:
        if -pivot not in d:
            continue
        rest = set(d) - {-pivot}
        if not any(-l in lits for l in rest):
            candidates += 1
        if not oracle.rup(formula, lits | rest):
            verdict = False
    return verdict, candidates


def reference(formula, steps, check_rat, apply_deletions, keep_root):
    """What a result must be. `keep_root` is the engines-1 explanation."""
    out = dict(ok=False, reason="", steps=0, rup_steps=0, rat_steps=0,
               deletions=0, ignored_deletions=0, failed_step=-1,
               failed_clause=None, reached_empty=False,
               resolvents_lo=0, resolvents_hi=0, sticky_rup=0,
               stuck_at=None, rat_nonvacuous=0, rat_vacuous=0,
               ignored_short=0, ignored_absent=0, skipped=0, root_reason=0)
    conflict, assigned = oracle.propagate(formula)
    if conflict:
        out.update(ok=True, reached_empty=True, reason=REFUTED)
        return out
    current = [list(c) for c in formula]
    retained = set(assigned) if keep_root else set()
    sticky = False
    for i, (kind, lits) in enumerate(steps, 1):
        out["steps"] = i
        clause = _distinct(lits)
        if kind == "d":
            if len(clause) <= 1:
                out["ignored_deletions"] += 1
                out["ignored_short"] += 1
            elif not apply_deletions:
                out["skipped"] += 1
            else:
                if not sticky and oracle.is_pseudo_unit(current, clause):
                    out["root_reason"] += 1
                current, present = oracle.remove_one(current, clause)
                if present:
                    out["deletions"] += 1
                else:
                    out["ignored_deletions"] += 1
                    out["ignored_absent"] += 1
            continue
        against = current + [[l] for l in sorted(retained)]
        rup = sticky or oracle.rup(against, clause)
        if sticky and not oracle.rup(against, clause):
            out["sticky_rup"] += 1
        if rup:
            out["rup_steps"] += 1
        else:
            good, candidates = False, 0
            if check_rat and clause:
                good, candidates = _judge_rat(current, against, clause)
                if not keep_root and good != oracle.rat(current, clause, clause[0]):
                    raise AssertionError(f"reference and oracle.rat differ on {clause}")
            if good:
                out["rat_steps"] += 1
                out["resolvents_lo"] += candidates
                out["resolvents_hi"] += candidates
                out["rat_nonvacuous" if candidates else "rat_vacuous"] += 1
            else:
                # stops at the first failure, in an order nothing documents
                out["resolvents_lo"] += 1 if candidates else 0
                out["resolvents_hi"] += candidates
                out["failed_step"] = i
                out["failed_clause"] = frozenset(clause)
                out["reason"] = NOT_RAT if check_rat else NOT_RUP
                out["stuck_at"] = current
                return out
        if not clause:
            out.update(ok=True, reached_empty=True, reason=VERIFIED)
            return out
        current.append(clause)
        if not sticky:
            sticky, assigned = oracle.propagate(
                current + [[l] for l in sorted(retained)])
            if keep_root:
                retained |= assigned
    out["reason"] = NO_EMPTY
    return out


def compare_with_reference(result, ref):
    """The fields of an engine's result that the reference forbids."""
    bad = []
    for field in ("ok", "reason", "steps", "rup_steps", "rat_steps", "deletions",
                  "ignored_deletions", "failed_step", "reached_empty"):
        if result[field] != ref[field]:
            bad.append(field)
    if not ref["resolvents_lo"] <= result["resolvents_checked"] <= ref["resolvents_hi"]:
        bad.append("resolvents_checked")
    fc = result["failed_clause"]
    got = None if fc is None else frozenset(to_dimacs(l) for l in fc)
    if got != ref["failed_clause"]:
        bad.append("failed_clause")
    return bad


# --------------------------------------------------------------------------
# generation
# --------------------------------------------------------------------------


def _clause(rng, nv, kmax=3, kmin=1):
    k = rng.randint(min(kmin, nv), min(kmax, nv))
    return [v if rng.random() < 0.5 else -v
            for v in rng.sample(range(1, nv + 1), k)]


def gen_formula(rng, tags):
    """Raw DIMACS clauses, before the parser normalises them."""
    n = rng.randint(2, 6)
    if rng.random() < 0.03:
        tags["gen.empty_formula"] += 1
        return n, []
    shape = rng.choice(("dense", "dense", "dense", "dense", "random", "random",
                        "chain", "chain", "chain"))
    clauses = []
    if shape == "dense":
        # no units, so propagation alone does not end it before the proof starts
        for _ in range(90):
            clauses.append(_clause(rng, n, 3, 2))
            if not oracle.satisfiable(clauses):
                break
    elif shape == "random":
        clauses = [_clause(rng, n, 4, 2) for _ in range(rng.randint(1, 3 * n))]
    else:
        order = rng.sample(range(1, n + 1), n)
        lits = [v if rng.random() < 0.5 else -v for v in order]
        clauses.append([lits[0]])
        for a, b in zip(lits, lits[1:]):
            clauses.append([-a, b])
        clauses += [_clause(rng, n, 4, 2) for _ in range(rng.randint(0, n))]
    roll = rng.random()
    if roll < 0.08:
        v = rng.randint(1, n)
        clauses.append([v, -v])
        tags["gen.input_tautology"] += 1
    elif roll < 0.16:
        c = _clause(rng, n)
        clauses.append(c + [c[0]])
        tags["gen.input_repeated_literal"] += 1
    elif roll < 0.24 and clauses:
        clauses.append(list(rng.choice(clauses)))
        tags["gen.input_duplicate_clause"] += 1
    elif roll < 0.26:
        clauses.append([])
        tags["gen.input_empty_clause"] += 1
    elif roll < 0.30:
        v = rng.randint(1, n)
        clauses += [[v], [-v]]
        tags["gen.input_contradictory_units"] += 1
    if shape != "chain":
        rng.shuffle(clauses)
    return n, clauses


def _refutation(current, nv):
    """A RUP chain ending in the empty clause, by case split on `current`."""
    current = [list(c) for c in current]
    out = []

    def go(assumed):
        conflict, assigned = oracle.propagate(current, assumed)
        if conflict:
            return
        free = [v for v in range(1, nv + 1)
                if v not in assigned and -v not in assigned]
        if free:
            v = free[0]
            go(assumed + [v])
            go(assumed + [-v])
        lemma = [-l for l in assumed]
        out.append(lemma)
        current.append(lemma)

    go([])
    return out if out and not out[-1] else None


def gen_proof(rng, n, formula, tags):
    current = [list(c) for c in formula]
    steps = []
    fresh = n + 1
    last_fresh = n + 3

    def add(lits):
        steps.append(("a", list(lits)))
        current.append(_distinct(lits))

    def delete(lits):
        nonlocal current
        steps.append(("d", list(lits)))
        if len(set(lits)) > 1:
            current, _ = oracle.remove_one(current, lits)

    for _ in range(rng.randint(0, 9)):
        nv = max(n, fresh - 1)
        action = rng.choices(
            ("rup", "rat", "fresh", "taut", "del", "del_unit", "del_absent",
             "reason", "repeat", "rep_lit", "long_rep", "garbage", "flip",
             "empty_del"),
            (14, 10, 5, 2, 10, 3, 3, 4, 4, 5, 1, 3, 2, 1))[0]
        if action == "rup":
            for _ in range(6):
                c = _clause(rng, nv)
                if oracle.rup(current, c):
                    add(c)
                    tags["gen.rup"] += 1
                    break
        elif action == "rat":
            for _ in range(8):
                c = _clause(rng, nv)
                if oracle.rup(current, c):
                    continue
                rng.shuffle(c)
                good = [p for p in c if oracle.rat(current, c, p)]
                if good:
                    p = rng.choice(good)
                    add([p] + [l for l in c if l != p])
                    tags["gen.rat"] += 1
                    break
        elif action == "fresh" and fresh <= last_fresh:
            a = rng.randint(1, n) * rng.choice((1, -1))
            x = fresh
            fresh += 1
            add([x, -a])
            if rng.random() < 0.7:
                add([-x, a])
            tags["gen.fresh_variable"] += 1
        elif action == "taut":
            v = rng.randint(1, nv)
            add([v, -v] if rng.random() < 0.5 else [-v, v])
            tags["gen.tautological_lemma"] += 1
        elif action == "del":
            cands = [c for c in current if len(set(c)) > 1]
            if cands:
                c = list(rng.choice(cands))
                rng.shuffle(c)
                delete(c)
                tags["gen.deletion"] += 1
        elif action == "del_unit":
            cands = [c for c in current if len(set(c)) == 1]
            if cands:
                delete(list(rng.choice(cands)))
                tags["gen.unit_deletion"] += 1
        elif action == "del_absent":
            c = _clause(rng, nv)
            if len(c) > 1 and sorted(c) not in map(sorted, current):
                delete(c)
                tags["gen.absent_deletion"] += 1
        elif action == "reason":
            # delete what implied a root literal, then deny that literal
            _, assigned = oracle.propagate(current)
            cands = [c for c in current
                     if len(set(c)) > 1 and oracle.is_pseudo_unit(current, c)]
            if cands:
                c = rng.choice(cands)
                true = [l for l in c if l in assigned]
                delete(list(c))
                tags["gen.reason_deletion"] += 1
                if true and rng.random() < 0.5:
                    add([-true[0]])
                    tags["gen.deny_retained"] += 1
        elif action == "repeat" and steps:
            kind, lits = rng.choice(steps)
            (delete if kind == "d" else add)(list(lits))
            tags["gen.repeat_step"] += 1
        elif action == "rep_lit":
            c = _clause(rng, nv)
            c.insert(rng.randint(1, len(c)), rng.choice(c))
            if rng.random() < 0.3:
                delete(c)
            elif oracle.rup(current, c) or oracle.rat(current, c, c[0]):
                add(c)
            else:
                steps.append(("a", c))    # dies here, with a repeat in it
            tags["gen.repeated_literals"] += 1
        elif action == "long_rep":
            # over 16 literals, where Rust removes repeats by another path
            c = _clause(rng, nv)
            longer = (c * 24)[:rng.randint(17, 24)]
            if rng.random() < 0.3:
                delete(longer)
            elif oracle.rup(current, c) or oracle.rat(current, c, c[0]):
                add(longer)
            else:
                steps.append(("a", longer))
            tags["gen.long_repeated_literals"] += 1
        elif action == "garbage":
            steps.append(("a", _clause(rng, nv)))
            tags["gen.garbage"] += 1
        elif action == "flip":
            rupped = [c for k, c in steps if k == "a" and c]
            if rupped:
                c = list(rng.choice(rupped))
                c[rng.randrange(len(c))] *= -1
                steps.append(("a", c))
                tags["gen.flipped"] += 1
        elif action == "empty_del":
            steps.append(("d", []))
            tags["gen.empty_deletion"] += 1

    ending = rng.choices(("refute", "empty", "none", "trailing", "past_conflict"),
                         (12, 2, 3, 1, 2))[0]
    if ending == "past_conflict":
        # conflict at the top level, then delete what made it, then go on
        proof = None
        if not oracle.satisfiable(current):
            proof = _refutation(current, max(n, fresh - 1))
        if proof is not None and len(proof) > 1:
            for c in proof[:-1]:
                add(c)
            for _ in range(3):
                cands = [c for c in current if len(set(c)) > 1]
                if cands:
                    delete(list(rng.choice(cands)))
            tags["gen.deleted_past_conflict"] += 1
        steps.append(("a", _clause(rng, n)))
        steps.append(("a", []))
    elif ending == "refute":
        proof = None
        if not oracle.satisfiable(current):
            proof = _refutation(current, max(n, fresh - 1))
        if proof is None:
            steps.append(("a", []))
        else:
            steps.extend(("a", c) for c in proof)
            tags["gen.refutation"] += 1
    elif ending == "empty":
        steps.append(("a", []))
    elif ending == "trailing":
        steps.append(("a", []))
        steps.append(("a", _clause(rng, n)))
        steps.append(("d", _clause(rng, n)))
        tags["gen.after_empty"] += 1
    else:
        tags["gen.truncated"] += 1

    if rng.random() < 0.01:
        # a fresh variable with a gap before it, past what the bound allows
        steps.insert(0, ("a", [n + 40]))
        tags["gen.fresh_gap"] += 1
    return steps


def formula_text(declared, clauses):
    return f"p cnf {declared} {len(clauses)}\n" + "".join(
        " ".join(map(str, c)) + " 0\n" for c in clauses)


def proof_text(steps):
    lines = []
    for kind, lits in steps:
        body = " ".join(map(str, lits))
        lines.append(("d " if kind == "d" else "") + (body + " 0" if lits else "0"))
    return "\n".join(lines) + "\n" if lines else ""


def internal(steps):
    return [(k, tuple(from_dimacs(l) for l in lits)) for k, lits in steps]


# --------------------------------------------------------------------------
# running an engine
# --------------------------------------------------------------------------


def _fields(r):
    return {f: getattr(r, f) for f in FIELDS}


def real_engine(engine):
    def run(cnf, proof, steps, check_rat, apply_deletions):
        return _fields(dratify.check_proof(cnf, proof, check_rat=check_rat,
                                           apply_deletions=apply_deletions,
                                           engine=engine))
    return run


def attempt(run, *args):
    """A result, or what was raised. A Rust panic is a BaseException."""
    try:
        return run(*args)
    except KeyboardInterrupt:
        raise
    except BaseException as e:      # noqa: BLE001 -- that is the point
        return {"raised": f"{type(e).__name__}: {e}"}


# --------------------------------------------------------------------------
# judging one instance
# --------------------------------------------------------------------------


class Tally:
    def __init__(self):
        self.counts = collections.Counter()
        self.mismatches = collections.Counter()
        self.examples = {}
        self.known = {}

    def flag(self, label, finding, detail):
        self.mismatches[label] += 1
        if finding:
            self.known[label] = finding
        self.examples.setdefault(label, []).append(detail)
        del self.examples[label][3:]

    @property
    def unexplained(self):
        return {k: v for k, v in self.mismatches.items() if k not in self.known}


def judge(n, raw, steps, engines, tally, rng, compare_paths=True):
    """Everything below is asked of every instance and every flag pair."""
    c = tally.counts
    text_f, text_p = formula_text(n, raw), proof_text(steps)
    cnf = parse_dimacs(text_f)
    snapshot = list(cnf.clauses)
    formula = [[to_dimacs(l) for l in cl] for cl in cnf.clauses]
    sat = oracle.satisfiable(formula)
    if sat != oracle.satisfiable(raw):
        tally.flag("parser-changed-satisfiability", None, (text_f,))
    c["instances"] += 1
    c["sat_formulas" if sat else "unsat_formulas"] += 1
    if len(formula) != len(raw):
        c["input_tautology_dropped"] += any(
            len(set(cl)) != len({abs(l) for l in cl}) for cl in raw)
    if oracle.propagate(formula)[0]:
        c["input_refuted_by_propagation"] += 1
    mentions_fresh = any(abs(l) > n for _, lits in steps for l in lits)
    if cnf.nvars > max((abs(l) for cl in raw for l in cl), default=0):
        c["header_declares_unused_variables"] += 1

    for check_rat, apply_deletions in COMBOS:
        tag = "TF"[not check_rat] + "TF"[not apply_deletions]
        where = (text_f, text_p, f"check_rat={check_rat}",
                 f"apply_deletions={apply_deletions}")
        args = (cnf, text_p, steps, check_rat, apply_deletions)
        py = attempt(engines["python"], *args)
        rs = attempt(engines["native"], *args)
        doc = reference(formula, steps, check_rat, apply_deletions, False)

        if "raised" in py or "raised" in rs:
            if py != rs:
                tally.flag("engine-diff:raised", None, where + (py, rs))
            bound = "can account for at most" in str(py.get("raised"))
            if bound:
                tally.flag("refused-fresh-variable", "engines-3", where + (py,))
                c["bound_refusals"] += 1
            else:
                tally.flag("raised", None, where + (py, rs))
            continue

        # 1. the engines against each other
        for field in FIELDS:
            c["field_comparisons"] += 1
            if py[field] == rs[field]:
                continue
            if (field == "failed_clause"
                    and py[field] is not None and rs[field] is not None
                    and tuple(_distinct(rs[field])) == py[field]
                    and len(rs[field]) != len(py[field])):
                tally.flag("engine-diff:failed_clause-repeat", "engines-2",
                           where + (py[field], rs[field]))
            else:
                tally.flag(f"engine-diff:{field}", None, where + (py, rs))

        # 2. the end-to-end question, and the invariant under it
        for name, r in (("python", py), ("native", rs)):
            if r["ok"] and not r["reached_empty"]:
                tally.flag("ok-without-empty", None, where + (name,))
            if bool(r["ok"]) and sat:
                explained = compare_with_reference(
                    r, reference(formula, steps, check_rat, apply_deletions, True)) == []
                tally.flag(f"sat-accepted:{tag}:{name}",
                           "engines-1" if explained else None, where)

        # 3. each engine against the oracle's reading of the documentation
        for name, r in (("python", py), ("native", rs)):
            bad = compare_with_reference(r, doc)
            if not bad:
                continue
            ext = reference(formula, steps, check_rat, apply_deletions, True)
            if compare_with_reference(r, ext) == []:
                tally.flag(f"retained-root:{tag}:{name}", "engines-1", where + (bad,))
                if doc["stuck_at"] is not None:
                    bad_step = steps[doc["failed_step"] - 1][1]
                    c["accepted_not_acceptable"] += 1
                    if not oracle.preserves_sat(doc["stuck_at"], bad_step):
                        c["accepted_not_sat_preserving"] += 1
            else:
                tally.flag(f"vs-reference:{name}:{','.join(bad)}", None,
                           where + (r, {k: doc[k] for k in doc if k != "stuck_at"}))

        # what ran, from what the engines reported and the oracle agreed
        c["steps_judged"] += py["steps"]
        c["accepted" if py["ok"] else "rejected"] += 1
        c[f"{tag}.{'accepted' if py['ok'] else 'rejected'}"] += 1
        c["rup_steps"] += py["rup_steps"]
        c["rat_steps"] += py["rat_steps"]
        c["resolvents_checked"] += py["resolvents_checked"]
        c["deletions_applied"] += py["deletions"]
        c["ignored_length_le_one"] += doc["ignored_short"]
        c["ignored_absent"] += doc["ignored_absent"]
        c["deletions_skipped_by_flag"] += doc["skipped"]
        c["root_reason_deleted"] += doc["root_reason"]
        c["rat_nonvacuous"] += doc["rat_nonvacuous"]
        c["rat_vacuous"] += doc["rat_vacuous"]
        c["sticky_additions_past_a_deletion"] += doc["sticky_rup"]
        if py["failed_step"] > 0:
            if py["resolvents_checked"] and check_rat:
                c["rejected_after_resolvents"] += 1
            if not check_rat:
                c["rejected_rat_disabled"] += 1
            if py["resolvents_checked"] and py["deletions"]:
                c["rejected_after_resolvents_and_deletion"] += 1
            failed = steps[py["failed_step"] - 1][1] if py["failed_step"] <= len(steps) else [0]
            if not failed:
                c["rejected_empty_claim"] += 1
            if len(set(failed)) != len(failed):
                c["failed_clause_with_repeat"] += 1
        if py["ok"] and py["steps"]:
            c["accepted_by_a_proof"] += 1
            if py["rat_steps"]:
                c["accepted_by_a_proof_with_rat"] += 1
            if py["deletions"]:
                c["accepted_by_a_proof_with_deletion"] += 1
        if py["ok"] and mentions_fresh:
            c["accepted_with_fresh_variable"] += 1
        if py["ok"] and py["rat_steps"] and py["deletions"]:
            c["accepted_with_rat_and_deletion"] += 1

        # the oracle's own walk, as a check on the reference above
        if check_rat and apply_deletions and doc["steps"] and not doc["sticky_rup"]:
            walk, _ = oracle.replay(formula, steps[:doc["steps"]], "length-one")
            walked_ok = walk[-1].acceptable
            if walked_ok != (doc["failed_step"] < 0):
                tally.flag("reference-disagrees-with-replay", None, where)
            c["replay_crosschecks"] += 1

        # the other ways to hand over the same proof
        if compare_paths:
            compare_other_paths(cnf, steps, py, rs, engines, where, tally, rng)

    if list(cnf.clauses) != snapshot:
        tally.flag("checker-mutated-formula", None, (text_f, text_p))


def compare_other_paths(cnf, steps, py, rs, engines, where, tally, rng):
    """A list of steps, a MemoryProof and engine="auto" must say the same."""
    c = tally.counts
    check_rat, apply_deletions = where[2].endswith("True"), where[3].endswith("True")
    roll = rng.random()
    if roll < 0.25:
        proof, path = internal(steps), "list"
        c["list_path_compared"] += 1
    elif roll < 0.5:
        proof, path = MemoryProof(), "memoryproof"
        proof.steps = internal(steps)
        c["memoryproof_path_compared"] += 1
    else:
        return
    for name, text_result in (("python", py), ("native", rs)):
        r = attempt(engines[name], cnf, proof, steps, check_rat, apply_deletions)
        if "raised" in r:
            if "can account for at most" in r["raised"]:
                tally.flag("refused-fresh-variable", "engines-3", where + (path, r))
                c["bound_refusals_list_only"] += 1
            else:
                tally.flag(f"path-raised:{path}", None, where + (r,))
        elif r != text_result:
            tally.flag(f"path-diff:{path}:{name}", None, where + (r, text_result))
    if "auto" in engines:
        r = attempt(engines["auto"], cnf, proof, steps, check_rat, apply_deletions)
        c["auto_engine_compared"] += 1
        if "raised" not in r and r != rs:
            tally.flag("auto-is-not-native", None, where + (r, rs))


def sweep(seed, instances, engines, compare_paths=True):
    rng = random.Random(seed)
    tally = Tally()
    tags = tally.counts
    for _ in range(instances):
        n, raw = gen_formula(rng, tags)
        # a header may declare more than the formula uses; Rust sizes by it
        declared = n + rng.choice((0, 0, 0, 0, 2, 50)) if raw else 0
        cnf = parse_dimacs(formula_text(declared, raw))
        formula = [[to_dimacs(l) for l in cl] for cl in cnf.clauses]
        steps = gen_proof(rng, n, formula, tags)
        judge(declared, raw, steps, engines, tally, rng, compare_paths)
    return tally


def missing_categories(tally):
    return [k for k in REQUIRED if not tally.counts[k]]


# --------------------------------------------------------------------------
# the native checker must be this checkout's
# --------------------------------------------------------------------------


def native_engines():
    """Register the native checker, proving it was built from this `rust/`."""
    import cdclkit_native

    register_native(cdclkit_native)
    here = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    want = os.path.join(here, "rust", "src", "checker.rs").encode()
    folder = os.path.dirname(cdclkit_native.__file__)
    libs = [f for f in os.listdir(folder) if f.endswith((".so", ".pyd", ".dylib"))]
    if not libs:
        raise SystemExit(f"no compiled library in {folder}")
    with open(os.path.join(folder, libs[0]), "rb") as fh:
        if want not in fh.read():
            raise SystemExit(f"{libs[0]} does not embed {want.decode()}: it was "
                             "not built from this checkout; run tests/build_native.sh")
    return {"python": real_engine("python"), "native": real_engine("native"),
            "auto": real_engine("auto")}, want.decode()


# --------------------------------------------------------------------------
# self-test: the harness must flag checkers known to be wrong
# --------------------------------------------------------------------------


def _as_result(ref, check_clause=None):
    fc = ref["failed_clause"]
    return dict(ok=ref["ok"], reason=ref["reason"], steps=ref["steps"],
                rup_steps=ref["rup_steps"], rat_steps=ref["rat_steps"],
                deletions=ref["deletions"],
                ignored_deletions=ref["ignored_deletions"],
                resolvents_checked=ref["resolvents_lo"],
                failed_step=ref["failed_step"],
                failed_clause=check_clause if check_clause is not None else
                (None if fc is None else tuple(from_dimacs(l) for l in sorted(fc))),
                reached_empty=ref["reached_empty"])


def _ref(cnf, steps, cr, ad, keep_root=False):
    formula = [[to_dimacs(l) for l in c] for c in cnf.clauses]
    return reference(formula, steps, cr, ad, keep_root)


def _correct(cnf, proof, steps, cr, ad):
    return _as_result(_ref(cnf, steps, cr, ad))


def _accept_all(cnf, proof, steps, cr, ad):
    return dict(_correct(cnf, proof, steps, cr, ad), ok=True, reached_empty=True,
                failed_step=-1, failed_clause=None, reason=VERIFIED)


def _reject_all(cnf, proof, steps, cr, ad):
    return dict(_correct(cnf, proof, steps, cr, ad), ok=False, reached_empty=False,
                reason=NOT_RAT, failed_step=1)


def _ok_without_empty(cnf, proof, steps, cr, ad):
    r = _correct(cnf, proof, steps, cr, ad)
    return dict(r, ok=True, reason=VERIFIED) if r["reason"] == NO_EMPTY else r


def _ignores_check_rat(cnf, proof, steps, cr, ad):
    return _as_result(_ref(cnf, steps, True, ad))


def _ignores_apply_deletions(cnf, proof, steps, cr, ad):
    return _as_result(_ref(cnf, steps, cr, True))


def _resolvents_off(cnf, proof, steps, cr, ad):
    r = _correct(cnf, proof, steps, cr, ad)
    return dict(r, resolvents_checked=r["resolvents_checked"] + (r["rat_steps"] > 0))


def _rup_rat_swapped(cnf, proof, steps, cr, ad):
    r = _correct(cnf, proof, steps, cr, ad)
    return dict(r, rup_steps=r["rat_steps"], rat_steps=r["rup_steps"])


def _reason_off(cnf, proof, steps, cr, ad):
    r = _correct(cnf, proof, steps, cr, ad)
    return dict(r, reason=r["reason"] + " ")


def _failed_clause_raw(cnf, proof, steps, cr, ad):
    r = _correct(cnf, proof, steps, cr, ad)
    if r["failed_step"] > 0:
        raw = steps[r["failed_step"] - 1][1]
        distinct = _distinct(raw)
        r["failed_clause"] = tuple(from_dimacs(l) for l in raw)
        if distinct == raw:
            r["failed_clause"] = tuple(from_dimacs(l) for l in distinct)
    return r


def _failed_clause_clean(cnf, proof, steps, cr, ad):
    r = _correct(cnf, proof, steps, cr, ad)
    if r["failed_step"] > 0:
        r["failed_clause"] = tuple(
            from_dimacs(l) for l in _distinct(steps[r["failed_step"] - 1][1]))
    return r


def _keeps_root(cnf, proof, steps, cr, ad):
    return _as_result(_ref(cnf, steps, cr, ad, True))


def _raises(cnf, proof, steps, cr, ad):
    if steps and steps[0][0] == "d":
        raise OverflowError("deliberately wrong")
    return _correct(cnf, proof, steps, cr, ad)


def self_test(seed, instances):
    good = {"python": _failed_clause_clean, "native": _failed_clause_clean}
    cases = [
        # name, python, native, a label that must be flagged
        ("accepts everything", _accept_all, _accept_all, "sat-accepted"),
        ("rejects everything", _reject_all, _reject_all, "vs-reference"),
        ("native accepts everything", _failed_clause_clean, _accept_all, "engine-diff:ok"),
        ("native rejects everything", _failed_clause_clean, _reject_all, "engine-diff:ok"),
        ("ok without the empty clause", _ok_without_empty, _ok_without_empty, "ok-without-empty"),
        ("ignores check_rat", _ignores_check_rat, _ignores_check_rat, "vs-reference"),
        ("ignores apply_deletions", _ignores_apply_deletions,
         _ignores_apply_deletions, "vs-reference"),
        ("native resolvents off by one", _failed_clause_clean, _resolvents_off,
         "engine-diff:resolvents_checked"),
        ("native counts rup as rat", _failed_clause_clean, _rup_rat_swapped,
         "engine-diff:rup_steps"),
        ("native reason differs", _failed_clause_clean, _reason_off, "engine-diff:reason"),
        ("native failed_clause keeps repeats", _failed_clause_clean, _failed_clause_raw,
         "engine-diff:failed_clause-repeat"),
        ("keeps root literals past their reason", _keeps_root, _keeps_root, "retained-root"),
        ("native raises", _failed_clause_clean, _raises, "engine-diff:raised"),
    ]
    failures = 0
    clean = sweep(seed, instances, good)
    leftover = dict(clean.mismatches)
    print(f"correct stub: {sum(leftover.values())} mismatches {leftover or ''}")
    if leftover:
        failures += 1
    for name, py, rs, want in cases:
        t = sweep(seed, instances, {"python": py, "native": rs}, compare_paths=False)
        hit = sum(v for k, v in t.mismatches.items() if k.startswith(want))
        print(f"{'flagged' if hit else 'MISSED ':8} {name}: {want} x{hit}")
        if not hit:
            failures += 1
    # the zero-count gate
    empty = sweep(seed, 0, good)
    gate = missing_categories(empty)
    print(f"{'flagged' if gate else 'MISSED ':8} a run reaching nothing: "
          f"{len(gate)} categories at zero")
    if not gate:
        failures += 1
    if failures:
        print(f"SELF-TEST FAILED: {failures}")
        return 1
    print("self-test passed")
    return 0


# --------------------------------------------------------------------------


NOT_CHECKED = [
    "formulas and proofs past 10 variables, or long proofs of any kind",
    "real solver proofs: every proof here is generated",
    "the order RAT tries resolvents in: on a rejected RAT step the reference "
    "only bounds resolvents_checked, so that count is judged exactly only "
    "between the two engines",
    "direct use of the Rust Checker and check_step: reached only through "
    "cdclkit_native.check_proof, plus the crate's own cargo test",
    "headers declaring many more variables than used, and the Rust allocation "
    "abort rust/src/checker.rs documents",
    "text parser edge cases, beyond one clause per line",
    "CNF objects whose clauses were built without CNF.add, so repeated literals "
    "and tautologies in the input reach the checkers only after normalisation",
    "drat-trim: not on PATH in this campaign, so nothing here compares with it",
    "whether a root conflict should outlive the deletion of the clauses behind "
    "it: dratify does not document this, the reference assumes it does, as "
    "drat-trim does, and only ok=False would make it matter",
]


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--seed", type=int, default=DEFAULT_SEED)
    ap.add_argument("--instances", type=int, default=DEFAULT_INSTANCES)
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--write-results", action="store_true",
                    help="write campaign/results/engines.json")
    args = ap.parse_args(argv)

    if args.self_test:
        return self_test(args.seed, min(args.instances, 150))

    engines, built_from = native_engines()
    print(f"native checker embeds {built_from}")
    start = time.time()
    tally = sweep(args.seed, args.instances, engines)
    runtime = round(time.time() - start, 1)
    c = tally.counts
    missing = missing_categories(tally)

    print(f"seed {args.seed}, {c['instances']} instances, {c['steps_judged']} steps "
          f"judged, {c['field_comparisons']} field comparisons, {runtime}s")
    for k in sorted(c):
        print(f"  {k}: {c[k]}")
    print("mismatches:" if tally.mismatches else "no mismatches")
    for label, count in sorted(tally.mismatches.items()):
        print(f"  {label}: {count}  [{tally.known.get(label, 'UNEXPLAINED')}]")
        print(f"    e.g. {tally.examples[label][0]!r}")
    if missing:
        print(f"CATEGORIES AT ZERO: {missing}")

    if args.write_results:
        hit = sorted(set(tally.known.values()))
        here = os.path.dirname(os.path.abspath(__file__))
        with open(os.path.join(here, "results", "engines.json"), "w") as fh:
            json.dump({
                "corner": "engines",
                "seeds": [args.seed],
                "instances": c["instances"],
                "steps": c["steps_judged"],
                "per_category_counts": dict(sorted(c.items())),
                "mismatches": dict(sorted(tally.mismatches.items())),
                "unexplained_mismatches": tally.unexplained,
                "categories_at_zero": missing,
                "runtime_seconds": runtime,
                "findings": [{"id": f, "severity": FINDINGS[f][0],
                              "summary": FINDINGS[f][1]} for f in hit],
                "not_checked": NOT_CHECKED,
            }, fh, indent=2)
            fh.write("\n")

    if missing or tally.mismatches:
        print(f"FAILED: {sum(tally.mismatches.values())} mismatches "
              f"({sum(tally.unexplained.values())} unexplained), "
              f"{len(missing)} categories at zero")
        return 1
    print("passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
