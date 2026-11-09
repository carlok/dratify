# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Soundness campaign, corner `root`: everything that happens at the root level.

Lemmas that are unit at the root on arrival, conflicting units, the empty clause
in the input, a formula refuted by unit propagation alone, and what a deletion
does to the root assignment. Run from the repo root:

    python -m campaign.gen_root                  # default seed and size
    python -m campaign.gen_root --self-test      # the harness against wrong stubs

What a checker result is held to, all of it decided by `campaign/oracle.py`:

* `ok=True` requires `not satisfiable(F)`. This is the primary question.
* Every field of the verdict matches a walk of the proof by the oracle under the
  rule dratify documents: a deletion is ignored when the clause is unit under the
  root assignment, and all of them once the root has conflicted (flavour
  `operational`), and a step is RUP, or RAT on its first literal, against the
  clauses present at that moment.
* The two engines, on text and on a list of steps, agree on every field.

The findings this was written to catch are fixed, so nothing here carries a label
any more: a mismatch reads UNEXPLAINED and the run exits non-zero. Coverage counters are
computed from the oracle's walk, not from the checker's answer, so fixing a bug
cannot zero a category and a checker cannot inflate one.
"""

from __future__ import annotations

import argparse
import json
import random
import sys
import time
from collections import Counter
from itertools import combinations_with_replacement, product
from pathlib import Path

from campaign import oracle
from dratify import DRATChecker, check_proof, parse_dimacs, parse_proof, register_native
from dratify.lits import from_dimacs, to_dimacs

DEFAULT_SEED = 20261108
DEFAULT_INSTANCES = 30000
MAX_NVARS = 8           # plus a few fresh ones; far below the oracle's 16
RESULTS = Path(__file__).parent / "results" / "root.json"

# (check_rat, apply_deletions)
MODES = list(product((True, False), (True, False)))

FIELDS = ("ok", "reason", "steps", "rup_steps", "rat_steps", "deletions",
          "ignored_deletions", "resolvents_checked", "failed_step",
          "failed_clause", "reached_empty")

# what is compared with the oracle: it has no notion of `reason` or of
# `resolvents_checked`, which the two engines are compared on instead
JUDGED = ("ok", "reached_empty", "steps", "rup_steps", "rat_steps", "deletions",
          "ignored_deletions", "failed_step", "failed_set")

# label prefix -> finding, for findings still open. root-1 and root-2 are fixed.
KNOWN: dict[str, str] = {}

FINDINGS = [
    {"id": "root-1", "status": "fixed", "severity": "Critical",
     "summary": "Deleting a clause that is the reason for a root literal leaves "
                "that literal assigned: both engines return ok=True on the "
                "satisfiable (1)(-1 2) with `d -1 2 0`, `-2 0`, `0`."},
    {"id": "root-2", "status": "fixed", "severity": "Bug",
     "summary": "failed_clause differs between engines when a rejected step "
                "repeats a literal: Python has it deduplicated, native raw."},
    {"id": "root-3", "status": "documented", "severity": "Note",
     "summary": "Root refutation ends the checking: a UP-refuted input ignores "
                "the proof entirely, and a deletion after a root conflict does "
                "not un-refute. Sound, and how drat-trim reads it."},
]

NOT_CHECKED = [
    "resolvents_checked against the oracle: it is only compared between engines",
    "agreement with drat-trim: the binary is not used here, flavours come from "
    "the oracle",
    "the `is_pseudo_unit` over-approximation: dratify's rule and the oracle's "
    "`operational` flavour are the same test, and drat-trim's reason test can differ",
    "input clauses reaching the checker with repeated literals other than "
    "through parse_dimacs (CNF.add normalises; a hand-built CNF is not tried)",
    "engine='auto' and MemoryProof (text and lists of steps are)",
    "formulas above about 11 variables, and proofs above about 16 steps",
    "non-chronological fresh variables (a gap in a list of steps trips the "
    "_validate_steps bound, a documented guard, not this corner)",
    "cdclkit: this generator is aimed at dratify's checker only",
]


# -- formulas and proofs --------------------------------------------------------


def tautological(clause):
    return any(-l in clause for l in clause)


def cnf_text(F, nvars):
    head = f"p cnf {nvars} {len(F)}\n"
    return head + "".join(" ".join(map(str, c)) + (" 0\n" if c else "0\n") for c in F)


def proof_text(steps):
    out = []
    for kind, lits in steps:
        body = " ".join(map(str, lits))
        out.append(("d " if kind == "d" else "") + (body + " 0" if body else "0"))
    return "\n".join(out) + "\n" if out else ""


def internal_steps(steps):
    return [(k, tuple(from_dimacs(l) for l in lits)) for k, lits in steps]


def literal(rng, v):
    return v if rng.random() < .5 else -v


def random_clause(rng, nvars, k):
    vs = rng.sample(range(1, nvars + 1), min(k, nvars))
    return [literal(rng, v) for v in vs]


def fam_random_root(rng, nvars):
    F = [random_clause(rng, nvars, rng.choice((1, 2, 2, 3, 3, 4)))
         for _ in range(rng.randrange(2, 3 * nvars))]
    return F, "mixed"


def fam_implication_chain(rng, nvars):
    """A unit and a chain of binary implications: all reasons, deep root."""
    order = rng.sample(range(1, nvars + 1), nvars)
    signs = {v: rng.choice((1, -1)) for v in order}
    F = [[signs[order[0]] * order[0]]]
    for a, b in zip(order, order[1:]):
        if rng.random() < .8:
            F.append([-signs[a] * a, signs[b] * b])
    for _ in range(rng.randrange(0, nvars)):
        c = random_clause(rng, nvars, rng.choice((2, 3)))
        F.append(c)
    rng.shuffle(F)
    return F, rng.choice(("mixed", "cheat"))


def fam_planted(rng, nvars):
    """Satisfiable by construction, with root units: a refutation must be wrong."""
    model = {v: rng.choice((True, False)) for v in range(1, nvars + 1)}
    def holds(c):
        return any((l > 0) == model[abs(l)] for l in c)
    F = []
    for _ in range(rng.randrange(1, 3)):
        v = rng.randrange(1, nvars + 1)
        F.append([v if model[v] else -v])
    while len(F) < rng.randrange(3, 2 * nvars + 3):
        c = random_clause(rng, nvars, rng.choice((2, 2, 3)))
        if holds(c):
            F.append(c)
    rng.shuffle(F)
    return F, "cheat"


def fam_up_refutable(rng, nvars):
    """A chain ending in a contradiction, so propagation alone refutes it."""
    n = rng.randrange(2, nvars + 1)
    order = rng.sample(range(1, nvars + 1), n)
    F = [[order[0]]]
    for a, b in zip(order, order[1:]):
        F.append([-a, b])
    F.append([-order[-1]] if rng.random() < .5 else [-order[-1], -order[0]])
    F += [random_clause(rng, nvars, 3) for _ in range(rng.randrange(0, 4))]
    rng.shuffle(F)
    return F, "mixed"


def fam_input_empty(rng, nvars):
    F = [random_clause(rng, nvars, rng.choice((1, 2, 3)))
         for _ in range(rng.randrange(0, 5))]
    F.insert(rng.randrange(len(F) + 1), [])
    return F, "mixed"


def fam_conflicting_units(rng, nvars):
    v = rng.randrange(1, nvars + 1)
    F = [random_clause(rng, nvars, rng.choice((2, 3)))
         for _ in range(rng.randrange(0, 5))]
    F += [[v], [-v]]
    rng.shuffle(F)
    return F, "mixed"


def fam_lemma_refutable(rng, nvars):
    """Not refuted by propagation, but refuted by failed-literal lemmas."""
    a, b, c = rng.sample(range(1, nvars + 1), 3)
    a, b, c = literal(rng, a), literal(rng, b), literal(rng, c)
    F = [[a, b], [a, -b], [-a, c], [-a, -c]]
    if nvars > 3 and rng.random() < .7:
        rest = [v for v in range(1, nvars + 1) if v not in map(abs, (a, b, c))]
        v = rng.choice(rest)
        F.append([literal(rng, v)])                # root, but not the refutation
        if len(rest) > 1:
            w = rng.choice([x for x in rest if x != v])
            F.append([-F[-1][0], literal(rng, w)])
    rng.shuffle(F)
    return F, "probe"


def fam_tautology_in_input(rng, nvars):
    """A tautology is dropped on reading, and a repeated literal normalised."""
    F = [random_clause(rng, nvars, rng.choice((1, 2, 3)))
         for _ in range(rng.randrange(1, 2 * nvars))]
    v = rng.randrange(1, nvars + 1)
    F.append([v, -v] + ([rng.randrange(1, nvars + 1)] if rng.random() < .5 else []))
    r = random_clause(rng, nvars, 2)
    F.append(r + [r[0]])
    rng.shuffle(F)
    return F, "mixed"


FAMILIES = [fam_random_root, fam_implication_chain, fam_planted, fam_up_refutable,
            fam_input_empty, fam_conflicting_units, fam_lemma_refutable,
            fam_tautology_in_input]

PROFILES = {
    #         aimed: lemmas built from the root; del_*: deletion kinds
    "mixed": dict(unit_at_root=6, unit=2, neg_root=2, neg_sticky=2, satisfied=2,
                  fresh=1, random=2, repeat=2, taut=1, probe=2, del_reason=3,
                  del_any=3, del_unit=2, del_absent=1, empty=1),
    "cheat": dict(unit_at_root=2, unit=1, neg_root=1, neg_sticky=5, satisfied=1,
                  fresh=1, random=1, repeat=1, taut=0, probe=1, del_reason=8,
                  del_any=1, del_unit=1, del_absent=0, empty=1),
    "probe": dict(unit_at_root=2, unit=1, neg_root=1, neg_sticky=0, satisfied=1,
                  fresh=0, random=1, repeat=1, taut=0, probe=10, del_reason=0,
                  del_any=1, del_unit=1, del_absent=0, empty=0),
}


def reason_clauses(cur):
    """Clauses of two or more literals whose removal shrinks the root assignment."""
    conflict, root = oracle.propagate(cur)
    if conflict:
        return []
    out = []
    for c in cur:
        if len(set(c)) >= 2:
            rest, _ = oracle.remove_one(cur, c)
            again, after = oracle.propagate(rest)
            if not again and not root <= after:
                out.append(c)
    return out


def valid_order(lemma, cur):
    """`lemma` reordered so it passes if any pivot would make it pass, else None."""
    if oracle.rup(cur, lemma):
        return lemma
    for i, l in enumerate(lemma):
        if oracle.rat(cur, lemma, l):
            return [l] + lemma[:i] + lemma[i + 1:]
    return None


def build_proof(rng, F, nvars, profile):
    """A proof aimed at the root, walked over a multiset that honours every
    deletion of two or more literals, so that it goes on to try what a kept reason
    forbids. What the checker should say about the result is `predict`'s business."""
    cur = [list(c) for c in F if not tautological(c)]
    weights = PROFILES[profile]
    actions = list(weights)
    steps: list[tuple[str, list[int]]] = []
    sticky: set[int] = set()         # every literal the root has ever held
    fresh = nvars + 1
    for _ in range(rng.randrange(1, 13)):
        _, root = oracle.propagate(cur)
        sticky |= root
        action = rng.choices(actions, [weights[a] for a in actions])[0]
        free_vars = [v for v in range(1, nvars + 1)
                     if v not in root and -v not in root]
        lemma = None

        if action.startswith("del_"):
            present = [c for c in cur if len(set(c)) >= 2]
            if action == "del_reason":
                pool = reason_clauses(cur) or present
            elif action == "del_any":
                pool = present
            elif action == "del_unit":
                pool = [c for c in cur if len(set(c)) == 1]
            else:
                pool = [random_clause(rng, nvars, 2)]
            if not pool:
                continue
            target = list(rng.choice(pool))
            rng.shuffle(target)
            if action == "del_unit" and rng.random() < .3:
                target = target + target
            steps.append(("d", target))
            if len(set(target)) >= 2:
                cur, _ = oracle.remove_one(cur, target)
            continue

        if action == "unit_at_root":
            falsified = [-l for l in root]
            k = rng.randrange(0, min(3, len(falsified)) + 1)
            lemma = rng.sample(falsified, k)
            if free_vars:
                lemma.append(literal(rng, rng.choice(free_vars)))
        elif action == "unit":
            lemma = [literal(rng, rng.randrange(1, nvars + 1))]
        elif action == "neg_root":
            lemma = [-rng.choice(sorted(root))] if root else None
        elif action == "neg_sticky":
            if sticky:
                k = rng.randrange(1, min(2, len(sticky)) + 1)
                lemma = [-l for l in rng.sample(sorted(sticky), k)]
        elif action == "satisfied":
            if root:
                lemma = [rng.choice(sorted(root))]
                lemma += random_clause(rng, nvars, rng.choice((1, 2)))
                lemma = list(dict.fromkeys(lemma))
        elif action == "fresh":
            lemma = [fresh * rng.choice((1, -1))]
            if rng.random() < .5:
                other = random_clause(rng, nvars, 1)
                lemma += other
            fresh += 1
        elif action == "random":
            lemma = random_clause(rng, nvars, rng.choice((2, 3)))
        elif action == "repeat":
            base = random_clause(rng, nvars, rng.choice((1, 2)))
            lemma = base + [rng.choice(base)]
        elif action == "taut":
            v = rng.randrange(1, nvars + 1)
            lemma = [v, -v]
        elif action == "probe":
            cands = [s * v for v in range(1, nvars + 1) for s in (1, -1)
                     if oracle.rup(cur, [s * v])]
            if cands:
                lemma = [rng.choice(cands)]
        elif action == "empty":
            lemma = []
        if lemma is None:
            continue

        rng.shuffle(lemma)
        if lemma:
            ordered = valid_order(lemma, cur)
        else:
            ordered = lemma if oracle.rup(cur, lemma) else None
        if ordered is None:
            if rng.random() < .1:           # rejections are compared as well
                steps.append(("a", lemma))
                return steps
            continue
        steps.append(("a", ordered))
        if not ordered:
            break
        cur.append(list(ordered))

    if profile == "probe" or rng.random() < .4:
        if profile == "probe":             # finish the failed-literal refutation
            for _ in range(2 * nvars):
                if oracle.propagate(cur)[0]:
                    break
                cands = [s * v for v in range(1, nvars + 1) for s in (1, -1)
                         if oracle.rup(cur, [s * v])
                         and s * v not in oracle.propagate(cur)[1]]
                if not cands:
                    break
                steps.append(("a", [cands[0]]))
                cur.append([cands[0]])
        steps.append(("a", []))
        if rng.random() < .2:              # nothing after the empty clause counts
            steps.append(("a", random_clause(rng, nvars, 2)))
    return steps


def make_instance(seed, index):
    rng = random.Random(f"{seed}:{index}")
    family = FAMILIES[index % len(FAMILIES)]
    nvars = rng.randrange(3, MAX_NVARS + 1)
    F, profile = family(rng, nvars)
    header = nvars + rng.choice((0, 0, 0, 1, 2))
    steps = build_proof(rng, F, header, profile)
    return {"family": family.__name__, "F": F, "nvars": header, "steps": steps}


# -- what the oracle says ---------------------------------------------------------


def verdict(ok=False, reached_empty=False, steps=0, rup_steps=0, rat_steps=0,
            deletions=0, ignored_deletions=0, failed_step=-1, failed_set=None):
    return dict(ok=ok, reached_empty=reached_empty, steps=steps, rup_steps=rup_steps,
                rat_steps=rat_steps, deletions=deletions,
                ignored_deletions=ignored_deletions, failed_step=failed_step,
                failed_set=failed_set)


def predict(F, steps, flavour="operational", check_rat=True, apply_deletions=True):
    """What a correct forward checker reports, from `oracle.replay` alone.

    Returns (verdict, analysis). A multiset refuted by propagation stays refuted,
    as flavour `operational` says: the proof is over, so a later deletion is
    ignored and, by the oracle's own remark, every addition passes.
    """
    clean = [list(c) for c in F if not tautological(c)]
    if oracle.propagate(clean)[0]:
        return verdict(ok=True, reached_empty=True), {"root_refuted_input": True,
                                                      "reason_deletion": False,
                                                      "walk": []}
    walked = steps if apply_deletions else [s for s in steps if s[0] == "a"]
    judged, _ = oracle.replay(clean, walked, flavour, stop_at_unacceptable=False)
    v = verdict()
    cur = [list(c) for c in clean]
    refuted = False
    reason_deletion = False
    walk = []
    judged_iter = iter(judged)
    for kind, lits in steps:
        v["steps"] += 1
        if kind == "d" and not apply_deletions:
            if len(set(lits)) <= 1:
                v["ignored_deletions"] += 1
            continue
        j = next(judged_iter)
        if kind == "d":
            if j.applied:
                if not refuted:
                    before = oracle.propagate(cur)[1]
                    after_c, after = oracle.propagate(oracle.remove_one(cur, lits)[0])
                    if not after_c and not before <= after:
                        reason_deletion = True
                cur, _ = oracle.remove_one(cur, lits)
                v["deletions"] += 1
            else:
                v["ignored_deletions"] += 1
            walk.append((j, refuted))
            continue
        passes_rup = refuted or j.rup
        if passes_rup:
            v["rup_steps"] += 1
        elif check_rat and j.rat_on_first:
            v["rat_steps"] += 1
        else:
            v["failed_step"] = v["steps"]
            v["failed_set"] = frozenset(lits)
            walk.append((j, refuted))
            return v, {"root_refuted_input": False, "reason_deletion": reason_deletion,
                       "walk": walk}
        walk.append((j, refuted))
        if not lits:
            v["reached_empty"] = True
            v["ok"] = True
            break
        cur.append(list(lits))
        refuted = refuted or oracle.propagate(cur)[0]
    return v, {"root_refuted_input": False, "reason_deletion": reason_deletion,
               "walk": walk}


def count_coverage(inst, cnt):
    """Coverage from the oracle's walk under the documented rule, default mode."""
    F = [list(c) for c in inst["F"]]
    clean = [c for c in F if not tautological(c)]
    cnt["instances"] += 1
    cnt["family:" + inst["family"]] += 1
    if len(clean) != len(F):
        cnt["input_tautology_dropped"] += 1
    sat = oracle.satisfiable(F)
    cnt["sat_instances" if sat else "unsat_instances"] += 1
    if any(not c for c in F):
        cnt["input_empty_clause"] += 1
    units = {c[0] for c in clean if len(set(c)) == 1}
    if any(-u in units for u in units):
        cnt["input_conflicting_units"] += 1
    conflict, _ = oracle.propagate(clean)
    if conflict and not any(not c for c in F) and not any(-u in units for u in units):
        cnt["input_up_refutable_otherwise"] += 1
    if conflict:
        cnt["input_refuted_at_root"] += 1
        if inst["steps"]:
            cnt["input_refuted_proof_ignored"] += 1
        return
    cnt["input_not_refuted_at_root"] += 1

    v, info = predict(F, inst["steps"])
    cnt["refutation_valid" if v["ok"] else "proof_not_a_refutation"] += 1
    if sat and not v["ok"] and any(not s[1] and s[0] == "a" for s in inst["steps"]):
        cnt["sat_with_empty_clause_attempt"] += 1

    cur = [list(c) for c in clean]
    nvars = inst["nvars"]
    for j, refuted in info["walk"]:
        conflict, root = oracle.propagate(cur)
        lits = set(j.clause)
        cnt["steps_default_mode"] += 1
        if j.kind == "d":
            if j.applied:
                cnt["deletions_applied"] += 1
                cur, _ = oracle.remove_one(cur, j.clause)
            elif refuted:
                cnt["deletions_after_root_conflict"] += 1
            elif len(lits) <= 1:
                cnt["deletions_ignored_unit"] += 1
            elif j.present:
                cnt["reason_deletions"] += 1
            else:
                cnt["deletions_ignored_absent"] += 1
            continue
        accepted = refuted or bool(j.rup or j.rat_on_first)
        if len(j.clause) != len(lits):
            cnt["lemma_repeated_literal"] += 1
        if any(-l in lits for l in lits):
            cnt["lemma_tautological"] += 1
        if any(abs(l) > nvars for l in lits):
            cnt["lemma_fresh_variable"] += 1
        if refuted:
            cnt["additions_after_root_conflict"] += 1
        if len(lits) == 1 and -next(iter(lits)) in root:
            cnt["conflicting_unit_lemma_accepted" if accepted
                else "conflicting_unit_lemma_rejected"] += 1
        if not lits:
            cnt["empty_clause_accepted" if accepted else "empty_clause_rejected"] += 1
        if not accepted:
            cnt["steps_rejected"] += 1
            break
        if not refuted and not j.rup:
            cnt["steps_accepted_only_by_rat"] += 1
        if not lits:
            break
        if lits & root:
            cnt["lemma_satisfied_at_root"] += 1
        else:
            free = [l for l in lits if -l not in root]
            if len(lits) == 1:
                cnt["lemma_unit_literal"] += 1
            elif len(free) == 1:
                cnt["lemma_unit_at_root"] += 1
        before_conflict = conflict
        cur.append(list(j.clause))
        if not before_conflict and oracle.propagate(cur)[0]:
            cnt["lemma_triggers_root_conflict"] += 1


REQUIRED = [
    "input_empty_clause", "input_conflicting_units", "input_up_refutable_otherwise",
    "input_refuted_proof_ignored", "input_not_refuted_at_root", "input_tautology_dropped",
    "sat_instances", "unsat_instances", "refutation_valid", "proof_not_a_refutation",
    "sat_with_empty_clause_attempt", "lemma_unit_at_root", "lemma_unit_literal",
    "lemma_satisfied_at_root", "lemma_triggers_root_conflict",
    "conflicting_unit_lemma_accepted", "conflicting_unit_lemma_rejected",
    "additions_after_root_conflict", "deletions_after_root_conflict",
    "empty_clause_accepted", "empty_clause_rejected", "steps_accepted_only_by_rat",
    "steps_rejected", "deletions_applied", "deletions_ignored_unit",
    "deletions_ignored_absent", "reason_deletions", "lemma_repeated_literal",
    "lemma_tautological", "lemma_fresh_variable", "runs_rup_only",
    "runs_deletions_off", "engine_comparisons", "exhaustive_instances",
    "exhaustive_satisfiable",
]


# -- running a checker, and judging it --------------------------------------------


def fields_of(r):
    return {name: getattr(r, name) for name in FIELDS}


def real_engine(engine):
    def run(cnf, proof, check_rat, apply_deletions):
        return fields_of(check_proof(parse_dimacs(cnf), proof, check_rat=check_rat,
                                     apply_deletions=apply_deletions, engine=engine))
    return run


def judged_view(fields):
    fc = fields.get("failed_clause")
    view = {k: fields[k] for k in JUDGED if k != "failed_set"}
    view["failed_set"] = (None if fc is None
                          else frozenset(to_dimacs(l) for l in fc))
    return view


def same_verdict(a, b):
    return all(a[k] == b[k] for k in JUDGED)


def classify(sat, got, want):
    """The label for a result that failed, or None when it passes."""
    if got["ok"] and sat:
        return "UNEXPLAINED:false-refutation"
    if same_verdict(got, want):
        return None
    wrong = sorted(k for k in JUDGED if got[k] != want[k])
    return "UNEXPLAINED:" + ",".join(wrong)


def judge_instance(inst, engines, cnt=None, modes=MODES):
    """Every label this instance earns, as a list of (label, detail)."""
    F, steps, nvars = inst["F"], inst["steps"], inst["nvars"]
    labels = []
    cnf = cnf_text(F, nvars)
    text = proof_text(steps)
    lst = internal_steps(steps)
    sat = oracle.satisfiable(F)
    for mode in modes:
        check_rat, apply_deletions = mode
        if cnt is not None:
            if not check_rat:
                cnt["runs_rup_only"] += 1
            if not apply_deletions:
                cnt["runs_deletions_off"] += 1
        want, _ = predict(F, steps, "operational", check_rat, apply_deletions)
        if cnt is not None:
            cnt["steps_judged"] += want["steps"]
        results = {}
        for name, run in engines.items():
            for form, proof in (("text", text), ("list", lst)):
                try:
                    results[f"{name}/{form}"] = run(cnf, proof, check_rat, apply_deletions)
                except KeyboardInterrupt:
                    raise
                except BaseException as e:     # a Rust panic is a BaseException
                    labels.append((f"UNEXPLAINED:exception:{type(e).__name__}",
                                   f"{name}/{form} mode={mode}: {e}"))
        if not results:
            continue
        keys = list(results)
        first = results[keys[0]]
        for other in keys[1:]:
            if cnt is not None:
                cnt["engine_comparisons"] += 1
            for field in FIELDS:
                if results[other][field] != first[field]:
                    label = f"engine:{field}"
                    labels.append((label, f"{keys[0]} {first[field]!r} vs {other} "
                                          f"{results[other][field]!r} mode={mode}"))
        seen = []
        for key in keys:
            view = judged_view(results[key])
            if view in seen:
                continue
            seen.append(view)
            label = classify(sat, view, want)
            if label:
                labels.append((label, f"{key} mode={mode} got={_show(view)} "
                                      f"want={_show(want)}"))
    return labels


def _show(v):
    return {k: (sorted(x) if isinstance(x, frozenset) else x) for k, x in v.items()}


def finding_of(label):
    for prefix, fid in KNOWN.items():
        if label.startswith(prefix):
            return fid
    return None


def shrink(inst, engines, label):
    """Remove clauses, steps and literals while the instance still earns `label`."""
    def earns(c):
        return any(l == label for l, _ in judge_instance(c, engines))
    cur = {**inst, "F": [list(c) for c in inst["F"]],
           "steps": [(k, list(l)) for k, l in inst["steps"]]}
    changed = True
    while changed:
        changed = False
        for i in range(len(cur["steps"]) - 1, -1, -1):
            c = {**cur, "steps": cur["steps"][:i] + cur["steps"][i + 1:]}
            if earns(c):
                cur, changed = c, True
        for i in range(len(cur["F"]) - 1, -1, -1):
            c = {**cur, "F": cur["F"][:i] + cur["F"][i + 1:]}
            if earns(c):
                cur, changed = c, True
        for i, (k, lits) in enumerate(cur["steps"]):
            for j in range(len(lits) - 1, -1, -1):
                new = lits[:j] + lits[j + 1:]
                c = {**cur, "steps": cur["steps"][:i] + [(k, new)] + cur["steps"][i + 1:]}
                if earns(c):
                    cur, changed = c, True
                    break
    return cur


def sweep(seed, instances, engines, cnt, labels, examples, coverage=True):
    for index in range(instances):
        inst = make_instance(seed, index)
        if coverage:
            count_coverage(inst, cnt)
        for label, detail in judge_instance(inst, engines, cnt if coverage else None):
            labels[label] += 1
            examples.setdefault(label, (index, inst, detail))


def exhaustive(engines, cnt, labels, examples):
    """Every formula of at most 3 clauses over 2 variables, as a multiset, with
    every proof of two steps and then the empty clause. Default mode only.

    The random sweep is seeded and so could miss a small case; this cannot. It is
    fixed, so `--seed` and `--instances` do not change it.
    """
    universe = [[1], [-1], [2], [-2], [1, 2], [1, -2], [-1, 2], [-1, -2]]
    moves = [("a", c) for c in universe] + [("d", c) for c in universe]
    formulas = [list(f) for n in range(4)
                for f in combinations_with_replacement(universe, n)]
    index = 0
    for F in formulas:
        for s1, s2 in product(moves, moves):
            index += 1
            inst = {"family": "exhaustive", "F": F, "nvars": 2,
                    "steps": [s1, s2, ("a", [])]}
            cnt["exhaustive_instances"] += 1
            if oracle.satisfiable(F):
                cnt["exhaustive_satisfiable"] += 1
            for label, detail in judge_instance(inst, engines, cnt, [(True, True)]):
                labels[label] += 1
                examples.setdefault(label, (f"exhaustive {index}", inst, detail))


# -- the self-test: deliberately wrong checkers -----------------------------------


class NoRootExtension(DRATChecker):
    """The 0.1.6 bug: a lemma unit at the root does not extend the root."""

    def _add_lemma(self, lits):
        self._insert(list(lits))


class BlindToInputConflict(DRATChecker):
    """Forgets that the input was already refuted at the root."""

    def __init__(self, *a, **k):
        super().__init__(*a, **k)
        self._root_conflict = self._input_refuted = False


class LengthOnlyDeletions(DRATChecker):
    """root-1: only clauses of at most one literal are spared, so a reason goes
    while the literal it implied stays. A return of that has to fail this run."""

    def _unit_at_root(self, lits):
        return False


class DeletesUnits(DRATChecker):
    """Applies deletions of unit clauses, which dratify documents ignoring."""

    def check_step(self, kind, lits):
        if kind == "d" and len(set(lits)) == 1 and self.apply_deletions:
            self.result.steps += 1
            if self._erase(list(dict.fromkeys(lits))):
                self.result.deletions += 1
            else:
                self.result.ignored_deletions += 1
            return True
        return super().check_step(kind, lits)


def mutant(cls):
    def run(cnf, proof, check_rat, apply_deletions):
        steps = parse_proof(proof) if isinstance(proof, str) else proof
        return fields_of(cls(parse_dimacs(cnf), check_rat=check_rat,
                             apply_deletions=apply_deletions).check(steps))
    return run


def stub_accepts_everything(cnf, proof, check_rat, apply_deletions):
    return dict(ok=True, reason="stub", steps=0, rup_steps=0, rat_steps=0, deletions=0,
                ignored_deletions=0, resolvents_checked=0, failed_step=-1,
                failed_clause=None, reached_empty=True)


def stub_rejects_everything(cnf, proof, check_rat, apply_deletions):
    return dict(ok=False, reason="stub", steps=1, rup_steps=0, rat_steps=0, deletions=0,
                ignored_deletions=0, resolvents_checked=0, failed_step=1,
                failed_clause=(), reached_empty=False)


def stub_perfect(cnf, proof, check_rat, apply_deletions):
    """Answers with the oracle's own prediction: the harness must not flag it."""
    f = parse_dimacs(cnf)
    F = [[to_dimacs(l) for l in c] for c in f.clauses]
    steps = parse_proof(proof) if isinstance(proof, str) else proof
    dimacs = [(k, [to_dimacs(l) for l in lits]) for k, lits in steps]
    v, _ = predict(F, dimacs, "operational", check_rat, apply_deletions)
    fc = None if v["failed_set"] is None else tuple(
        sorted(from_dimacs(l) for l in v["failed_set"]))
    return dict(ok=v["ok"], reason="stub", steps=v["steps"], rup_steps=v["rup_steps"],
                rat_steps=v["rat_steps"], deletions=v["deletions"],
                ignored_deletions=v["ignored_deletions"], resolvents_checked=0,
                failed_step=v["failed_step"], failed_clause=fc,
                reached_empty=v["reached_empty"])


def self_test(seed, instances):
    """Each wrong stub must be flagged; the perfect one must not be."""
    cases = [
        ("accepts everything", {"stub": stub_accepts_everything}, True),
        ("rejects everything", {"stub": stub_rejects_everything}, True),
        ("0.1.6 bug: no root extension", {"stub": mutant(NoRootExtension)}, True),
        ("blind to a refuted input", {"stub": mutant(BlindToInputConflict)}, True),
        ("deletes unit clauses", {"stub": mutant(DeletesUnits)}, True),
        ("root-1: spares clauses by length alone", {"stub": mutant(LengthOnlyDeletions)},
         True),
        ("engines disagree", {"a": stub_perfect, "b": stub_rejects_everything}, True),
        ("the oracle itself", {"stub": stub_perfect}, False),
    ]
    failed = 0
    for name, engines, should_flag in cases:
        cnt, labels, examples = Counter(), Counter(), {}
        sweep(seed, instances, engines, cnt, labels, examples, coverage=False)
        flagged = sum(labels.values())
        critical = sum(n for l, n in labels.items() if "false-refutation" in l)
        good = (flagged > 0) == should_flag
        failed += not good
        print(f"{'pass' if good else 'FAIL'}  {name}: {flagged} mismatches "
              f"({critical} false refutations) in {instances} instances")
        for label, n in labels.most_common(4):
            print(f"        {n:7d}  {label}")
    # accepting everything has to show as false refutations in particular
    cnt, labels, examples = Counter(), Counter(), {}
    sweep(seed, instances, {"stub": stub_accepts_everything}, cnt, labels, examples,
          coverage=False)
    if not any("false-refutation" in l for l in labels):
        print("FAIL  accepting everything raised no false refutation")
        failed += 1
    print("self-test " + ("FAILED" if failed else "passed"))
    return 1 if failed else 0


# -- main -------------------------------------------------------------------------


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--seed", type=int, default=DEFAULT_SEED)
    ap.add_argument("--instances", type=int, default=DEFAULT_INSTANCES)
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--no-write", action="store_true",
                    help=f"do not write {RESULTS.name}")
    args = ap.parse_args(argv)

    if args.self_test:
        return self_test(args.seed, min(args.instances, 800))

    engines = {"python": real_engine("python")}
    try:
        import cdclkit_native
        register_native(cdclkit_native)
        engines["native"] = real_engine("native")
    except ImportError:
        print("no native checker installed: `engine_comparisons` covers Python "
              "text against Python lists only, and this run does not count",
              file=sys.stderr)

    start = time.monotonic()
    cnt, labels, examples = Counter(), Counter(), {}
    sweep(args.seed, args.instances, engines, cnt, labels, examples)
    exhaustive(engines, cnt, labels, examples)
    elapsed = time.monotonic() - start

    print(f"seed {args.seed}, {args.instances} random instances over {len(MODES)} modes "
          f"and {cnt['exhaustive_instances']} exhaustive, {cnt['steps_judged']} steps "
          f"judged, engines {sorted(engines)}, {elapsed:.1f}s")
    for key in sorted(cnt):
        print(f"  {cnt[key]:9d}  {key}")

    missing = [c for c in REQUIRED if not cnt[c]]
    for c in missing:
        print(f"COVERAGE FAILURE: category {c} stayed at zero")
    if "native" not in engines:
        print("COVERAGE FAILURE: the native engine did not run")

    unexplained = 0
    print(f"mismatches: {sum(labels.values())}")
    for label, n in labels.most_common():
        fid = finding_of(label)
        unexplained += fid is None
        print(f"  {n:9d}  {label}  [{fid or 'UNEXPLAINED'}]")
    for label, (index, inst, detail) in sorted(examples.items()):
        small = shrink(inst, engines, label)
        print(f"example {label} (instance {index}, family {inst['family']}):")
        print(f"  F = {small['F']}, header {small['nvars']} variables")
        print(f"  proof = {proof_text(small['steps'])!r}")
        print(f"  {detail}")

    if not args.no_write:
        RESULTS.parent.mkdir(exist_ok=True)
        RESULTS.write_text(json.dumps({
            "corner": "root",
            "seeds": [args.seed],
            "instances": cnt["instances"] + cnt["exhaustive_instances"],
            "steps": cnt["steps_judged"],
            "per_category_counts": dict(sorted(cnt.items())),
            "mismatch_labels": dict(labels.most_common()),
            "runtime_seconds": round(elapsed, 1),
            "findings": FINDINGS,
            "not_checked": NOT_CHECKED,
        }, indent=2) + "\n")

    # Anything here is a regression, or something new.
    if labels or missing or "native" not in engines:
        print(f"exit 1: {len(labels)} labels, {unexplained} of them unexplained, "
              f"{len(missing)} categories at zero")
        return 1
    print("every result matched the oracle and every category was reached")
    return 0


if __name__ == "__main__":
    sys.exit(main())
