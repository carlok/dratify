# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Aim a generator at `ok` against `reached_empty`: where a refutation ends.

The questions, all asked of both engines through every proof shape:

* A proof cut short at any step or byte is never a refutation (`ok` and
  `reached_empty` stay False), even when its lemmas already refute the formula.
* What follows the first accepted empty clause changes no field of the result.
* `d 0` is not the empty clause, and `0` is not accepted without a conflict.
* A satisfiable formula is never refuted, however the proof ends. This is the
  primary question, and the generator aims at it with bogus endings, including
  a RAT step made possible by deleting the reason of a root-level literal.
* Every step is judged by the oracle under the reading dratify documents: RUP,
  or RAT on the first literal, with deletions of clauses unit under the root
  assignment ignored, and all of them once the root has conflicted (`operational`).

    python -m campaign.gen_ok_empty                # reproduces the reported run
    python -m campaign.gen_ok_empty --self-test    # the harness against wrong stubs

The native engine comes from `cdclkit_native`, as in tests/test_differential.py,
because both engines are the point. The run fails if it is missing.

Exit status: 0 only with no mismatch and no empty category. The findings this was
written to catch are fixed and carry no label now, so a return of one fails the run.
"""

from __future__ import annotations

import argparse
import json
import pathlib
import random
import sys
import time
from collections import Counter
from dataclasses import dataclass

from campaign import oracle
from dratify import MemoryProof, check_proof, parse_dimacs, register_native

FIELDS = ("ok", "reached_empty", "reason", "steps", "rup_steps", "rat_steps",
          "deletions", "ignored_deletions", "resolvents_checked", "failed_step",
          "failed_clause")

FLAGS = ((True, True), (True, False), (False, True), (False, False))

NEVER = "every step verified, but the proof never derives the empty clause"

#: Every one of these must be non-zero, or the run did not reach its corner.
#: Only things the generator aims at: none needs a bug to be present.
REQUIRED = (
    "compared_python_native", "route_text", "route_list", "route_memory",
    "oracle_steps_judged", "ok_true_on_unsat", "rejected_steps_agreeing",
    "accepted_only_by_rat", "deletions_applied", "deletions_ignored",
    "truncated_no_empty_rejected", "truncated_after_top_level_conflict",
    "byte_cut_raised", "byte_cut_judged", "tail_instances", "tail_steps",
    "tail_additions_not_acceptable_before_empty", "tail_deletions",
    "tail_second_empty", "tail_malformed_raised", "delete_empty_steps",
    "delete_empty_not_a_refutation", "empty_step_rejected",
    "empty_step_accepted", "sat_formula_checks", "sat_formula_empty_attempted",
    "reason_deletion_then_rat_attempted", "unit_deletion_then_negation_rejected",
    "up_refuted_input_checks", "up_refuted_input_with_invalid_step",
    "input_contains_empty_clause", "repeated_literal_rejections",
)

FINDINGS = [
    {"id": "ok_empty-1", "status": "fixed", "severity": "Critical",
     "summary": "ok=True on a satisfiable formula, both engines: deleting a "
                "root literal's reason keeps the literal but removes the RAT "
                "candidate, so its negation passes as RAT and refutes."},
    {"id": "ok_empty-2", "status": "fixed", "severity": "Bug",
     "summary": "failed_clause differs between engines when the failing step "
                "repeats a literal: Python removes repeats, the native wrapper "
                "returns the raw step."},
    {"id": "ok_empty-3", "status": "documented", "severity": "Note",
     "summary": "A top-level conflict is permanent: the clauses behind it can "
                "be deleted and `0` still passes, as in the operational flavour, "
                "not length-one. The formula is unsatisfiable, so no wrong verdict."},
    {"id": "ok_empty-4", "status": "open", "severity": "Note",
     "summary": "Where a refutation ends: conflict without a written `0` is "
                "rejected, and steps after the empty clause, or any proof on a "
                "UP-refuted input, are not read, so `steps` stops short."},
]

NOT_CHECKED = [
    "drat-trim is not on PATH, so nothing here compares with it; ok_empty-4 "
    "describes dratify's behaviour only and asserts nothing about drat-trim.",
    "Input formulas with tautologies or repeated literals: the parser normalises "
    "them and the oracle's multiset would differ. Repeats in proof steps are covered.",
    "Proofs from real solvers: refutations here come from a small DPLL trace.",
    "Formulas above 11 variables, and fresh proof variables far above the header "
    "(the bound in _validate_steps raises, and is not judged here).",
    "Non-ASCII digits and underscores in proof tokens, which int() accepts.",
    "A registered native module that returns a malformed result; that seam is "
    "tests/test_untrusted_input.py's.",
    "cdclkit: this corner is dratify only.",
]


# ---------------------------------------------------------------- instances


@dataclass
class Instance:
    family: str
    nvars: int
    clauses: list            # DIMACS, no tautologies or repeated literals
    steps: list              # ("a" | "d", DIMACS tuple), order and repeats as written
    byte_cuts: bool = False
    malformed_tail: bool = False


def internal(lit: int) -> int:
    return 2 * (abs(lit) - 1) + (lit < 0)


def internal_steps(steps) -> list:
    return [(k, tuple(internal(l) for l in c)) for k, c in steps]


def formula_text(inst: Instance) -> str:
    body = "".join(" ".join(map(str, c)) + (" 0\n" if c else "0\n") for c in inst.clauses)
    return f"p cnf {inst.nvars} {len(inst.clauses)}\n{body}"


def render(steps, rng: random.Random) -> str:
    """The same proof, in one of the layouts a text proof may take."""
    style = rng.randrange(4)
    parts = []
    for kind, c in steps:
        body = " ".join(str(l) for l in (*c, 0))
        if kind == "d":
            body = f"d{body}" if style == 3 else f"d {body}"
        parts.append(body)
    if style == 1:
        return " ".join(parts) + ("\n" if parts else "")
    if style == 2:
        out = ["c a comment holding a false ending: 0"]
        for p in parts:
            out.extend(p.split())
            out.append("c 0")
        return "\n".join(out) + "\n"
    return "\n".join(parts) + ("\n" if parts else "")


def memory_proof(steps) -> MemoryProof:
    p = MemoryProof()
    for kind, c in internal_steps(steps):
        (p.add if kind == "a" else p.delete)(c)
    return p


def read_text(text: str):
    """This harness's own reading of a proof's tokens, or None if a clause is open."""
    out, kind, lits, opened = [], "a", [], False
    for line in text.splitlines():
        line = line.strip()
        if not line or line[0] == "c":
            continue
        for tok in line.split():
            if tok == "d":
                kind, opened = "d", True
                continue
            if tok[0] == "d":
                kind, tok = "d", tok[1:]
            if tok == "-":             # a cut through a literal: no verdict is due
                return None
            d = int(tok)
            if d == 0:
                out.append((kind, tuple(lits)))
                kind, lits, opened = "a", [], False
            else:
                lits.append(d)
                opened = True
    return None if opened else out


# ---------------------------------------------------------------- generators


def clause_of(rng, nvars, size):
    vs = rng.sample(range(1, nvars + 1), min(size, nvars))
    return [v if rng.random() < .5 else -v for v in vs]


def planted(rng, nvars, nclauses):
    """Satisfiable by construction; the oracle still judges it."""
    model = {v: rng.random() < .5 for v in range(1, nvars + 1)}
    out = []
    for _ in range(nclauses):
        c = clause_of(rng, nvars, rng.randint(2, 3))
        if not any((l > 0) == model[abs(l)] for l in c):
            c[0] = -c[0]
        out.append(c)
    return out


def chain(rng, nvars, extra):
    """A unit, then literals each implied at the root by a clause of 2 or 3."""
    order = rng.sample(range(1, nvars + 1), nvars)
    true = [v if rng.random() < .5 else -v for v in order]
    length = rng.randint(2, nvars)
    out = [[true[0]]]
    for i in range(1, length):
        reasons = rng.sample(true[:i], min(i, rng.randint(1, 2)))
        c = [true[i], *(-r for r in reasons)]
        rng.shuffle(c)
        out.append(c)
    for _ in range(extra):
        c = clause_of(rng, nvars, rng.randint(2, 3))
        if not any(l in true for l in c):
            c[0] = true[order.index(abs(c[0]))]
        if len(set(c)) == len(c) and not any(-l in c for l in c):
            out.append(c)
    rng.shuffle(out)
    return out


def square(a, b):
    return [[a, b], [a, -b], [-a, b], [-a, -b]]


def php32(base):
    x = lambda p, h: base + 2 * p + h
    return [[x(p, 0), x(p, 1)] for p in range(3)] + [
        [-x(p, h), -x(q, h)] for h in range(2) for p in range(3) for q in range(p + 1, 3)]


def unsat_formula(rng):
    """Unsatisfiable and not refuted by unit propagation alone, usually."""
    pick = rng.randrange(4)
    if pick == 0:
        a, b = rng.sample(range(1, 7), 2)
        return 6, square(a, b) + planted(rng, 6, rng.randint(0, 4))
    if pick == 1:
        return 6, php32(1)
    while True:
        n = rng.randint(4, 7)
        f = [clause_of(rng, n, 3) for _ in range(rng.randint(5 * n, 8 * n))]
        if not oracle.satisfiable(f):
            return n, f


def dpll_proof(rng, clauses, delete_children):
    """A DRUP refutation: the negated decisions of each closed branch, then `0`."""
    current = [list(c) for c in clauses]
    proof = []

    def close(decisions):
        c = tuple(-d for d in decisions)
        proof.append(("a", c))
        current.append(list(c))
        return c

    def go(decisions):
        conflict, assigned = oracle.propagate(current, decisions)
        if conflict:
            return close(decisions)
        free = sorted({abs(l) for c in clauses for l in c} - {abs(l) for l in assigned})
        if not free:
            raise AssertionError("dpll_proof was given a satisfiable formula")
        v = rng.choice(free)
        left = go([*decisions, v])
        right = go([*decisions, -v])
        parent = close(decisions)
        if delete_children:
            for child in (left, right):
                if len(child) > 1 and rng.random() < .7:
                    proof.append(("d", child))
        return parent

    go([])
    return proof


def definition_steps(rng, nvars, fresh):
    """Extended resolution: fresh <-> a and b. The steps pass only by RAT."""
    a, b = rng.sample(range(1, nvars + 1), 2)
    a = a if rng.random() < .5 else -a
    b = b if rng.random() < .5 else -b
    return [("a", (-fresh, a)), ("a", (-fresh, b)), ("a", (fresh, -a, -b))]


def with_definition(rng, nvars, proof):
    at = rng.randrange(len(proof))
    return proof[:at] + definition_steps(rng, nvars, nvars + 1) + proof[at:]


def corrupt(rng, nvars, proof):
    """One step made wrong. The oracle decides whether it still passes."""
    out = list(proof)
    additions = [i for i, (k, c) in enumerate(out) if k == "a" and c]
    if not additions:
        return out
    i = rng.choice(additions)
    c = list(out[i][1])
    move = rng.randrange(3)
    if move == 0:
        c[rng.randrange(len(c))] *= -1
    elif move == 1 and len(c) > 1:
        c.pop(rng.randrange(len(c)))
    else:
        c = clause_of(rng, nvars, rng.randint(1, 2))
    if rng.random() < .3:
        c.append(c[0])                 # a repeat in a step, usually a failing one
    out[i] = ("a", tuple(c))
    return out


def tail_steps(rng, nvars, clauses):
    """After the empty clause: anything well formed, valid-looking or not."""
    out = []
    for _ in range(rng.randint(1, 4)):
        pick = rng.randrange(7)
        if pick == 0:
            out.append(("a", ()))
        elif pick == 1:
            out.append(("d", ()))
        elif pick == 2 and clauses:
            out.append(("d", tuple(rng.choice(clauses))))
        elif pick == 3:
            out.append(("a", (nvars + 1,)))
        elif pick == 4:
            c = clause_of(rng, nvars, 1)
            out.append(("a", (c[0], c[0])))
        else:
            out.append(("a", tuple(clause_of(rng, nvars, rng.randint(1, 3)))))
    return out


def reason_deletion(rng, nvars, clauses):
    """Delete the reasons of a root literal, then add its negation, then `0`.

    Under the documented reading the negation is RAT, vacuously, and the `0`
    is not RUP: nothing refutes what is left. Returns None without a target.
    """
    conflict, assigned = oracle.propagate(clauses)
    if conflict:
        return None
    units = {c[0] for c in clauses if len(c) == 1}
    candidates = sorted(assigned - units)
    if not candidates:
        return None
    x = rng.choice(candidates)
    holding = [c for c in clauses if x in c]
    rng.shuffle(holding)
    steps = [("d", tuple(c)) for c in holding]
    if rng.random() < .3:
        steps.insert(rng.randrange(len(steps) + 1), ("d", ()))
    lemma = [-x]
    if rng.random() < .4:
        others = [v for v in range(1, nvars + 1) if v != abs(x)]
        lemma.append(rng.choice(others) * rng.choice((1, -1)))
    steps.append(("a", tuple(lemma)))
    steps.append(("a", ()))
    return steps


def random_walk(rng, nvars, clauses):
    steps, live = [], [list(c) for c in clauses]
    for _ in range(rng.randint(1, 8)):
        pick = rng.randrange(10)
        if pick < 5:
            c = clause_of(rng, nvars, rng.randint(1, 3))
            if rng.random() < .15:
                c.append(c[-1])
            steps.append(("a", tuple(c)))
            live.append(c)
        elif pick < 8 and live:
            c = live.pop(rng.randrange(len(live)))
            steps.append(("d", tuple(c)))
        elif pick == 8:
            steps.append(("d", ()))
        else:
            steps.append(("a", ()))
    if rng.random() < .7:
        steps.append(("a", ()))
    return steps


def fixed_instances():
    """Hand-written, so that each ending is there whatever the seed does."""
    sq = square(1, 2)
    chain2 = [[-2], [1, 2]]
    cases = [
        ("no_proof", 2, sq, []),
        ("no_proof_sat", 2, [[1, 2]], []),
        ("no_clauses", 0, [], []),
        ("no_clauses_empty", 1, [], [("a", ())]),
        ("empty_on_sat", 2, [[1, 2]], [("a", ())]),
        ("truncated", 2, sq, [("a", (1,))]),
        ("conflict_no_empty", 2, sq, [("a", (1,)), ("a", (2,))]),
        ("refuted", 2, sq, [("a", (1,)), ("a", ())]),
        ("tail_invalid", 2, sq, [("a", (1,)), ("a", ()), ("a", (3,))]),
        ("tail_second_empty", 2, sq, [("a", (1,)), ("a", ()), ("a", ())]),
        ("tail_deletion", 2, sq, [("a", (1,)), ("a", ()), ("d", (1, 2)), ("d", ())]),
        ("delete_empty", 2, sq, [("d", ())]),
        ("delete_empty_sat", 1, [[1]], [("d", ())]),
        ("delete_all_then_empty", 2, sq, [("d", tuple(c)) for c in sq] + [("a", ())]),
        ("conflict_delete_empty", 2, sq,
         [("a", (1,)), *[("d", tuple(c)) for c in sq], ("a", ())]),
        ("up_unit", 1, [[1], [-1]], []),
        ("up_unit_bad", 1, [[1], [-1]], [("a", (2,))]),
        ("up_chain", 3, [[1], [-1, 2], [-2, 3], [-3, -1]], [("a", (1, 2))]),
        ("input_empty", 1, [[]], []),
        ("input_empty_steps", 2, [[], [1, 2]], [("d", (1, 2)), ("a", ())]),
        ("repeat_fail", 2, [[1, 2]], [("a", (-1, -1))]),
        ("unit_del_negate", 1, [[1]], [("d", (1,)), ("a", (-1,)), ("a", ())]),
        ("reason_kept", 2, chain2, [("a", (-1,)), ("a", ())]),
        ("reason_deleted", 2, chain2, [("d", (1, 2)), ("a", (-1,)), ("a", ())]),
    ]
    out = [Instance(f"fixed:{name}", n, [list(c) for c in f], s) for name, n, f, s in cases]
    out[7].byte_cuts = True
    out[7].malformed_tail = True
    return out


def generate(rng: random.Random):
    """One draw: a list of instances from a family, each judged on its own."""
    family = rng.randrange(7)
    if family <= 1:                 # refutations, cut at every kind of place
        nvars, clauses = unsat_formula(rng)
        proof = dpll_proof(rng, clauses, rng.random() < .5)
        if rng.random() < .3:
            proof = with_definition(rng, nvars, proof)
        if rng.random() < .15:
            proof = corrupt(rng, nvars, proof)
        whole = Instance("refutation", nvars, clauses, proof,
                         byte_cuts=rng.random() < .2,
                         malformed_tail=rng.random() < .2)
        cuts = sorted(rng.sample(range(len(proof)), min(len(proof), 6)))
        return [whole, *(Instance("truncated", nvars, clauses, proof[:c]) for c in cuts)]
    if family == 2:                 # what follows the empty clause
        nvars, clauses = unsat_formula(rng)
        proof = dpll_proof(rng, clauses, rng.random() < .5)
        return [Instance("tail", nvars, clauses, proof + tail_steps(rng, nvars, clauses),
                         malformed_tail=rng.random() < .2)]
    if family == 3:                 # bogus endings on satisfiable formulas
        nvars = rng.randint(2, 8)
        clauses = planted(rng, nvars, rng.randint(1, 3 * nvars))
        ends = rng.randrange(5)
        if ends == 0:
            steps = [("a", ())]
        elif ends == 1:
            steps = [("d", ()), ("a", ())]
        elif ends == 2:
            steps = [*definition_steps(rng, nvars, nvars + 1), ("a", ())] if nvars >= 2 else [("a", ())]
        elif ends == 3:
            u = rng.choice([1, -1]) * rng.randint(1, nvars)
            clauses = [[u], *clauses]
            steps = [("d", (u,)), ("a", (-u,)), ("a", ())]
        else:
            steps = random_walk(rng, nvars, clauses)
        return [Instance("sat_bogus", nvars, clauses, steps)]
    if family == 4:                 # the deleted reason, on both kinds of formula
        nvars = rng.randint(2, 8)
        clauses = chain(rng, nvars, rng.randint(0, 4))
        if rng.random() < .3:       # unsatisfiable, and not by propagation
            a, b = nvars + 1, nvars + 2
            nvars += 2
            clauses = clauses + square(a, b)
        steps = reason_deletion(rng, nvars, clauses)
        if steps is None:           # nothing implied at the root to aim at
            return [Instance("random_walk", nvars, clauses, random_walk(rng, nvars, clauses))]
        return [Instance("reason_deletion", nvars, clauses, steps)]
    if family == 5:                 # refuted before the proof starts
        nvars = rng.randint(1, 5)
        v = rng.randint(1, nvars)
        pick = rng.randrange(3)
        if pick == 0:
            core = [[v], [-v]]
        elif pick == 1:
            core = [[]]
        else:
            w = nvars + 1
            nvars += 1
            core = [[v], [-v, w], [-v, -w]]
        clauses = core + (planted(rng, nvars, rng.randint(0, 3)) if nvars >= 2 else [])
        return [Instance("up_refuted", nvars, clauses, random_walk(rng, nvars, clauses))]
    nvars = rng.randint(2, 7)       # no aim at all, to catch what the aims miss
    clauses = [clause_of(rng, nvars, rng.randint(1, 3))
               for _ in range(rng.randint(1, 4 * nvars))]
    return [Instance("random_walk", nvars, clauses, random_walk(rng, nvars, clauses))]


# ---------------------------------------------------------------- the checker


def real_check(inst, proof, steps, check_rat, apply_deletions, engine):
    r = check_proof(parse_dimacs(formula_text(inst)), proof, check_rat=check_rat,
                    apply_deletions=apply_deletions, engine=engine)
    return {f: getattr(r, f) for f in FIELDS}


# ---------------------------------------------------------------- the judge


class Run:
    def __init__(self, check):
        self.check = check
        self.counts = Counter()
        self.mismatches = Counter()
        self.examples = {}
        self.instances = 0

    def tally(self, name, n=1):
        self.counts[name] += n

    def mismatch(self, label, what, inst, flags, engine, detail=""):
        key = f"{label}: {what}"
        self.mismatches[key] += 1
        self.examples.setdefault(key, {
            "family": inst.family, "formula": inst.clauses,
            "steps": [[k, list(c)] for k, c in inst.steps],
            "check_rat": flags[0], "apply_deletions": flags[1],
            "engine": engine, "detail": str(detail)})


def distinct(c):
    return tuple(dict.fromkeys(c))


def compare_results(run, inst, flags, label, a, b, engines):
    """Two results that must be equal, in every field."""
    if a == b:
        return
    differ = [f for f in FIELDS if a.get(f) != b.get(f)]
    run.mismatch("UNEXPLAINED",
                 f"{label}: fields differ ({','.join(differ)})", inst, flags, engines,
                 {f: (a.get(f), b.get(f)) for f in differ})


def judge(run, inst, r, flags, engine):
    """One result against the oracle, under the reading dratify documents."""
    check_rat, apply_deletions = flags
    F, steps = inst.clauses, inst.steps
    sat = oracle.satisfiable(F)
    wrong = lambda what, detail="": run.mismatch("UNEXPLAINED", what, inst, flags, engine, detail)

    if r["ok"] != r["reached_empty"]:
        wrong("ok and reached_empty differ", (r["ok"], r["reached_empty"]))
    if sat:
        run.tally("sat_formula_checks")
    if r["ok"] and not sat:
        run.tally("ok_true_on_unsat")

    if oracle.propagate(F)[0]:      # refuted before any step is read
        run.tally("up_refuted_input_checks")
        if any(not c for c in F):
            run.tally("input_contains_empty_clause")
        if any(k == "a" and c for k, c in steps):
            run.tally("up_refuted_input_with_invalid_step")
        if not (r["ok"] and r["reached_empty"] and r["steps"] == 0 and r["failed_step"] == -1):
            wrong("input refuted by propagation was not accepted at once", r)
        return

    first_empty = next((i for i, (k, c) in enumerate(steps) if k == "a" and not c), None)
    has_empty = first_empty is not None
    scope = steps[:first_empty + 1] if has_empty else steps
    if not has_empty and (r["ok"] or r["reached_empty"]):
        wrong("accepted a proof with no empty clause", r)

    current = [list(c) for c in F]
    n_rup = n_rat = n_del = n_ign = 0
    outcome = None

    for j, (kind, clause) in enumerate(scope, 1):
        if kind == "d":
            if r["failed_step"] == j:
                wrong("a deletion was reported as the failed step", j)
            size = len(set(clause))
            if not clause:
                run.tally("delete_empty_steps")
            if size <= 1:
                n_ign += 1
                run.tally("deletions_ignored")
            elif apply_deletions:
                after, present = oracle.remove_one(current, clause)
                if (present and not oracle.propagate(current)[0]
                        and not oracle.is_pseudo_unit(current, clause)):
                    current = after
                    n_del += 1
                    run.tally("deletions_applied")
                else:
                    n_ign += 1
                    run.tally("deletions_ignored")
            continue

        is_rup = oracle.rup(current, clause)
        is_rat = bool(check_rat and clause and oracle.rat(current, clause, clause[0]))
        acceptable = is_rup or is_rat
        run.tally("oracle_steps_judged")
        if not clause:
            run.tally("sat_formula_empty_attempted" if sat else "unsat_formula_empty_attempted")

        if r["failed_step"] == j:
            if acceptable:
                run.mismatch("UNEXPLAINED", "rejected a step that is RUP or RAT on its "
                             "first literal", inst, flags, engine, j)
            else:
                run.tally("rejected_steps_agreeing")
                if not clause:
                    run.tally("empty_step_rejected")
                if len(set(clause)) != len(clause):
                    run.tally("repeated_literal_rejections")
            if r["ok"] or r["reached_empty"] or r["steps"] != j:
                wrong("a rejection did not stop at its step", r)
            if r["rup_steps"] + r["rat_steps"] != n_rup + n_rat:
                wrong("additions before the failed step miscounted", r)
            if r["failed_clause"] is None or set(r["failed_clause"]) != {internal(l) for l in clause}:
                wrong("failed_clause is not the failing step", r)
            outcome = "rejected"
            break

        if not acceptable:
            wrong("accepted a step the oracle refuses", (j, clause))
            outcome = "accepted"
            break

        if is_rup:
            n_rup += 1
        else:
            n_rat += 1
            run.tally("accepted_only_by_rat")
        if not clause:
            run.tally("empty_step_accepted")
            break
        current.append(list(clause))

    if r["ok"] and sat:
        wrong("ok=True on a satisfiable formula", r)

    if outcome is None:             # every step agreed: the ending is now determined
        if has_empty:
            if not r["ok"] or r["steps"] != first_empty + 1 or r["failed_step"] != -1:
                wrong("a refutation valid under the oracle was not accepted", r)
        else:
            if r["ok"] or r["reason"] != NEVER or r["steps"] != len(steps) or r["failed_step"] != -1:
                wrong("a proof with no empty clause ended wrongly", r)
            run.tally("truncated_no_empty_rejected")
            if oracle.propagate(current)[0]:
                run.tally("truncated_after_top_level_conflict")
            if any(k == "d" and not c for k, c in steps):
                run.tally("delete_empty_not_a_refutation")
        if r["rup_steps"] + r["rat_steps"] != n_rup + n_rat:
            wrong("rup_steps + rat_steps is not the additions accepted", r)
        if r["deletions"] != n_del or r["ignored_deletions"] != n_ign:
            wrong("deletions miscounted", (r, n_del, n_ign))
        if (r["rup_steps"], r["rat_steps"]) != (n_rup, n_rat):
            wrong("rup_steps and rat_steps differ from the oracle's", (r, n_rup, n_rat))
        if r["failed_clause"] is not None:
            wrong("failed_clause set on a proof with no failed step", r)

    if inst.family == "reason_deletion":
        run.tally("reason_deletion_then_rat_attempted")
    if inst.family.startswith("sat_bogus") or inst.family == "fixed:unit_del_negate":
        if (len(steps) == 3 and steps[0][0] == "d" and len(steps[0][1]) == 1
                and steps[1][1] == (-steps[0][1][0],)):
            if not r["ok"]:
                run.tally("unit_deletion_then_negation_rejected")


def judge_tail(run, inst, flags, full_py, full_native):
    """What follows the first empty clause must change nothing."""
    F, steps = inst.clauses, inst.steps
    first = next((i for i, (k, c) in enumerate(steps) if k == "a" and not c), None)
    if first is None or first == len(steps) - 1:
        return
    scope, tail = steps[:first + 1], steps[first + 1:]
    baseline = run.check(inst, internal_steps(scope), scope, *flags, "python")
    compare_results(run, inst, flags, "a tail changed the result", full_py, baseline,
                    "python+tail vs python")
    baseline_native = run.check(inst, internal_steps(scope), scope, *flags, "native")
    compare_results(run, inst, flags, "a tail changed the native result", full_native,
                    baseline_native, "native+tail vs native")
    run.tally("tail_instances")
    run.tally("tail_steps", len(tail))
    # The oracle's view: on the multiset before the empty clause, a tail addition
    # may be no good at all; on the one holding it, every addition passes. So
    # skipping the tail cannot hide a step that had to fail.
    before = [list(c) for c in F] + [list(c) for k, c in scope if k == "a" and c]
    for kind, clause in tail:
        if kind == "d":
            run.tally("tail_deletions")
        elif not clause:
            run.tally("tail_second_empty")
        else:
            if not oracle.rup(before, clause) and not oracle.rat(before, clause, clause[0]):
                run.tally("tail_additions_not_acceptable_before_empty")
            if not oracle.rup([*before, []], clause):
                run.mismatch("UNEXPLAINED", "the oracle refused a step once refuted",
                             inst, flags, "oracle", clause)


def judge_instance(run, inst, rng):
    run.instances += 1
    text = render(inst.steps, rng)
    as_list = internal_steps(inst.steps)
    for flags in FLAGS:
        def call(proof, engine):
            try:
                return run.check(inst, proof, inst.steps, *flags, engine)
            except ValueError as e:
                run.mismatch("UNEXPLAINED", "raised on a well-formed proof", inst, flags, engine, e)
                return None

        py = call(text, "python")
        native = call(text, "native")
        py_list = call(as_list, "python")
        native_list = call(as_list, "native")
        py_memory = call(memory_proof(inst.steps), "python")
        if None in (py, native, py_list, native_list, py_memory):
            continue
        run.tally("route_text", 2)
        run.tally("route_list", 2)
        run.tally("route_memory")
        run.tally("compared_python_native", 2)
        compare_results(run, inst, flags, "python vs native", py, native, "both")
        compare_results(run, inst, flags, "python text vs list", py, py_list, "python")
        compare_results(run, inst, flags, "python text vs memory", py, py_memory, "python")
        compare_results(run, inst, flags, "native text vs list", native, native_list, "native")
        judge(run, inst, py, flags, "python")
        judge(run, inst, native, flags, "native")
        judge_tail(run, inst, flags, py, native)

    flags = FLAGS[0]
    if inst.byte_cuts:
        base = render(inst.steps, random.Random(0))
        cuts = rng.sample(range(len(base)), min(len(base), 16))
        for cut in cuts:
            cut_text = base[:cut]
            cut_steps = read_text(cut_text)
            sub = Instance("truncated", inst.nvars, inst.clauses, cut_steps or [])
            for engine in ("python", "native"):
                try:
                    r = run.check(inst, cut_text, cut_steps, *flags, engine)
                except ValueError:
                    if cut_steps is None:
                        run.tally("byte_cut_raised")
                    else:
                        run.mismatch("UNEXPLAINED", "a byte cut at a clause boundary raised",
                                     sub, flags, engine, repr(cut_text))
                    continue
                if cut_steps is None:
                    run.mismatch("UNEXPLAINED", "a byte cut inside a clause was given a verdict",
                                 inst, flags, engine, repr(cut_text))
                    continue
                run.tally("byte_cut_judged")
                judge(run, sub, r, flags, engine)
    if inst.malformed_tail:
        base = render(inst.steps, random.Random(0))
        for junk in (" junk", "\n1 2", "\nd", " 0x"):
            for engine in ("python", "native"):
                try:
                    r = run.check(inst, base + junk, None, *flags, engine)
                except ValueError:
                    run.tally("tail_malformed_raised")
                else:
                    run.mismatch("UNEXPLAINED", "malformed text after the proof got a verdict",
                                 inst, flags, engine, (junk, r))
        bad = internal_steps(inst.steps) + [("a", (-5,))]
        for engine in ("python", "native"):
            try:
                r = run.check(inst, bad, None, *flags, engine)
            except ValueError:
                run.tally("tail_malformed_raised")
            else:
                run.mismatch("UNEXPLAINED", "a negative internal literal in the tail got a verdict",
                             inst, flags, engine, r)


def sweep(run, seed, instances):
    rng = random.Random(seed)
    for inst in fixed_instances():
        judge_instance(run, inst, rng)
    for _ in range(instances):
        for inst in generate(rng):
            judge_instance(run, inst, rng)


def empty_categories(counts):
    return [c for c in REQUIRED if counts[c] == 0]


# ---------------------------------------------------------------- the self-test


def model_check(bug, inst, proof, steps, check_rat, apply_deletions, engine):
    """A checker written from the oracle, correct unless `bug` says otherwise."""
    if steps is None:
        if bug == "ignores_malformed":
            return dict(ok=False, reached_empty=False, reason="", steps=0, rup_steps=0,
                        rat_steps=0, deletions=0, ignored_deletions=0, resolvents_checked=0,
                        failed_step=-1, failed_clause=None)
        raise ValueError("malformed")
    r = dict(ok=False, reached_empty=False, reason=NEVER, steps=0, rup_steps=0,
             rat_steps=0, deletions=0, ignored_deletions=0, resolvents_checked=0,
             failed_step=-1, failed_clause=None)
    if bug == "accept_all":
        r.update(ok=True, reached_empty=True, reason="accepted", steps=len(steps))
        first = next((i for i, (k, c) in enumerate(steps) if k == "a" and not c), None)
        r["steps"] = 0 if oracle.propagate(inst.clauses)[0] else (
            first + 1 if first is not None else len(steps))
        return r
    if bug == "reject_all":
        r["reason"] = "rejected"
        return r
    current = [list(c) for c in inst.clauses]
    if oracle.propagate(current)[0]:
        r.update(ok=True, reached_empty=True, reason="input formula is refuted")
        return r
    retained = set(oracle.propagate(current)[1])
    for kind, clause in steps:
        if r["reached_empty"] and bug != "reads_tail":
            break
        r["steps"] += 1
        if kind == "d":
            if bug == "d0_is_empty" and not clause:
                r["reached_empty"] = True
                continue
            if len(set(clause)) <= 1:
                r["ignored_deletions"] += 1
            elif apply_deletions:
                if bug != "retained" and (oracle.propagate(current)[0]
                                          or oracle.is_pseudo_unit(current, clause)):
                    r["ignored_deletions"] += 1
                    continue
                current, present = oracle.remove_one(current, clause)
                r["deletions" if present else "ignored_deletions"] += 1
            continue
        view = current + [[l] for l in retained] if bug == "retained" else current
        is_rup = oracle.rup(view, clause)
        is_rat = False
        if not is_rup and check_rat and clause:
            # candidates from the clauses present, RUP on what the old rule kept
            pivot, lits = clause[0], set(clause)
            is_rat = (all(oracle.rup(view, lits | (set(d) - {-pivot}))
                          for d in current if -pivot in d)
                      if bug == "retained" else oracle.rat(current, clause, clause[0]))
        if is_rup:
            r["rup_steps"] += 1
        elif is_rat:
            r["rat_steps"] += 1
        else:
            r.update(failed_step=r["steps"], reason="rejected",
                     failed_clause=tuple(distinct(internal(l) for l in clause)))
            r["reached_empty"] = False
            return r
        if not clause:
            r["reached_empty"] = True
            continue
        current.append(list(clause))
        if bug == "retained":
            retained |= set(oracle.propagate(view + [list(clause)])[1])
        if bug == "conflict_is_enough" and oracle.propagate(current)[0]:
            r.update(ok=True, reached_empty=True, reason="conflict")
            return r
    if bug == "truncation_accepted" and r["failed_step"] == -1:
        r.update(ok=True, reached_empty=True, reason="accepted")
        return r
    r["ok"] = r["reached_empty"]
    if r["ok"]:
        r["reason"] = "empty clause derived and every step verified"
    if bug == "ok_only" and r["ok"]:
        r["reached_empty"] = False
    if bug == "reached_always":
        r["reached_empty"] = True
    if bug == "engines_differ" and engine == "native":
        r["resolvents_checked"] += 1
    return r


#: stub -> a substring some flagged mismatch must contain
STUBS = {
    "accept_all": "ok=True on a satisfiable formula",
    "reject_all": "a refutation valid under the oracle was not accepted",
    "truncation_accepted": "accepted a proof with no empty clause",
    "conflict_is_enough": "accepted a proof with no empty clause",
    "ok_only": "ok and reached_empty differ",
    "reached_always": "ok and reached_empty differ",
    "reads_tail": "a tail changed the result",
    "d0_is_empty": "accepted a proof with no empty clause",
    "retained": "ok=True on a satisfiable formula",
    "engines_differ": "python vs native",
    "ignores_malformed": "got a verdict",
}


def self_test(seed, instances):
    failed = False
    for name, expected in STUBS.items():
        run = Run(lambda *a, bug=name: model_check(bug, *a))
        sweep(run, seed, instances)
        hit = sum(n for k, n in run.mismatches.items() if expected in k)
        ok = hit > 0
        failed |= not ok
        print(f"  {'flagged' if ok else 'MISSED ':8} {name:22} {hit:6} hits of {expected!r}; "
              f"{sum(run.mismatches.values())} mismatches in all")
    run = Run(lambda *a: model_check(None, *a))
    sweep(run, seed, instances)
    total = sum(run.mismatches.values())
    print(f"  {'clean' if not total else 'FLAGGED':8} the correct stub: {total} mismatches, "
          f"empty categories {empty_categories(run.counts)}")
    if total:
        failed = True
        for key, n in run.mismatches.most_common(8):
            print(f"      {n} {key}\n        {run.examples[key]}")
    empty = Run(lambda *a: model_check(None, *a))
    gate = len(empty_categories(empty.counts)) == len(REQUIRED)
    print(f"  {'gated' if gate else 'NOT GATED':8} a run that reaches nothing fails its categories")
    failed |= not gate
    print("self-test " + ("FAILED" if failed else "passed"))
    return 1 if failed else 0


# ---------------------------------------------------------------- main


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--seed", type=int, default=20261108)
    parser.add_argument("--instances", type=int, default=1200)
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--results", default="campaign/results/ok_empty.json",
                        help="where to write the results; '' for nowhere")
    args = parser.parse_args(argv)

    if args.self_test:
        return self_test(args.seed, min(args.instances, 120))

    try:
        import cdclkit_native
    except ImportError:
        print("FAILED: no native checker, and both engines are the point of this corner")
        return 1
    register_native(cdclkit_native)

    started = time.time()
    run = Run(real_check)
    try:
        sweep(run, args.seed, args.instances)
    finally:
        register_native(None)
    elapsed = time.time() - started

    empty = empty_categories(run.counts)
    print(f"seed {args.seed}: {run.instances} instances, "
          f"{run.counts['oracle_steps_judged']} oracle-judged steps, {elapsed:.1f}s")
    for name in REQUIRED:
        print(f"  {name:48} {run.counts[name]}")
    for key, n in sorted(run.mismatches.items()):
        print(f"MISMATCH {n:7} {key}\n         first: {json.dumps(run.examples[key], default=str)[:600]}")
    if empty:
        print(f"FAILED: categories never reached: {empty}")

    if args.results:
        result = {
            "corner": "ok_empty",
            "seeds": [args.seed],
            "instances": run.instances,
            "steps": run.counts["oracle_steps_judged"],
            "per_category_counts": {k: run.counts[k] for k in REQUIRED},
            "mismatches": dict(sorted(run.mismatches.items())),
            "runtime_seconds": round(elapsed, 1),
            "findings": FINDINGS,
            "not_checked": NOT_CHECKED,
        }
        path = pathlib.Path(args.results)
        path.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")

    unexplained = sum(n for k, n in run.mismatches.items() if k.startswith("UNEXPLAINED"))
    known = sum(run.mismatches.values()) - unexplained
    print(f"{unexplained} unexplained mismatches, {known} labelled with known findings, "
          f"{len(empty)} empty categories")
    return 1 if run.mismatches or empty else 0


if __name__ == "__main__":
    sys.exit(main())
