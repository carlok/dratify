# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Run dratify beside an external DRAT checker and classify every disagreement.

Two external checkers are supported, and they are never confused in the output:

* ``drat-trim``, when one is on PATH or given by ``--drat-trim PATH``. It reads
  from its stdout (``s VERIFIED`` / ``s NOT VERIFIED``), never from its exit
  code, which has its own meanings, and it runs with its ``-t`` time limit.
* ``rate``, the independent checker on crates.io (``cargo install rate``), when
  one is on PATH or given by ``--rate PATH``. It is not drat-trim. Everything it
  produces is counted under a ``rate_`` key.

``rate`` runs in four modes, all with ``-p`` so that the pivot is the first
literal, as it is in dratify and in drat-trim's default:

    ========== ============ ===========================================
    mode       flags        reading of a deletion
    ========== ============ ===========================================
    fwd-spec   -f -p        specified: every deletion happens
    fwd-skip   -f -p -d     skips deletions of clauses unit at the root
    bwd-spec   -p           specified, backward
    bwd-skip   -p -d        rate's "drat-trim compatibility"
    ========== ============ ===========================================

dratify's documented reading is the oracle's ``length-one`` flavour: deletions
are applied, except that a deletion of a clause of at most one literal is
ignored. ``DOCUMENTED_FLAVOUR`` names it, and every dratify verdict is judged
against it and against ``satisfiable`` before any external checker is consulted.

What a disagreement can be:

* a **Note**, when the two flavours of DRAT or backward checking explain it;
* a **Critical** or **Bug**, when dratify is wrong by the oracle;
* **unexplained**, which fails the run until someone has looked at it.

Run from the repository root:

    python -m campaign.gen_drat_trim --rate PATH
    python -m campaign.gen_drat_trim --self-test --rate PATH
"""

from __future__ import annotations

import argparse
import collections
import json
import pathlib
import random
import shutil
import subprocess
import sys
import tempfile
import time

from campaign import oracle
from dratify import DRATChecker, check_proof, parse_dimacs, parse_proof, register_native

CORNER = "drat_trim"
DOCUMENTED_FLAVOUR = "length-one"
RESULT_FIELDS = ("ok", "reason", "steps", "rup_steps", "rat_steps", "deletions",
                 "ignored_deletions", "resolvents_checked", "failed_step",
                 "failed_clause", "reached_empty")
# mode -> (flags, direction, oracle flavour nearest to it)
RATE_MODES = {
    "fwd-spec": (["-f", "-p"], "fwd", "specified"),
    "fwd-skip": (["-f", "-p", "-d"], "fwd", "operational"),
    "bwd-spec": (["-p"], "bwd", "specified"),
    "bwd-skip": (["-p", "-d"], "bwd", "operational"),
}
TIMEOUT = 20
#: every finding whose cause this generator can recognise, for labelling only
STALE_ROOT_FINDING = "drat_trim-1"
CRITICAL_KINDS = {"ok_on_satisfiable", "rup_not_implied", "accepted_not_preserving"}
BUG_KINDS = {"accepted_unacceptable", "false_rejection", "engine_disagreement",
             "field_mismatch", "verdict_mismatch"}


# --------------------------------------------------------------------------
# text formats
# --------------------------------------------------------------------------


def cnf_text(formula):
    nvars = max((abs(l) for c in formula for l in c), default=0)
    lines = [f"p cnf {max(nvars, 1)} {len(formula)}"]
    lines += [" ".join(map(str, [*c, 0])) for c in formula]
    return "\n".join(lines) + "\n"


def proof_text(steps):
    out = []
    for kind, lits in steps:
        head = "d " if kind == "d" else ""
        out.append(head + " ".join(map(str, [*lits, 0])))
    return "\n".join(out) + ("\n" if out else "")


def read_proof(text):
    steps = []
    for line in text.splitlines():
        toks = line.split()
        if not toks or toks[0] == "c":
            continue
        kind = "d" if toks[0] == "d" else "a"
        lits = [int(t) for t in toks if t != "d"]
        steps.append((kind, tuple(lits[:-1])))
    return steps


# --------------------------------------------------------------------------
# what the oracle says about a proof
# --------------------------------------------------------------------------


class Walk:
    """One flavour's reading of a proof, stopped where a checker would stop."""

    def __init__(self, formula, steps, flavour):
        cut = []
        for kind, lits in steps:
            cut.append((kind, lits))
            if kind == "a" and not lits:
                break
        self.judged, _ = oracle.replay(formula, cut, flavour)
        self.first_bad = next(
            (s.index for s in self.judged if not s.acceptable), None)
        self.refuted_at = 0 if oracle.propagate(formula)[0] else None
        self.unrefuted = False        # a deletion undid a propagation conflict
        self.root_shrunk_at = None    # first deletion that shrinks the root
        self.shrinks = 0
        current = [list(c) for c in formula]
        before = oracle.propagate(current)
        for step in self.judged:
            if step.kind == "a":
                if step.acceptable:
                    current.append(list(step.clause))
            elif step.applied:
                current, _ = oracle.remove_one(current, step.clause)
            now = oracle.propagate(current)
            if step.kind == "d" and step.applied and not before[0] and not now[0] \
                    and not before[1] <= now[1]:
                self.shrinks += 1
                if self.root_shrunk_at is None:
                    self.root_shrunk_at = step.index
            if now[0] and self.refuted_at is None:
                self.refuted_at = step.index
            if self.refuted_at is not None and not now[0]:
                self.unrefuted = True
            before = now
        last = self.judged[-1] if self.judged else None
        self.explicit = bool(
            last and last.kind == "a" and not last.clause and last.acceptable)

    @property
    def input_refuted(self):
        return self.refuted_at == 0

    @property
    def expected_ok(self):
        """A refutation as dratify documents it: an explicit, valid empty clause."""
        return self.input_refuted or self.explicit

    @property
    def accepts_like_external(self):
        """External checkers stop at the first propagation conflict."""
        return self.refuted_at is not None


# --------------------------------------------------------------------------
# dratify, and the stubs the self-test puts in its place
# --------------------------------------------------------------------------


class Dratify:
    name = "dratify"

    @staticmethod
    def run(formula, steps, engine):
        result = check_proof(parse_dimacs(cnf_text(formula)), proof_text(steps),
                             engine=engine)
        return {f: getattr(result, f) for f in RESULT_FIELDS}

    @staticmethod
    def labels(formula, steps):
        """What the Python engine called each step, in order, or None."""
        checker = DRATChecker(parse_dimacs(cnf_text(formula)))
        if checker._root_conflict:
            return []
        out = []
        r = checker.result
        for kind, lits in parse_proof(proof_text(steps)):
            rup, rat = r.rup_steps, r.rat_steps
            if not checker.check_step(kind, lits):
                out.append("fail")
                break
            out.append("rup" if r.rup_steps > rup else "rat" if r.rat_steps > rat
                       else "del")
            if r.reached_empty:
                break
        return out


def _blank(**fields):
    base = dict(ok=False, reason="", steps=0, rup_steps=0, rat_steps=0, deletions=0,
                ignored_deletions=0, resolvents_checked=0, failed_step=-1,
                failed_clause=None, reached_empty=False)
    base.update(fields)
    return base


class AcceptAll:
    name = "stub: accepts everything"

    @staticmethod
    def run(formula, steps, engine):
        return _blank(ok=True, reached_empty=True, steps=len(steps))

    @staticmethod
    def labels(formula, steps):
        return None


class RejectAll:
    name = "stub: rejects at the first step"

    @staticmethod
    def run(formula, steps, engine):
        return _blank(steps=1, failed_step=1)

    @staticmethod
    def labels(formula, steps):
        return None


class EngineSkew(Dratify):
    name = "stub: native miscounts deletions"

    @staticmethod
    def run(formula, steps, engine):
        r = Dratify.run(formula, steps, "python")
        if engine == "native":
            r["deletions"] += 1
        return r


class Reference:
    """The documented semantics, computed by the oracle: nothing may be flagged."""

    name = "stub: the documented semantics, from the oracle"

    @staticmethod
    def run(formula, steps, engine):
        w = Walk(formula, steps, DOCUMENTED_FLAVOUR)
        if w.input_refuted:
            return _blank(ok=True, reached_empty=True)
        r = _blank(ok=w.expected_ok, reached_empty=w.expected_ok,
                   steps=len(w.judged), failed_step=w.first_bad or -1)
        for s in w.judged:
            if s.kind == "d":
                r["deletions" if s.applied else "ignored_deletions"] += 1
            elif s.rup:
                r["rup_steps"] += 1
            elif s.rat_on_first:
                r["rat_steps"] += 1
        return r

    @staticmethod
    def labels(formula, steps):
        return None


# --------------------------------------------------------------------------
# external checkers
# --------------------------------------------------------------------------


def stdout_verdict(stdout):
    """True, False, or None when the checker did not reach a verdict."""
    lines = [line.strip() for line in stdout.splitlines()]
    if "s NOT VERIFIED" in lines:
        return False
    if "s VERIFIED" in lines:
        return True
    return None


class External:
    """Runs whichever checkers exist, on one formula and proof at a time."""

    def __init__(self, rate, drat_trim, workdir):
        self.rate = rate
        self.drat_trim = drat_trim
        self.cnf = pathlib.Path(workdir) / "instance.cnf"
        self.proof = pathlib.Path(workdir) / "instance.drat"

    def _run(self, argv, limit):
        try:
            done = subprocess.run(argv, capture_output=True, text=True, timeout=limit)
        except subprocess.TimeoutExpired:
            return None
        return stdout_verdict(done.stdout)

    def verdicts(self, formula, steps):
        self.cnf.write_text(cnf_text(formula))
        self.proof.write_text(proof_text(steps))
        out = {}
        if self.rate:
            for mode, (flags, _, _) in RATE_MODES.items():
                out[f"rate/{mode}"] = self._run(
                    [self.rate, *flags, str(self.cnf), str(self.proof)], TIMEOUT)
        if self.drat_trim:
            # drat-trim's exit code is not a verdict, so only stdout is read
            out["drat-trim"] = self._run(
                [self.drat_trim, str(self.cnf), str(self.proof), "-t", str(TIMEOUT)],
                TIMEOUT + 5)
        return out


def checker_reading(name):
    """(direction, oracle flavour) for an external checker's name."""
    if name == "drat-trim":
        return "bwd", "operational"
    _, direction, flavour = RATE_MODES[name.split("/")[1]]
    return direction, flavour


# --------------------------------------------------------------------------
# judging one instance
# --------------------------------------------------------------------------


class Analysis:
    def __init__(self):
        self.mismatches = []   # (severity, kind, detail): fail the run
        self.notes = []        # note categories: explained, do not fail it

    def flag(self, severity, kind, detail=""):
        self.mismatches.append((severity, kind, detail))

    @property
    def kinds(self):
        return {kind for _, kind, _ in self.mismatches}


def judge_dratify(formula, steps, checker, walk, sat, a):
    """dratify against the oracle: both engines, every field, before any tool."""
    py = checker.run(formula, steps, "python")
    native = checker.run(formula, steps, "native")
    for field in RESULT_FIELDS:
        if py[field] != native[field]:
            a.flag("Bug", "engine_disagreement",
                   f"{field}: python={py[field]!r} native={native[field]!r}")

    for name, r in (("python", py), ("native", native)):
        if r["ok"] and sat:
            a.flag("Critical", "ok_on_satisfiable", f"{name} engine")

    # Steps past a refutation are not comparable: dratify stops looking, and a
    # later deletion may undo the propagation conflict without undoing the fact.
    labels = checker.labels(formula, steps)
    failed = py["failed_step"] if py["failed_step"] > 0 else None
    bad = walk.first_bad
    over = False
    if not walk.input_refuted and bad is not None and (failed is None or bad < failed):
        over = True
        if walk.refuted_at is not None and walk.refuted_at < bad:
            a.notes.append("note_sticky_refutation")
        else:
            step = walk.judged[bad - 1]
            label = labels[bad - 1] if labels and bad <= len(labels) else None
            where = f"step {bad} {step.clause}, labelled {label}"
            if label == "rup" and not step.implied:
                a.flag("Critical", "rup_not_implied", where)
            elif not step.preserves_sat:
                a.flag("Critical", "accepted_not_preserving", where)
            else:
                a.flag("Bug", "accepted_unacceptable", where)
    elif failed is not None and (bad is None or failed < bad) and not walk.input_refuted:
        a.flag("Bug", "false_rejection", f"step {failed}")
    if labels:
        for label, step in zip(labels, walk.judged):
            # past a real refutation every clause is implied by what was refuted,
            # even if a later deletion has undone the propagation conflict
            refuted = walk.refuted_at is not None and walk.refuted_at < step.index
            if label == "rup" and step.kind == "a" and not step.implied \
                    and step.acceptable and not refuted:
                a.flag("Critical", "rup_not_implied",
                       f"step {step.index} {step.clause} accepted as RUP")
    if not over and py["ok"] != walk.expected_ok and not walk.unrefuted:
        a.flag("Bug", "verdict_mismatch",
               f"ok={py['ok']}, documented semantics say {walk.expected_ok}")
    if not over and not walk.input_refuted and not walk.unrefuted and failed == bad:
        counted = {
            "rup_steps": sum(1 for s in walk.judged if s.kind == "a" and s.rup),
            "rat_steps": sum(1 for s in walk.judged if s.kind == "a" and not s.rup
                             and s.rat_on_first),
            "deletions": sum(1 for s in walk.judged if s.kind == "d" and s.applied),
            "ignored_deletions": sum(1 for s in walk.judged
                                     if s.kind == "d" and not s.applied),
            "reached_empty": walk.explicit,
        }
        for field, want in counted.items():
            if py[field] != want:
                a.flag("Bug", "field_mismatch", f"{field}={py[field]}, oracle {want}")
    return py


def judge_external(name, theirs, ours, walks, verdicts, sat, a, counts):
    """Explain one disagreement, or say that it cannot be explained."""
    tag = "rate_" + name.split("/")[1].replace("-", "_") if name.startswith("rate/") \
        else "drat_trim"
    if theirs is None:
        counts[f"{tag}_no_verdict"] += 1
        if name.startswith("rate/"):   # drat-trim's timeouts are reported, not judged
            a.flag("Bug", "external_no_verdict", name)
        return
    counts[f"{tag}_run"] += 1
    if theirs and sat:
        # No flavour and no backward pass can explain this: it is that checker's
        # own soundness in question, and a claim that needs a human either way.
        a.flag("Bug", "external_accepted_satisfiable", f"{name} said VERIFIED")
    if theirs == ours["ok"]:
        counts[f"{tag}_agree"] += 1
        return
    counts[f"{tag}_disagree"] += 1
    direction, flavour = checker_reading(name)
    documented = walks[DOCUMENTED_FLAVOUR]
    reading = walks[flavour]

    def note(category):
        counts[f"{tag}_{category}"] += 1
        a.notes.append(category)

    if ours["ok"]:
        counts[f"{tag}_dratify_accepts_it_rejects"] += 1
        if a.mismatches:
            note("follows_dratify_mismatch")     # already a failure above
        elif documented.expected_ok and not reading.accepts_like_external:
            note("note_deletion_flavour")
        elif not documented.expected_ok:
            note("note_sticky_refutation")       # truly refuted before this point
        else:
            a.flag("Bug", "external_unexplained",
                   f"dratify accepted, {name} rejected, oracle {flavour} accepts")
        return

    counts[f"{tag}_it_accepts_dratify_rejects"] += 1
    forward = verdicts.get(f"rate/fwd-{'spec' if flavour == 'specified' else 'skip'}")
    if forward is None:
        forward = reading.accepts_like_external
    if a.mismatches:
        note("follows_dratify_mismatch")
    elif direction == "bwd" and not forward and not sat:
        note("note_backward_skips_unused")
    elif documented.accepts_like_external and not documented.explicit:
        # it stops at the first propagation conflict; dratify asks for the clause
        note("note_implicit_empty_clause")
    elif reading.accepts_like_external and not documented.accepts_like_external:
        note("note_deletion_flavour")
    else:
        a.flag("Bug", "external_unexplained",
               f"{name} accepted, dratify rejected, oracle {flavour} "
               f"{'accepts' if reading.accepts_like_external else 'rejects'}")


def analyse(formula, steps, checker, external, counts):
    a = Analysis()
    sat = oracle.satisfiable(formula)
    walks = {f: Walk(formula, steps, f) for f in oracle.FLAVOURS}
    ours = judge_dratify(formula, steps, checker, walks[DOCUMENTED_FLAVOUR], sat, a)
    verdicts = external.verdicts(formula, steps)
    for name, theirs in verdicts.items():
        judge_external(name, theirs, ours, walks, verdicts, sat, a, counts)

    walk = walks[DOCUMENTED_FLAVOUR]
    counts["instances"] += 1
    counts["steps_judged"] += len(walk.judged)
    counts["formulas_satisfiable" if sat else "formulas_unsatisfiable"] += 1
    counts["dratify_ok" if ours["ok"] else "dratify_rejected"] += 1
    counts["dratify_rejected_a_step"] += ours["failed_step"] > 0
    for s in walk.judged:
        if s.kind == "d":
            counts["deletions_applied" if s.applied else
                   "deletions_absent" if not s.present else
                   "deletions_ignored_as_unit"] += 1
        elif s.rup:
            counts["additions_rup"] += 1
        elif s.rat_on_first:
            counts["additions_rat_only"] += 1
        else:
            counts["additions_unacceptable"] += 1
    counts["deletions_shrinking_the_root"] += walk.shrinks
    counts["proofs_with_implicit_empty_clause"] += (
        walk.first_bad is None and walk.refuted_at not in (None, 0) and not walk.explicit)
    for category in a.notes:
        counts[category] += 1
    a.stale = walk.root_shrunk_at is not None
    a.verdicts = verdicts
    return a


# --------------------------------------------------------------------------
# generators. Every formula stays within the oracle's 16 variables.
# --------------------------------------------------------------------------


def signed(rng, v):
    return v if rng.random() < 0.5 else -v


def random_clause(rng, nvars, width):
    return [signed(rng, v) for v in rng.sample(range(1, nvars + 1), min(width, nvars))]


def random_formula(rng, nvars, nclauses, widths=(2, 3, 3)):
    return [random_clause(rng, nvars, rng.choice(widths)) for _ in range(nclauses)]


def chain_formula(rng):
    """Root units with reasons of two or more literals, plus noise."""
    n = rng.randint(3, 9)
    order = [signed(rng, v) for v in rng.sample(range(1, n + 1), n)]
    formula = [[order[0]]]
    for i in range(1, n):
        premises = rng.sample(order[:i], min(rng.randint(1, 2), i))
        if rng.random() < 0.85:
            clause = [-p for p in premises] + [order[i]]
            rng.shuffle(clause)
            formula.append(clause)
    formula += random_formula(rng, n, rng.randint(0, 4))
    rng.shuffle(formula)
    return formula


def php_formula(rng, pigeons, holes):
    var = lambda p, h: p * holes + h + 1
    formula = [[var(p, h) for h in range(holes)] for p in range(pigeons)]
    for h in range(holes):
        for p in range(pigeons):
            for q in range(p + 1, pigeons):
                formula.append([-var(p, h), -var(q, h)])
    rng.shuffle(formula)
    return formula


def dpll_proof(formula):
    """A RUP proof read off a DPLL tree, or None when the formula is satisfiable."""
    variables = sorted({abs(l) for c in formula for l in c})
    steps = []

    def search(decisions):
        conflict, assigned = oracle.propagate(formula, decisions)
        if not conflict:
            free = [v for v in variables if v not in assigned and -v not in assigned]
            if not free:
                return False
            if not search([*decisions, free[0]]) or not search([*decisions, -free[0]]):
                return False
        steps.append(("a", tuple(-d for d in reversed(decisions))))
        return True

    return steps if search([]) else None


def reasons_of(formula):
    return [c for c in formula if len(set(c)) >= 2 and oracle.is_pseudo_unit(formula, c)]


def true_literal(formula, clause):
    _, assigned = oracle.propagate(formula)
    return next(l for l in clause if l in assigned)


class Pool:
    """Solver proofs: real ones to run as they are and to mutate."""

    def __init__(self, workdir):
        self.dir = pathlib.Path(workdir)
        self.solvers = [s for s in ("cadical", "kissat") if shutil.which(s)]
        self.proofs = []
        self.serial = 0

    def solve(self, formula, solver):
        self.serial += 1
        cnf = self.dir / f"p{self.serial}.cnf"
        proof = self.dir / f"p{self.serial}.drat"
        cnf.write_text(cnf_text(formula))
        argv = [solver, "-q", "--no-binary", str(cnf), str(proof)]
        done = subprocess.run(argv, capture_output=True, text=True, timeout=TIMEOUT)
        steps = read_proof(proof.read_text()) if proof.exists() else []
        cnf.unlink(missing_ok=True)
        proof.unlink(missing_ok=True)
        if done.returncode not in (10, 20):
            raise RuntimeError(f"{solver} exited {done.returncode}: {done.stderr}")
        return steps


def gen_solver(rng, pool, counts):
    if not pool.solvers:
        return None
    solver = rng.choice(pool.solvers)
    shape = rng.random()
    if shape < 0.15:
        formula = php_formula(rng, *rng.choice([(3, 2), (4, 3), (5, 3)]))
    elif shape < 0.3:
        formula = chain_formula(rng)
    else:
        n = rng.randint(6, 14)
        formula = random_formula(rng, n, int(n * rng.uniform(3.5, 6)), (3,))
    steps = pool.solve(formula, solver)
    # a solver may introduce variables of its own, past what the oracle can judge
    used = {abs(l) for c in formula for l in c} | {abs(l) for _, c in steps for l in c}
    if len(used) > oracle.MAX_VARS:
        counts["solver_proofs_over_the_oracle_limit"] += 1
        return None
    counts[f"proofs_from_{solver}"] += 1
    if not oracle.satisfiable(formula):
        pool.proofs.append((formula, steps))
    return formula, steps


def mutate(rng, formula, steps):
    steps = list(steps)
    variables = sorted({abs(l) for c in formula for l in c}) or [1]
    choice = rng.randrange(9)
    i = rng.randrange(len(steps)) if steps else 0
    if steps and choice == 0:
        del steps[i]
    elif steps and choice == 1 and steps[i][1]:
        kind, lits = steps[i]
        j = rng.randrange(len(lits))
        steps[i] = (kind, lits[:j] + (-lits[j],) + lits[j + 1:])
    elif steps and choice == 2 and steps[i][1]:
        kind, lits = steps[i]
        steps[i] = (kind, lits[1:])
    elif steps and choice == 3:
        kind, lits = steps[i]
        steps[i] = (kind, (*lits, signed(rng, rng.choice(variables))))
    elif choice == 4:
        steps.insert(i, ("a", tuple(random_clause(rng, max(variables), rng.randint(1, 3)))))
    elif choice == 5:
        steps.insert(i, ("d", tuple(rng.choice(formula))))
    elif choice == 6 and reasons_of(formula):
        steps.insert(i if rng.random() < 0.5 else 0, ("d", tuple(rng.choice(reasons_of(formula)))))
    elif choice == 7 and steps:
        steps = steps[:i]                  # truncated, as a buffered proof can be
    elif steps:
        kind, lits = steps[i]
        steps[i] = (kind, tuple(rng.sample(lits, len(lits))))   # moves the pivot
    return steps


def gen_mutant(rng, pool, counts):
    if not pool.proofs:
        n = rng.randint(3, 8)
        formula = random_formula(rng, n, 5 * n)
        return formula, mutate(rng, formula, dpll_proof(formula) or [])
    formula, steps = rng.choice(pool.proofs)
    for _ in range(rng.randint(1, 2)):
        steps = mutate(rng, formula, steps)
    return formula, steps


def gen_dpll(rng, pool, counts):
    n = rng.randint(3, 9)
    formula = random_formula(rng, n, int(n * rng.uniform(3, 7)))
    steps = dpll_proof(formula) or []
    out = []
    for step in steps:                     # deletions the proof may or may not need
        if rng.random() < 0.2:
            out.append(("d", tuple(rng.choice(formula))))
        out.append(step)
    return formula, out


def gen_walk(rng, pool, counts):
    """Random steps kept mostly valid by asking the oracle, then a claim of UNSAT."""
    n = rng.randint(3, 10)
    formula = random_formula(rng, n, rng.randint(2, 3 * n))
    current = [list(c) for c in formula]
    steps = []
    for _ in range(rng.randint(2, 14)):
        roll = rng.random()
        if roll < 0.3 and current:
            clause = rng.choice(current)
            steps.append(("d", tuple(clause)))
            if len(set(clause)) > 1:       # what dratify documents; a guide, not a rule
                current, _ = oracle.remove_one(current, clause)
        elif roll < 0.36:
            steps.append(("d", tuple(random_clause(rng, n, rng.randint(1, 3)))))
        else:
            for _ in range(8):
                lemma = random_clause(rng, n, rng.randint(1, 3))
                if oracle.rup(current, lemma) or oracle.rat(current, lemma, lemma[0]):
                    break
            steps.append(("a", tuple(lemma)))
            if oracle.rup(current, lemma) or oracle.rat(current, lemma, lemma[0]):
                current.append(lemma)
    steps.append(("a", ()))
    return formula, steps


def gen_reason_aim(rng, pool, counts):
    """Delete a clause that is unit at the root, then lean on what it implied."""
    formula = chain_formula(rng)
    reasons = reasons_of(formula)
    if oracle.propagate(formula)[0] or not reasons:
        return gen_walk(rng, pool, counts)
    reason = rng.choice(reasons)
    lit = true_literal(formula, reason)
    steps = [("d", tuple(reason))]
    shape = rng.randrange(6)
    if shape == 0:
        steps += [("a", (-lit,)), ("a", ())]                 # the minimal attack
    elif shape == 1:
        steps += [("a", (lit,)), ("a", ())]                  # RUP only by a stale root
    elif shape == 2:
        other = rng.randint(1, abs(lit) + 1)
        steps += [("a", (-lit, other if other != abs(lit) else other + 1)), ("a", ())]
    elif shape == 3:
        for second in rng.sample(reasons, min(2, len(reasons))):
            if second != reason:
                steps.append(("d", tuple(second)))
                steps.append(("a", (-true_literal(formula, second),)))
        steps += [("a", (-lit,)), ("a", ())]
    elif shape == 4:
        steps += list(dpll_proof(formula) or []) + [("a", ())]
    else:
        steps += mutate(rng, formula, dpll_proof(formula) or [("a", ())])
    return formula, steps


def gen_unit_aim(rng, pool, counts):
    """Delete unit clauses, which is where the two flavours of DRAT part."""
    n = rng.randint(2, 8)
    units = rng.sample(range(1, n + 1), rng.randint(1, min(2, n)))
    formula = [[signed(rng, u)] for u in units] + random_formula(rng, n, rng.randint(1, 4 * n))
    rng.shuffle(formula)
    unit = rng.choice([c for c in formula if len(c) == 1])
    lit = unit[0]
    written = (lit,) if rng.random() < 0.8 else (lit, lit)   # `d 1 1 0` is a unit too
    steps = [("d", written)]
    shape = rng.randrange(6)
    if shape == 5:
        # Refuted only with the unit: ignoring its deletion verifies, honouring it
        # does not, so this is the flavours parting on an unsatisfiable formula.
        u, x, y = rng.sample(range(1, 17), 3)
        formula = [[u]] + [[-u, a * x, b * y] for a in (1, -1) for b in (1, -1)]
        rng.shuffle(formula)
        return formula, [("d", (u,)), ("a", (x,)), ("a", ())]
    if shape == 0:
        steps += [("a", (-lit,)), ("a", ())]
    elif shape == 1:
        steps += list(dpll_proof(formula) or [("a", ())])
    elif shape == 2:
        rest = [c for c in formula if c != unit]
        steps += list(dpll_proof(rest) or [("a", ())])
    elif shape == 3:
        # every clause holding the other polarity goes, so (-lit) is vacuously RAT
        # when the deletion of the unit is honoured, and not when it is ignored
        for c in formula:
            if lit in c and c != unit:
                steps.append(("d", tuple(c)))
        steps += [("a", (-lit,))] + list(
            dpll_proof([c for c in formula if lit not in c] + [[-lit]]) or [("a", ())])
    else:
        steps += [("d", written), ("a", (lit,)), ("a", ())]
    return formula, steps


def gen_rat_aim(rng, pool, counts):
    """Lemmas that only RAT can justify: definitions and blocked clauses."""
    n = rng.randint(3, 9)
    formula = random_formula(rng, n, int(n * rng.uniform(1.5, 6)))
    steps = []
    fresh = n + 1
    a, b = rng.sample(range(1, n + 1), 2)
    a, b = signed(rng, a), signed(rng, b)
    if rng.random() < 0.7:                 # fresh <-> a AND b
        steps += [("a", (fresh, -a, -b)), ("a", (-fresh, a)), ("a", (-fresh, b))]
    else:                                  # the same, with the pivot written second
        steps += [("a", (-a, fresh, -b)), ("a", (a, -fresh)), ("a", (-fresh, b))]
    for _ in range(rng.randint(0, 4)):     # blocked clauses, found by asking
        lemma = random_clause(rng, n, rng.randint(1, 3))
        if oracle.rat(formula, lemma, lemma[0]) and rng.random() < 0.8:
            steps.append(("a", tuple(lemma)))
    lit = signed(rng, rng.randint(1, n))
    if rng.random() < 0.5:                 # RAT only once its candidates are gone
        for c in formula:
            if -lit in c:
                steps.append(("d", tuple(c)))
        steps.append(("a", (lit,)))
    tail = dpll_proof(formula)
    steps += list(tail) if tail else [("a", ())]
    return formula, steps


def gen_syntax(rng, pool, counts):
    """Spellings that must not change a verdict: repeats, tautologies, multisets."""
    n = rng.randint(2, 6)
    formula = random_formula(rng, n, rng.randint(2, 5 * n))
    if rng.random() < 0.3:
        formula.append(list(rng.choice(formula)))   # a real duplicate
    tail = list(dpll_proof(formula) or [("a", ())])
    shape = rng.randrange(6)
    if shape == 0:
        c = rng.choice(formula)
        steps = [("d", tuple(c)), ("d", tuple(c))] + tail
    elif shape == 1:
        v = rng.randint(1, n)
        taut = (v, -v, signed(rng, rng.randint(1, n)))
        steps = [("a", taut), ("d", taut)] + tail
    elif shape == 2:
        steps = [("a", (*s[1], *s[1])) if s[1] else s for s in tail]
    elif shape == 3:
        steps = tail + [("a", tuple(random_clause(rng, n, 2))), ("d", tuple(rng.choice(formula)))]
    elif shape == 4:
        steps = [("d", tuple(random_clause(rng, n, 2)))] + tail  # often not present
    else:
        steps = [s for s in tail if s[1]]       # the final empty clause is left out
        if rng.random() < 0.3:
            steps = []
            formula = formula + [[]]            # the empty clause in the input
    return formula, steps


FAMILIES = {
    "solver": gen_solver, "mutant": gen_mutant, "dpll": gen_dpll, "walk": gen_walk,
    "reason_aim": gen_reason_aim, "unit_aim": gen_unit_aim, "rat_aim": gen_rat_aim,
    "syntax": gen_syntax,
}


def instances(seed, total, pool, counts):
    rng = random.Random(seed)
    names = list(FAMILIES)
    for i in range(total):
        family = names[i % len(names)]
        generated = FAMILIES[family](rng, pool, counts)
        if generated is None:
            continue
        counts[f"family_{family}"] += 1
        yield family, generated[0], list(generated[1])


# --------------------------------------------------------------------------
# shrinking a mismatch for the report
# --------------------------------------------------------------------------


def shrink(formula, steps, kind, checker, external):
    """Remove clauses and steps while the same kind of mismatch stays."""

    def still(f, s):
        try:
            return kind in analyse(f, s, checker, external, collections.Counter()).kinds
        except (ValueError, RuntimeError):
            return False

    changed = True
    while changed:
        changed = False
        for i in range(len(steps) - 1, -1, -1):
            candidate = steps[:i] + steps[i + 1:]
            if still(formula, candidate):
                steps, changed = candidate, True
        for i in range(len(formula) - 1, -1, -1):
            candidate = formula[:i] + formula[i + 1:]
            if still(candidate, steps):
                formula, changed = candidate, True
    return formula, steps


# --------------------------------------------------------------------------
# the run
# --------------------------------------------------------------------------


def campaign(seed, total, checker, external, workdir, keep_examples=True):
    counts = collections.Counter()
    pool = Pool(workdir)
    mismatches = collections.Counter()
    examples = {}
    for family, formula, steps in instances(seed, total, pool, counts):
        a = analyse(formula, steps, checker, external, counts)
        if family == "solver":
            # How much real solvers lean on the reading of a deletion.
            counts["solver_proofs_shrinking_the_root"] += a.stale
            counts["solver_proofs_with_a_deletion"] += any(k == "d" for k, _ in steps)
            counts["solver_unsat_proofs_rate_fwd_spec_rejects"] += (
                a.verdicts.get("rate/fwd-spec") is False and not oracle.satisfiable(formula))
            counts["solver_unsat_proofs_rate_fwd_skip_rejects"] += (
                a.verdicts.get("rate/fwd-skip") is False and not oracle.satisfiable(formula))
        for severity, kind, detail in a.mismatches:
            label = STALE_ROOT_FINDING if a.stale and kind in (
                CRITICAL_KINDS | {"accepted_unacceptable", "field_mismatch"}) else None
            mismatches[(severity, kind, label)] += 1
            counts[f"mismatch_{kind}"] += 1
            examples.setdefault((severity, kind, label), (family, formula, steps, detail))
    return counts, mismatches, examples, pool


def required_categories(external, pool):
    needed = ["instances", "steps_judged", "formulas_satisfiable", "formulas_unsatisfiable",
              "dratify_ok", "dratify_rejected_a_step", "additions_rup", "additions_rat_only",
              "additions_unacceptable", "deletions_applied", "deletions_ignored_as_unit",
              "deletions_absent", "deletions_shrinking_the_root",
              "proofs_with_implicit_empty_clause"]
    needed += [f"family_{name}" for name in FAMILIES if name != "solver" or pool.solvers]
    needed += [f"proofs_from_{s}" for s in pool.solvers]
    if external.rate:
        for mode in RATE_MODES:
            tag = "rate_" + mode.replace("-", "_")
            needed += [f"{tag}_run", f"{tag}_agree", f"{tag}_disagree"]
        needed += ["rate_fwd_spec_note_deletion_flavour", "rate_fwd_spec_dratify_accepts_it_rejects",
                   "rate_bwd_skip_it_accepts_dratify_rejects", "note_backward_skips_unused",
                   "note_implicit_empty_clause"]
    if external.drat_trim:
        needed += ["drat_trim_run", "drat_trim_agree"]
    return needed


def tool_version(path):
    try:
        done = subprocess.run([path, "--version"], capture_output=True, text=True, timeout=5)
    except (OSError, subprocess.TimeoutExpired):
        return "unknown"
    return (done.stdout.strip().splitlines() or ["unknown"])[0]


def native_engine():
    try:
        import cdclkit_native
    except ImportError:
        return False
    register_native(cdclkit_native)
    return True


def print_mismatches(mismatches, examples, checker, external):
    for (severity, kind, label), n in sorted(mismatches.items(), key=str):
        family, formula, steps, detail = examples[(severity, kind, label)]
        tiny_f, tiny_s = shrink(formula, steps, kind, checker, external)
        print(f"  {severity:8} {kind:26} x{n:<6} {label or 'UNLABELLED: not a known finding'}")
        print(f"           family {family}; {detail}")
        print(f"           shrunk: F={tiny_f} proof={tiny_s}")


#: disagreements that are explained, each with a finding file, and the counter
#: that shows the run reached it
NOTE_FINDINGS = [
    ("drat_trim-2", "note_deletion_flavour",
     "rate, with unit deletions honoured, rejects proofs dratify accepts because "
     "dratify documents ignoring them; rate -d agrees with dratify"),
    ("drat_trim-3", "note_implicit_empty_clause",
     "rate verifies a proof that reaches a propagation conflict without writing the "
     "empty clause; dratify documents rejecting it"),
    ("drat_trim-4", "note_backward_skips_unused",
     "rate's backward modes verify proofs with an invalid unused lemma; dratify and "
     "rate -f reject them, as the README documents"),
    ("drat_trim-5", "note_sticky_refutation",
     "once propagation has refuted the clauses, dratify keeps treating them as refuted "
     "after a deletion undoes the conflict; sound, and rate agrees"),
]

NOT_CHECKED = [
    "drat-trim itself: not installed, no package install provides it, and its source "
    "is on GitHub, outside this campaign's network rule. Its invocation and stdout "
    "parsing were exercised only against shell stubs in --self-test.",
    "rate with no -p flag, where it tries every literal as a pivot",
    "rate's LRAT and GRAT output, and DPR proofs",
    "binary DRAT: dratify documents text proofs only",
    "minisat: it writes no DRAT proof, so it contributed no proofs",
    "formulas past 16 variables, so no proof of realistic size; the README's uuf and "
    "php benchmarks are bench/repro.py's job",
    "tautological clauses in the input formula, and DIMACS parsing corners",
    "the list-of-steps and MemoryProof paths into check_proof: only proof text is passed",
]


def main_run(args):
    if not native_engine():
        print("FAILED: cdclkit_native is not importable, so the native engine did not run.")
        return 2
    rate = args.rate or shutil.which("rate")
    drat_trim = args.drat_trim or shutil.which("drat-trim")
    print(f"rate:      {rate or 'NOT RUN: not on PATH and no --rate given'}")
    print(f"drat-trim: {drat_trim or 'NOT RUN: not on PATH and no --drat-trim given'}")
    started = time.perf_counter()
    with tempfile.TemporaryDirectory() as workdir:
        external = External(rate, drat_trim, workdir)
        counts, mismatches, examples, pool = campaign(
            args.seed, args.instances, Dratify, external, workdir)
        runtime = time.perf_counter() - started
        print(f"seed {args.seed}, {counts['instances']} instances, "
              f"{counts['steps_judged']} steps judged by the oracle, {runtime:.1f}s")
        for key in sorted(counts):
            print(f"  {key:52} {counts[key]}")
        missing = [c for c in required_categories(external, pool) if not counts[c]]
        print("mismatches:" if mismatches else "mismatches: none")
        print_mismatches(mismatches, examples, Dratify, external)

    findings = sorted({label for (_, _, label) in mismatches if label})
    report = {
        "corner": CORNER,
        "seeds": [args.seed],
        "instances": counts["instances"],
        "steps": counts["steps_judged"],
        "per_category_counts": dict(sorted(counts.items())),
        "runtime_seconds": round(runtime, 1),
        "external_checkers": {
            "rate": tool_version(rate) if rate else "not run",
            "rate_modes": {m: " ".join(f) for m, (f, _, _) in RATE_MODES.items()} if rate else {},
            "drat-trim": tool_version(drat_trim) if drat_trim else
            "NOT RUN: not installed and not available as a package",
        },
        "findings": ([
            {"id": STALE_ROOT_FINDING, "severity": "Critical",
             "summary": "dratify keeps a literal in the root assignment after deleting "
                        "the only clause implying it, on both engines, so it returns "
                        "ok=True on satisfiable formulas"}
        ] if STALE_ROOT_FINDING in findings else []) + [
            {"id": ident, "severity": "Note", "summary": summary}
            for ident, category, summary in NOTE_FINDINGS if counts[category]],
        "mismatch_kinds": [
            {"severity": s, "kind": k, "finding": l, "count": n}
            for (s, k, l), n in sorted(mismatches.items(), key=str)],
        "not_checked": NOT_CHECKED,
    }
    if args.results:
        path = pathlib.Path(args.results)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(report, indent=2) + "\n")
        print(f"wrote {path}")

    status = 0
    if not rate and not drat_trim:
        print("FAILED: no external checker ran, so this corner was not reached.")
        status = 2
    if missing:
        print(f"FAILED: categories this generator claims stayed at zero: {missing}")
        status = 2
    if mismatches:
        print(f"FAILED: {sum(mismatches.values())} mismatches, listed above.")
        status = status or 1
    return status


# --------------------------------------------------------------------------
# self-test
# --------------------------------------------------------------------------


def write_stub(directory, name, body):
    path = pathlib.Path(directory) / name
    path.write_text("#!/bin/sh\n" + body + "\n")
    path.chmod(0o755)
    return str(path)


def self_test(args):
    """Wrong checkers must be flagged, and a right one must not be."""
    if not native_engine():
        print("self-test FAILED: cdclkit_native is not importable")
        return 2
    rate = args.rate or shutil.which("rate")
    failures = []

    def expect(name, ok, shown=""):
        print(f"  {'ok ' if ok else 'FAIL'} {name}{': ' + shown if shown else ''}")
        if not ok:
            failures.append(name)

    with tempfile.TemporaryDirectory() as workdir:
        says_yes = write_stub(workdir, "says_yes", 'echo "s VERIFIED"; exit 0')
        says_no = write_stub(workdir, "says_no", 'echo "s NOT VERIFIED"; exit 1')
        says_nothing = write_stub(workdir, "says_nothing", 'echo "c out of time"; exit 0')
        external_rate = rate or says_yes
        if not rate:
            print("  rate is not available: the dratify stubs run beside a stub, which "
                  "proves less")
        n = args.instances if args.instances < 400 else 160

        def run(checker, ext=None):
            ext = ext or External(external_rate, None, workdir)
            counts, mismatches, _, _ = campaign(args.seed, n, checker, ext, workdir)
            return counts, {kind for (_, kind, _) in mismatches}, mismatches

        print("wrong dratify, right tools:")
        _, kinds, _ = run(AcceptAll)
        expect("accept-everything is flagged as ok on a satisfiable formula",
               "ok_on_satisfiable" in kinds, str(sorted(kinds)))
        _, kinds, _ = run(RejectAll)
        expect("reject-everything is flagged as a false rejection",
               "false_rejection" in kinds, str(sorted(kinds)))
        _, kinds, _ = run(EngineSkew)
        expect("engines that differ on one field are flagged",
               "engine_disagreement" in kinds)

        print("the documented semantics, computed by the oracle:")
        counts, kinds, mismatches = run(Reference)
        if rate:
            expect("nothing is flagged, so every rate disagreement is explained by a "
                   "flavour or by backward checking", not kinds, str(dict(mismatches)))
        else:
            expect("nothing is flagged but the tool stub's disagreements",
                   kinds <= {"external_unexplained"}, str(sorted(kinds)))

        print("wrong external checkers, right dratify semantics:")
        for name, stub in (("says VERIFIED to everything", says_yes),
                           ("says NOT VERIFIED to everything", says_no)):
            _, kinds, _ = run(Reference, External(stub, None, workdir))
            expect(f"a rate that {name} is flagged", "external_unexplained" in kinds,
                   str(sorted(kinds)))
        _, kinds, _ = run(Reference, External(says_nothing, None, workdir))
        expect("a rate that gives no verdict is flagged", "external_no_verdict" in kinds)

        print("drat-trim's calling convention, against shell stubs only "
              "(the real drat-trim did not run):")
        record = pathlib.Path(workdir) / "argv"
        recorder = write_stub(workdir, "records",
                              f'echo "$@" > "{record}"\necho "c something"\n'
                              'echo "s VERIFIED"\nexit 40')
        ext = External(None, recorder, workdir)
        verdicts = ext.verdicts([[1], [-1]], [("a", ())])
        argv = record.read_text().split()
        expect("the formula, the proof and a -t limit are passed",
               argv[0].endswith(".cnf") and argv[1].endswith(".drat")
               and argv[2] == "-t" and argv[3].isdigit(), " ".join(argv[2:]))
        expect("an odd exit code does not hide s VERIFIED", verdicts["drat-trim"] is True)
        no_code = write_stub(workdir, "rejects_exit_0", 'echo "s NOT VERIFIED"; exit 0')
        expect("exit 0 does not hide s NOT VERIFIED", External(None, no_code, workdir)
               .verdicts([[1]], [])["drat-trim"] is False)
        expect("no verdict is None, not a rejection",
               External(None, says_nothing, workdir).verdicts([[1]], [])["drat-trim"] is None)
        counts = collections.Counter()
        analyse([[1], [-1]], [("a", ())], Dratify, External(None, says_nothing, workdir), counts)
        expect("drat-trim's lack of a verdict is counted, not a pass",
               counts["drat_trim_no_verdict"] == 1)
        counts = collections.Counter()
        a = analyse([[1, 2], [-1, 2]], [("a", (2,)), ("a", ())], Dratify,
                    External(None, says_yes, workdir), counts)
        expect("a drat-trim that accepts a false refutation of a satisfiable formula is "
               "not explained away", "external_accepted_satisfiable" in a.kinds, str(a.kinds))

        print("zero-count guard:")
        ext = External(None, None, workdir)
        counts = collections.Counter(instances=1)
        missing = [c for c in required_categories(ext, Pool(workdir)) if not counts[c]]
        expect("a run that reached nothing would fail", len(missing) > 5, f"{len(missing)} missing")

    if failures:
        print(f"self-test FAILED: {failures}")
        return 1
    print("self-test passed")
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--seed", type=int, default=1)
    parser.add_argument("--instances", type=int, default=1600)
    parser.add_argument("--rate", help="path to `rate`; otherwise looked up on PATH")
    parser.add_argument("--drat-trim", dest="drat_trim",
                        help="path to drat-trim; otherwise looked up on PATH")
    parser.add_argument("--results", default=f"campaign/results/{CORNER}.json",
                        help="where to write the results; empty to write nothing")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        return self_test(args)
    return main_run(args)


if __name__ == "__main__":
    sys.exit(main())
