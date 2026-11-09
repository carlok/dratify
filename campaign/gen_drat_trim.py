# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Run dratify beside an external DRAT checker and classify every disagreement.

Two external checkers are supported, and they are never confused in the output:

* ``drat-trim``, when one is on PATH or given by ``--drat-trim PATH``. Its verdict
  is read from its stdout (``s VERIFIED``, ``s NOT VERIFIED``, ``s DERIVATION``,
  ``s TIMEOUT``), never from its exit code: a trivially refuted formula can exit 1
  and print ``s VERIFIED``, and ``s TIMEOUT`` exits 0. It opens ``argv[1]`` and
  ``argv[2]`` by position, so every flag goes after the two files.
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

drat-trim runs in these modes, every one with ``-t``:

    ========== ========== ===================================================
    mode       flags      what it is for
    ========== ========== ===================================================
    default    -I         backward, judged against dratify
    forward    -f -I      forward, every lemma up to the first conflict, judged
    verbose    -I -v      default again, to list the deletions it ignores
    autodetect (none)     default without -I: a control on its text detection
    sat        -S -I      answers another question, so it is counted, not judged
    ========== ========== ===================================================

There is no mode at this commit that honours a unit deletion and still checks a
refutation. ``-S`` honours them, but it checks deletions and not additions, and
stops at a written empty clause: ``campaign/findings/drat_trim-9.md``.

A disagreement with drat-trim is a Note only if a changed proof shows the cause:
``explain_trim`` turns the proof into one both checkers accept, one named change at
a time, and asks both checkers again. Otherwise it fails the run. ``deletion_rule``
tests directly whether dratify's root-unit test and drat-trim's reason test can
give different verdicts.

dratify's documented reading is the oracle's ``operational`` flavour: deletions
are applied, except that a deletion of a clause unit under the root assignment is
ignored, and all of them once the root has conflicted. So rate's ``fwd-skip`` should
agree with it nearly always. ``DOCUMENTED_FLAVOUR`` names it, and every dratify verdict is judged
against it and against ``satisfiable`` before any external checker is consulted.

What a disagreement can be:

* a **Note**, when the two flavours of DRAT or backward checking explain it;
* a **Critical** or **Bug**, when dratify is wrong by the oracle;
* **unexplained**, which fails the run until someone has looked at it.

Run from the repository root:

    python -m campaign.gen_drat_trim --rate PATH --drat-trim PATH
    python -m campaign.gen_drat_trim --self-test --rate PATH --drat-trim PATH
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
from typing import NamedTuple
from unittest import mock

from campaign import oracle
from dratify import DRATChecker, check_proof, parse_dimacs, parse_proof, register_native

CORNER = "drat_trim"
DOCUMENTED_FLAVOUR = "operational"
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
# mode -> flags. drat-trim opens argv[1] and argv[2] by position, so these follow them.
DRAT_TRIM_MODES = {
    "default": ["-I"],
    "forward": ["-f", "-I"],
    "verbose": ["-I", "-v"],
    "autodetect": [],
    "sat": ["-S", "-I"],
}
TIMEOUT = 20
CRASH_RETRIES = 5     # its crash depends on what the heap holds, so a run can be repeated
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


class LengthOnlyDeletion(Dratify):
    """drat_trim-1, now fixed: only clauses of at most one literal are spared."""

    name = "stub: spares clauses by length alone"

    @staticmethod
    def run(formula, steps, engine):
        with mock.patch.object(DRATChecker, "_unit_at_root", lambda self, lits: False):
            return Dratify.run(formula, steps, "python")


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


class Trim(NamedTuple):
    """One run of drat-trim. ``outcome`` is the verdict its stdout printed, or
    ``timeout``, ``crash`` (killed by a signal) or ``none`` (it exited without one).
    ``crashes`` counts the runs it took to get there: see drat_trim-10."""

    outcome: str
    stdout: str
    crashes: int = 0


TRIM_VERDICTS = {"s VERIFIED": "verified", "s NOT VERIFIED": "not_verified",
                 "s DERIVATION": "derivation", "s TIMEOUT": "timeout"}


def trim_outcome(stdout, returncode):
    # Universal newlines have already turned its \r prefixes into line breaks.
    for line in stdout.splitlines():
        outcome = TRIM_VERDICTS.get(line.strip())
        if outcome:
            return outcome
    return "crash" if returncode < 0 else "none"


class External:
    """Runs whichever checkers exist, on one formula and proof at a time."""

    def __init__(self, rate, drat_trim, workdir):
        self.rate = rate
        self.drat_trim = drat_trim
        self.cnf = pathlib.Path(workdir) / "instance.cnf"
        self.proof = pathlib.Path(workdir) / "instance.drat"
        self.trim_cnf = pathlib.Path(workdir) / "trim.cnf"
        self.trim_proof = pathlib.Path(workdir) / "trim.drat"

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
        return out

    def trim(self, mode, formula, steps):
        """One drat-trim mode on this formula and proof, which may be a changed one."""
        self.trim_cnf.write_text(cnf_text(formula))
        self.trim_proof.write_text(proof_text(steps))
        argv = [self.drat_trim, str(self.trim_cnf), str(self.trim_proof),
                *DRAT_TRIM_MODES[mode], "-t", str(TIMEOUT)]
        for crashes in range(CRASH_RETRIES):
            try:
                done = subprocess.run(argv, capture_output=True, text=True, errors="replace",
                                      timeout=TIMEOUT + 5)   # -f and -S never look at -t
            except subprocess.TimeoutExpired:
                return Trim("timeout", "", crashes)
            outcome = trim_outcome(done.stdout, done.returncode)
            if outcome != "crash":
                break
        else:
            crashes = CRASH_RETRIES
        return Trim(outcome, done.stdout, crashes)

    def trims(self, formula, steps):
        if not self.drat_trim:
            return {}
        return {mode: self.trim(mode, formula, steps) for mode in DRAT_TRIM_MODES}


def checker_reading(name):
    """(direction, oracle flavour) for one of rate's modes."""
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
    tag = "rate_" + name.split("/")[1].replace("-", "_")
    if theirs is None:
        counts[f"{tag}_no_verdict"] += 1
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


def trim_agrees(outcome, ours):
    """Does this drat-trim verdict say what dratify's result says?

    ``s DERIVATION`` is forward mode's "every lemma is fine, and this is not a
    refutation", which is what dratify means by ok=False with no failed step.
    """
    if outcome == "verified":
        return ours["ok"]
    if outcome == "derivation":
        return not ours["ok"] and ours["failed_step"] <= 0
    return not ours["ok"]


def repair(formula, steps, checker, backward, want_empty, skip_first=False):
    """Change a proof dratify rejects until it accepts it, naming each change.

    Returns ``(steps, causes)``, or None when no change here will do. Every change
    is one drat-trim's own behaviour stands for, read from drat-trim.c:

    * ``other_pivot``: redundancyCheck falls back to every literal of the lemma,
      where dratify has only the first. The lemma is rewritten with that one first.
    * ``unused_lemma``: backward checking never looks at a lemma the refutation
      does not reach. Backward only. The lemma is removed.
    * ``core_only_rat``: checkRAT skips a candidate not yet marked as used, in
      backward mode only. The candidates that fail are deleted just before the lemma.
    * ``implicit_empty``: it stops at the first propagation conflict; dratify asks
      for the written clause. The clause is appended.

    ``skip_first`` is for a proof forward mode refused: its fallback pivots did not
    save the lemma, so if backward mode let it through, that is because it never
    looked.
    """
    r = checker.run(formula, steps, "python")
    if r["failed_step"] <= 0:
        if r["ok"] or not want_empty:
            return steps, set()
        closed = [*steps, ("a", ())]
        return (closed, {"implicit_empty"}) if checker.run(formula, closed, "python")["ok"] \
            else None
    k = r["failed_step"] - 1
    lemma = steps[k][1]
    before, after = steps[:k], steps[k + 1:]
    current = oracle.replay(formula, before, DOCUMENTED_FLAVOUR,
                            stop_at_unacceptable=False)[1]

    def attempt(changed, cause):
        out = repair(formula, changed, checker, backward, want_empty, skip_first)
        return (out[0], out[1] | {cause}) if out else None

    if backward and skip_first:
        out = attempt([*before, *after], "unused_lemma")
        if out:
            return out
    for lit in dict.fromkeys(lemma[1:]):
        if lit != lemma[0] and oracle.rat(current, lemma, lit):
            moved = (lit, *[l for l in lemma if l != lit])
            out = attempt([*before, ("a", moved), *after], "other_pivot")
            if out:
                return out
    if not backward:
        return None
    if not skip_first:
        out = attempt([*before, *after], "unused_lemma")
        if out:
            return out
    for pivot in dict.fromkeys(lemma):
        failing = [("d", tuple(c)) for c in current if -pivot in c
                   and not oracle.rup(current, set(lemma) | (set(c) - {-pivot}))]
        moved = (pivot, *[l for l in lemma if l != pivot])
        out = attempt([*before, *failing, ("a", moved), *after], "core_only_rat")
        if out:
            return out
    return None


NOTE_OF_CAUSE = {
    "other_pivot": "note_other_pivot",
    "unused_lemma": "note_backward_skips_unused",
    "core_only_rat": "note_core_only_rat",
    "implicit_empty": "note_implicit_empty_clause",
}


def explain_trim(mode, outcome, formula, steps, ours, checker, external, trims):
    """The notes that account for one disagreement, each shown by a changed proof."""
    notes = []
    # `d 0`: its fscanf(" d  %i ") reads the 0 as the first literal, takes that for
    # "no literal yet", reads again, and so swallows the next token of the proof.
    if any(kind == "d" and not lits for kind, lits in steps):
        clean = [s for s in steps if s != ("d", ())]
        again = external.trim(mode, formula, clean).outcome
        ours_clean = checker.run(formula, clean, "python")
        if again != outcome and ours_clean["ok"] == ours["ok"]:
            notes.append("note_deletion_of_nothing")
            if trim_agrees(again, ours_clean):
                return notes
        steps, outcome, ours = clean, again, ours_clean
    if outcome not in ("verified", "derivation") or ours["ok"]:
        return None                 # nothing below makes drat-trim stricter than dratify
    out = repair(formula, steps, checker, mode == "default", outcome == "verified",
                 trims["forward"].outcome == "not_verified")
    if out is None or external.trim(mode, formula, out[0]).outcome != outcome:
        return None
    causes = out[1]
    if "unused_lemma" in causes and trims["forward"].outcome != "not_verified":
        return None                 # forward mode must look at the lemma and refuse it
    return notes + [NOTE_OF_CAUSE[c] for c in sorted(causes)]


def settle_crash(mode, run, formula, steps, external, a, counts):
    """drat_trim-10: at a final empty clause with no conflict behind it, drat-trim reads
    one int past its clause database, and can crash on what it finds there.

    Without that clause it must not crash, and with a second one after it the read
    stays inside the database, so it must answer NOT VERIFIED. Anything else fails
    the run. Returns the run with the answer in it.
    """
    tag = f"drat_trim_{mode}"
    counts[f"{tag}_crashed_at_least_once"] += 1
    counts[f"{tag}_crashed_every_time"] += run.outcome == "crash"
    if ("a", ()) in steps and run.outcome in ("crash", "not_verified"):
        without = [s for s in steps if s != ("a", ())]
        padded = external.trim(mode, formula, [*steps, ("a", ())])
        if padded.outcome == "not_verified" and not padded.crashes and not any(
                external.trim(mode, formula, without).crashes for _ in range(10)):
            counts[f"{tag}_note_crash_on_unsupported_empty_clause"] += 1
            a.notes.append("note_crash_on_unsupported_empty_clause")
            return Trim(padded.outcome, padded.stdout, run.crashes)
    a.flag("Bug", "drat_trim_crash_unexplained", f"{mode}: {run.crashes} crashes")
    return run


def judge_drat_trim(mode, run, ours, formula, steps, sat, checker, external, trims, a, counts):
    tag = f"drat_trim_{mode}"
    counts[f"{tag}_outcome_{run.outcome}"] += 1
    if mode == "sat":
        # It checks deletions and skips additions: another question, so never compared.
        counts[f"{tag}_run"] += 1
        counts[f"{tag}_crashed_at_least_once"] += run.crashes > 0
        if run.outcome == "verified":
            shape = "satisfiable" if sat else "unsatisfiable" if not oracle.propagate(formula)[0] \
                else "unsatisfiable_by_propagation"
            counts[f"{tag}_verified_on_{shape}"] += 1
        return
    if mode == "default":
        counts["drat_trim_default_warned_of_a_unit_deletion"] += (
            "backward mode ignores deletion" in run.stdout)
        counts["drat_trim_default_warned_of_another_pivot"] += (
            "RAT check on proof pivot failed" in run.stdout)
    if mode in ("autodetect", "verbose"):
        counts[f"{tag}_run"] += 1
        if run.outcome != trims["default"].outcome:
            a.flag("Bug", f"drat_trim_{mode}_changes_the_verdict",
                   f"{run.outcome}, and {trims['default'].outcome} in the default mode")
        return
    if run.outcome == "timeout":
        return                      # counted above, and reported
    if run.outcome in ("crash", "none"):
        a.flag("Bug", "drat_trim_no_verdict", f"{mode}: {run.outcome}")
        return
    counts[f"{tag}_run"] += 1
    if run.outcome == "verified" and sat:
        # No flavour and no backward pass can explain this.
        a.flag("Bug", "external_accepted_satisfiable", f"drat-trim {mode} said VERIFIED")
    if trim_agrees(run.outcome, ours):
        counts[f"{tag}_agree"] += 1
        return
    counts[f"{tag}_disagree"] += 1
    counts[f"{tag}_{'dratify_accepts_it_rejects' if ours['ok'] else 'it_accepts_dratify_rejects'}"] += 1
    if a.mismatches:
        notes = ["follows_dratify_mismatch"]     # already a failure
    else:
        notes = explain_trim(mode, run.outcome, formula, steps, ours, checker, external, trims)
    if not notes:
        a.flag("Bug", "drat_trim_unexplained",
               f"{mode} says {run.outcome}, dratify ok={ours['ok']} "
               f"failed_step={ours['failed_step']}")
        return
    for note in notes:
        counts[f"{tag}_{note}"] += 1
        a.notes.append(note)


def trim_lines(stdout, start):
    """The clauses on the lines of drat-trim -v that begin this way."""
    found = collections.Counter()
    for line in stdout.splitlines():
        if line.strip().startswith(start):
            printed = line.split("]", 1)[1].split()
            found[frozenset(int(t) for t in printed[:-1])] += 1
    return found


def reasons_kept_by_trim(stdout):
    """The clauses drat-trim -v says it kept because they were reasons."""
    return trim_lines(stdout, "c ignoring deletion instruction")


def deletions_it_found_nothing_for(stdout):
    """Its parser matches a deletion to a copy before it knows the copy is a reason, so
    a second deletion of a reason it kept finds nothing. No clause goes, as in dratify."""
    return trim_lines(stdout, "c WARNING: deleted clause on proof line")


def with_lookalikes_applied(formula, steps, applied):
    """dratify's Python engine with the deletions numbered in ``applied`` honoured.

    The numbers count the deletions of two or more literals that reach the root-unit
    test. This is dratify holding drat-trim's reason test where the two differ.
    """
    real = DRATChecker._unit_at_root
    seen = [0]

    def test(self, lits):
        seen[0] += 1
        return real(self, lits) and seen[0] not in applied

    with mock.patch.object(DRATChecker, "_unit_at_root", test):
        return Dratify.run(formula, steps, "python")


def deletion_rule(formula, steps, walk, ours, checker, external, trims, a, counts):
    """Where dratify's root-unit test and drat-trim's reason test part, does it matter?

    The deletions compared are those before the first conflict, where both stop
    asking, and before any step dratify rejects, which is exactly where a proof
    relying on a clause being gone would show. drat-trim does not stop there, so it is
    asked again on that prefix. On each proof that differs, the deletions the two read
    differently are put right on either side in turn: drat-trim with them removed from
    the proof, and dratify with them honoured. A verdict that moves is the deletion
    rule itself showing, and fails the run.
    """
    if not external.drat_trim or walk.input_refuted:
        return
    trace = trims["verbose"].stdout if walk.first_bad is None else external.trim(
        "verbose", formula, steps[:walk.first_bad - 1]).stdout
    theirs = reasons_kept_by_trim(trace)
    nothing = deletions_it_found_nothing_for(trace)
    in_time = [s for s in walk.judged if s.kind == "d" and len(set(s.clause)) >= 2
               and (walk.refuted_at is None or s.index < walk.refuted_at)]
    mine = collections.Counter(
        frozenset(s.clause) for s in in_time if s.present and not s.applied)
    counts["deletion_rule_proofs_compared"] += 1
    counts["deletion_rule_kept_by_both"] += sum((mine & theirs).values())
    only_trim = theirs - mine
    if only_trim:
        counts["deletion_rule_kept_only_by_drat_trim"] += sum(only_trim.values())
        a.flag("Bug", "deletion_kept_only_by_drat_trim", str(list(only_trim)))
    counts["deletion_rule_repeated_on_a_kept_clause"] += sum(((mine - theirs) & nothing).values())
    only_mine = mine - theirs - nothing
    if not only_mine:
        return
    counts["deletion_rule_kept_only_by_dratify"] += sum(only_mine.values())
    counts["deletion_rule_proofs_that_differ"] += 1
    counts["deletion_rule_differing_proofs_verdicts_agree"] += trim_agrees(
        trims["default"].outcome, ours)
    counts["deletion_rule_differing_proofs_dratify_accepts"] += ours["ok"]

    # the last copies stand for the ones it applied: which copy it took does not matter
    remaining = collections.Counter(only_mine)
    dropped = set()
    for s in reversed(in_time):
        if s.present and not s.applied and remaining[frozenset(s.clause)] > 0:
            remaining[frozenset(s.clause)] -= 1
            dropped.add(s.index)
    without = [s for i, s in enumerate(steps, 1) if i not in dropped]
    for mode in ("default", "forward"):
        if external.trim(mode, formula, without).outcome != trims[mode].outcome:
            a.flag("Bug", "deletion_rule_moved_the_verdict",
                   f"drat-trim {mode}, without the deletions of {sorted(only_mine, key=sorted)}")
        else:
            counts[f"deletion_rule_{mode}_verdict_stays_without_them"] += 1
    if checker is Dratify:
        # the root-unit test is asked once per deletion of two or more literals
        ordinal = {s.index: n for n, s in enumerate(in_time, 1)}
        honoured = with_lookalikes_applied(formula, steps, {ordinal[i] for i in dropped})
        if honoured["ok"] != ours["ok"] or honoured["failed_step"] != ours["failed_step"]:
            a.flag("Bug", "deletion_rule_moved_the_verdict",
                   f"dratify honouring {sorted(only_mine, key=sorted)}: "
                   f"ok={honoured['ok']} failed_step={honoured['failed_step']}")
        else:
            counts["deletion_rule_dratify_verdict_stays_honouring_them"] += 1


def analyse(formula, steps, checker, external, counts):
    a = Analysis()
    sat = oracle.satisfiable(formula)
    walks = {f: Walk(formula, steps, f) for f in oracle.FLAVOURS}
    ours = judge_dratify(formula, steps, checker, walks[DOCUMENTED_FLAVOUR], sat, a)
    verdicts = external.verdicts(formula, steps)
    for name, theirs in verdicts.items():
        judge_external(name, theirs, ours, walks, verdicts, sat, a, counts)
    trims = external.trims(formula, steps)
    for mode, run in trims.items():
        if run.crashes and mode != "sat":
            trims[mode] = settle_crash(mode, run, formula, steps, external, a, counts)
    for mode, run in trims.items():
        judge_drat_trim(mode, run, ours, formula, steps, sat, checker, external, trims, a, counts)

    walk = walks[DOCUMENTED_FLAVOUR]
    deletion_rule(formula, steps, walk, ours, checker, external, trims, a, counts)
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
    # what the proof tried: under the documented reading no deletion shrinks the root
    tried = walks["length-one"]
    counts["deletions_shrinking_the_root"] += tried.shrinks
    if walk.shrinks:
        a.flag("Critical", "root_shrank_under_the_documented_rule", str(walk.shrinks))
    counts["proofs_with_implicit_empty_clause"] += (
        walk.first_bad is None and walk.refuted_at not in (None, 0) and not walk.explicit)
    for category in a.notes:
        counts[category] += 1
    a.stale = tried.root_shrunk_at is not None
    a.verdicts = verdicts
    a.trims = trims
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


def gen_lookalike(rng, pool, counts):
    """Delete a clause that has a reason's shape but need not be the reason.

    Not one of ``FAMILIES``: it runs after them on its own random stream, so the
    default run stays the same 1,593 proofs.
    """
    formula = chain_formula(rng)
    conflict, assigned = oracle.propagate(formula)
    if conflict or len(assigned) < 2:
        return gen_lookalike(rng, pool, counts)
    # Half stay satisfiable. The rest carry a core no propagation reaches, so a proof
    # can be a real refutation with the deletion in it, and acceptance is on the table.
    tail = []
    if rng.random() < 0.5:
        x = max(abs(l) for c in formula for l in c) + 1
        core = [[x, x + 1], [-x, x + 1], [x, -x - 1], [-x, -x - 1]]
        formula += core
        tail = [("a", (x,)), ("a", ())]
    true_lits = sorted(assigned)
    t = rng.choice(true_lits)
    others = rng.sample([l for l in true_lits if l != t], min(rng.randint(1, 2), len(true_lits) - 1))
    clause = [t, *(-o for o in others)]
    rng.shuffle(clause)
    steps = []
    roll = rng.random()
    if roll < 0.5:
        formula.insert(rng.randint(0, len(formula)), clause)
    elif roll < 0.75:
        formula.insert(rng.randint(0, len(formula)), list(rng.choice(formula)))
        clause = rng.choice([c for c in formula if oracle.is_pseudo_unit(formula, c)
                             and len(set(c)) >= 2] or [clause])
        steps.append(("d", tuple(clause)))
    else:
        steps.append(("a", tuple(clause)))     # RUP: one of its literals is true
    steps.append(("d", tuple(clause)))
    if rng.random() < 0.3 and reasons_of(formula):
        steps.append(("d", tuple(rng.choice(reasons_of(formula)))))
    fresh = max((abs(l) for c in formula for l in c), default=1) + 1
    o = rng.choice(others)
    shape = rng.randrange(7)
    if shape == 0:
        steps += [("a", (-t, fresh)), ("a", (-fresh,))]
    elif shape == 1:
        steps += [("a", (fresh, -t))]
    elif shape == 2:
        steps += [("a", (-t,))]                # the attack on a real reason
    elif shape == 3:
        steps += [("a", (o, fresh)), ("a", (-fresh, o))]
    elif shape == 4:
        steps += list(dpll_proof(formula) or [])
    elif shape == 5:
        steps += [("a", (fresh, t, -o)), ("a", (-t, -fresh)), ("a", (t, o))]
    else:
        steps += mutate(rng, formula, dpll_proof(formula) or [("a", ())])
    return formula, [*steps, *(tail or [("a", ())])]


#: real solvers at a size the oracle cannot judge: dratify and drat-trim alone
LARGE_PHP = [(5, 4), (6, 5), (7, 6)]
LARGE_RANDOM = (40, 60, 80, 100, 120)


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
        self.last_exit = done.returncode
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


def large_solver_proofs(seed, external, pool, counts, mismatches, examples):
    """cadical and kissat past the oracle's limit: both engines, then drat-trim."""
    rng = random.Random(seed * 1009 + 2)
    native = native_engine()
    for solver in pool.solvers:
        shapes = [php_formula(rng, *size) for size in LARGE_PHP]
        for n in LARGE_RANDOM:
            shapes += [random_formula(rng, n, int(n * 4.6), (3,)) for _ in range(3)]
        for formula in shapes:
            steps = pool.solve(formula, solver)
            if pool.last_exit == 10:
                counts["large_solver_satisfiable_skipped"] += 1
                continue
            counts[f"large_solver_proofs_{solver}"] += 1
            counts["large_solver_steps"] += len(steps)
            ours = Dratify.run(formula, steps, "python")
            if native and Dratify.run(formula, steps, "native") != ours:
                mismatches[("Bug", "engine_disagreement", None)] += 1
                examples.setdefault(("Bug", "engine_disagreement", None),
                                    ("large", formula, steps, solver))
            counts["large_solver_dratify_ok"] += ours["ok"]
            for mode in ("default", "forward"):
                outcome = external.trim(mode, formula, steps).outcome
                counts[f"large_solver_drat_trim_{mode}_{outcome}"] += 1
            if not ours["ok"]:
                # a solver's own refutation, which dratify must accept
                mismatches[("Bug", "large_solver_proof_rejected", None)] += 1
                examples.setdefault(("Bug", "large_solver_proof_rejected", None),
                                    ("large", formula, steps, ours["reason"]))


#: how many proofs gen_lookalike contributes after the families, when drat-trim runs
LOOKALIKES = 1000


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
            for mode in ("default", "forward"):
                run = a.trims.get(mode)
                counts[f"solver_unsat_proofs_drat_trim_{mode}_rejects"] += bool(
                    run and run.outcome == "not_verified" and not oracle.satisfiable(formula))
        for severity, kind, detail in a.mismatches:
            label = None
            mismatches[(severity, kind, label)] += 1
            counts[f"mismatch_{kind}"] += 1
            examples.setdefault((severity, kind, label), (family, formula, steps, detail))
    if external.drat_trim and keep_examples:
        extra = collections.Counter()
        rng = random.Random(seed * 1009 + 1)
        for _ in range(LOOKALIKES):
            formula, steps = gen_lookalike(rng, pool, extra)
            a = analyse(formula, steps, checker, external, extra)
            for severity, kind, detail in a.mismatches:
                mismatches[(severity, kind, None)] += 1
                examples.setdefault((severity, kind, None), ("lookalike", formula, steps, detail))
        counts.update({f"lookalike_{key}": n for key, n in extra.items()})
        if pool.solvers:
            large_solver_proofs(seed, external, pool, counts, mismatches, examples)
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
        for mode in ("default", "forward"):
            tag = f"drat_trim_{mode}"
            needed += [f"{tag}_run", f"{tag}_agree", f"{tag}_disagree",
                       f"{tag}_it_accepts_dratify_rejects"]
        needed += ["drat_trim_autodetect_run", "drat_trim_verbose_run", "drat_trim_sat_run",
                   "note_implicit_empty_clause", "note_backward_skips_unused",
                   "deletion_rule_proofs_compared",
                   "deletion_rule_kept_by_both", "lookalike_deletion_rule_proofs_that_differ",
                   "lookalike_deletion_rule_kept_only_by_dratify"]
        needed += [f"large_solver_proofs_{s}" for s in pool.solvers]
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


#: A shrunk proof per category of disagreement with drat-trim, pinned by --self-test.
_TWO_VARS = [[1, 2], [-1, 2], [1, -2], [-1, -2]]
# (1 2) is RAT on 1 until (-1 7) joins these. The refutation needs it: (3) is RUP only
# through it.
_NEEDS_THE_LEMMA = [[-1, 3], [2, 3, 4], [2, 3, -4], [-2, 5], [-2, -5], [-3, 6], [-3, -6]]
TRIM_EXAMPLES = [
    ("note_implicit_empty_clause", _TWO_VARS, [("a", (1,))]),
    ("note_backward_skips_unused", [*_TWO_VARS, [-3, 4]], [("a", (-4,)), ("a", (1,)), ("a", ())]),
    ("note_other_pivot", [*_TWO_VARS, [-3, 5]], [("a", (3, 4)), ("a", (1,)), ("a", ())]),
    ("note_core_only_rat", [*_NEEDS_THE_LEMMA, [-1, 7]],
     [("a", (1, 2)), ("a", (3,)), ("a", ())]),
    ("note_deletion_of_nothing", _TWO_VARS, [("d", ()), ("a", (1,)), ("a", ())]),
]
#: the cases this corner exists for: dratify and drat-trim's default mode refuse them
TRIM_AGREEMENTS = [
    ("deleted reason", [[1], [-1, 2]], [("d", (-1, 2)), ("a", (-2,)), ("a", ())]),
    ("deletion-2", [[1], [-1, 2], [-2, 3]], [("d", (-1, 2)), ("a", (2,))]),
    ("reason deleted twice", [[-4, 6], [4, 5], [-5]],
     [("d", (-4, 6)), ("d", (-4, 6)), ("a", (-6,))]),
]

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
    ("drat_trim-6", "note_other_pivot",
     "drat-trim falls back to every literal of a lemma as the RAT pivot, in both modes; "
     "dratify documents the first literal only"),
    ("drat_trim-7", "note_core_only_rat",
     "drat-trim's backward mode skips a RAT candidate not yet marked as used, so it "
     "accepts a used lemma that is not RAT on the clauses present"),
    ("drat_trim-10", "note_crash_on_unsupported_empty_clause",
     "drat-trim reads past its clause database at a final empty clause with no conflict "
     "behind it, and can segfault; retried, it answers NOT VERIFIED, as dratify does"),
]

#: Notes the default seed need not reach, so they are listed whatever the counters say.
ALWAYS_LISTED = [
    {"id": "drat_trim-8", "severity": "Note",
     "summary": "drat-trim's parser reads `d 0` and then swallows the next token of the "
                "proof, so the next lemma can become a deletion; found by hand, pinned by "
                "--self-test"},
    {"id": "drat_trim-9", "severity": "Note",
     "summary": "no drat-trim mode honours a unit deletion and also checks a refutation: "
                "-S checks deletions and skips additions, so it is counted and not compared"},
    {"id": "drat_trim-11", "severity": "Note",
     "summary": "dratify's root-unit test keeps more clauses than drat-trim's reason test, "
                "and no verdict moved on either side; one README sentence claims otherwise"},
]

NOT_CHECKED = [
    "drat-trim's -p plain mode, -u, -O and its LRAT and core outputs: only -I, -f, -v, -S "
    "and -t were run. -W was run by hand on the two named cases, not on the corpus",
    "any drat-trim commit but the one recorded under external_checkers, and any build but "
    "cc -std=c99 -O2 on macOS arm64: its crash depends on what the heap holds",
    "drat-trim's binary proof reading: text only, with -I, and without it as a control",
    "rate with no -p flag, where it tries every literal as a pivot",
    "rate's LRAT and GRAT output, and DPR proofs",
    "binary DRAT: dratify documents text proofs only",
    "minisat: it writes no DRAT proof, so it contributed no proofs",
    "the oracle past 16 variables: the large solver proofs are judged by dratify and "
    "drat-trim alone, up to 120 variables, which is not the README's uuf and php scale",
    "tautological clauses in the input formula, and DIMACS parsing corners",
    "the list-of-steps and MemoryProof paths into check_proof: only proof text is passed",
    "that the root-unit test and the reason test can never give different verdicts: that "
    "rests on the argument in drat_trim-11 and on the proofs run here, not on a proof "
    "checked by machine",
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
            "drat-trim": (args.drat_trim_build or drat_trim) if drat_trim else
            "NOT RUN: not on PATH and no --drat-trim given",
            "drat_trim_modes": {m: " ".join(f) or "(no flags)"
                                for m, f in DRAT_TRIM_MODES.items()} if drat_trim else {},
        },
        "findings": [
            {"id": "drat_trim-1", "status": "fixed", "severity": "Critical",
             "summary": "dratify kept a literal in the root assignment after deleting "
                        "the only clause implying it, on both engines, so it returned "
                        "ok=True on satisfiable formulas"}
        ] + [
            {"id": ident, "severity": "Note", "summary": summary}
            for ident, category, summary in NOTE_FINDINGS if counts[category]
        ] + ALWAYS_LISTED,
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

        _, kinds, _ = run(LengthOnlyDeletion)
        expect("the old deletion rule is flagged as a soundness failure",
               kinds & CRITICAL_KINDS, str(sorted(kinds)))

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

        print("drat-trim's calling convention, against shell stubs:")
        record = pathlib.Path(workdir) / "argv"
        recorder = write_stub(workdir, "records",
                              f'echo "$@" >> "{record}"\necho "c something"\n'
                              'echo "s VERIFIED"\nexit 40')
        ext = External(None, recorder, workdir)
        recorded = ext.trim("forward", [[1], [-1]], [("a", ())])
        argv = record.read_text().split()
        expect("the files come first, then the flags and a -t limit",
               argv[0].endswith(".cnf") and argv[1].endswith(".drat")
               and argv[2:4] == ["-f", "-I"] and argv[4] == "-t" and argv[5].isdigit(),
               " ".join(argv[2:]))
        expect("an odd exit code does not hide s VERIFIED", recorded.outcome == "verified")
        no_code = write_stub(workdir, "rejects_exit_0", 'echo "s NOT VERIFIED"; exit 0')
        expect("exit 0 does not hide s NOT VERIFIED",
               External(None, no_code, workdir).trim("default", [[1]], []).outcome == "not_verified")
        cr = write_stub(workdir, "carriage", 'printf "\\rc x\\n\\rs VERIFIED\\n"; exit 1')
        expect("its \\r prefix does not hide the line",
               External(None, cr, workdir).trim("default", [[1]], []).outcome == "verified")
        timed = write_stub(workdir, "timed_out", 'echo "s TIMEOUT"; exit 0')
        derived = write_stub(workdir, "derived", 'echo "s DERIVATION"; exit 1')
        expect("s TIMEOUT and s DERIVATION are read as what they are",
               External(None, timed, workdir).trim("default", [[1]], []).outcome == "timeout"
               and External(None, derived, workdir).trim("forward", [[1]], []).outcome == "derivation")
        expect("no verdict is not a rejection",
               External(None, says_nothing, workdir).trim("default", [[1]], []).outcome == "none")

        def trim_kinds(stub, formula, steps, checker=Dratify):
            counts = collections.Counter()
            a = analyse(formula, steps, checker, External(None, stub, workdir), counts)
            return a, counts

        a, counts = trim_kinds(says_nothing, [[1], [-1]], [("a", ())])
        expect("drat-trim's lack of a verdict fails the run",
               "drat_trim_no_verdict" in a.kinds, str(a.kinds))
        a, counts = trim_kinds(timed, [[1], [-1]], [("a", ())])
        expect("a timeout is counted and not judged",
               counts["drat_trim_default_outcome_timeout"] == 1
               and "drat_trim_unexplained" not in a.kinds, str(a.kinds))
        crashes_early = write_stub(workdir, "crashes_at_the_empty_clause",
                                   f'if [ "$(grep -c "^0$" "$2")" = 1 ] && [ ! -e "{workdir}/crashed" ]; '
                                   f'then touch "{workdir}/crashed"; kill -SEGV $$; fi; '
                                   f'rm -f "{workdir}/crashed"; echo "s NOT VERIFIED"')
        a, counts = trim_kinds(crashes_early, [[1, 2]], [("a", ())])
        expect("a crash at an unsupported empty clause, gone once the clause is, is a Note",
               counts["drat_trim_default_note_crash_on_unsupported_empty_clause"] == 1
               and not a.mismatches, str(a.kinds))
        one_zero = write_stub(workdir, "crashes_at_one_empty_clause",
                              'if [ "$(grep -c "^0$" "$2")" = 1 ]; then kill -SEGV $$; fi; '
                              'echo "s NOT VERIFIED"')
        a, counts = trim_kinds(one_zero, [[1, 2]], [("a", ())])
        expect("a crash on every run takes its answer from a proof that pads the clause",
               counts["drat_trim_default_crashed_every_time"] == 1
               and a.trims["default"].outcome == "not_verified" and not a.mismatches,
               str(a.kinds))
        crashes_anyway = write_stub(workdir, "crashes_anyway",
                                    f'if [ ! -e "{workdir}/crashed" ]; then '
                                    f'touch "{workdir}/crashed"; kill -SEGV $$; fi; '
                                    f'rm -f "{workdir}/crashed"; echo "s NOT VERIFIED"')
        a, _ = trim_kinds(crashes_anyway, [[1, 2]], [("a", (1,))])
        expect("any other crash fails the run", "drat_trim_crash_unexplained" in a.kinds, str(a.kinds))
        always = write_stub(workdir, "always_crashes", "kill -SEGV $$")
        a, _ = trim_kinds(always, [[1, 2]], [("a", ())])
        expect("a crash that never gives way to a verdict fails the run",
               "drat_trim_no_verdict" in a.kinds, str(a.kinds))
        a, _ = trim_kinds(says_yes, [[1, 2], [-1, 2]], [("a", (2,)), ("a", ())])
        expect("a drat-trim that accepts a false refutation of a satisfiable formula is "
               "not explained away", "external_accepted_satisfiable" in a.kinds, str(a.kinds))
        php = [[1, 2], [-1, 2], [1, -2], [-1, -2]]
        a, _ = trim_kinds(says_no, php, [("a", (1,)), ("a", ())])
        expect("a drat-trim that refuses a valid refutation is unexplained",
               "drat_trim_unexplained" in a.kinds, str(a.kinds))
        a, _ = trim_kinds(says_yes, [*php, [-3, 4]], [("a", (-4,)), ("a", ())])
        expect("backward skipping is no excuse when forward mode accepts too",
               "drat_trim_unexplained" in a.kinds, str(a.kinds))
        flips = write_stub(workdir, "text_flag_matters",
                           'case " $* " in *" -I "*) echo "s NOT VERIFIED";; '
                           '*) echo "s VERIFIED";; esac')
        a, _ = trim_kinds(flips, php, [("a", (1,)), ("a", ())])
        expect("a verdict that depends on -I is flagged",
               "drat_trim_autodetect_changes_the_verdict" in a.kinds, str(a.kinds))
        says_kept = write_stub(workdir, "says_it_kept",
                               'echo "c ignoring deletion instruction 7: [3] 4 5 0"; '
                               'echo "s NOT VERIFIED"')
        a, _ = trim_kinds(says_kept, php, [("d", (1, 2))])
        expect("a reason drat-trim kept and dratify did not is flagged",
               "deletion_kept_only_by_drat_trim" in a.kinds, str(a.kinds))
        depends = write_stub(workdir, "needs_the_deletion",
                             'if grep -q "^d " "$2"; then echo "s VERIFIED"; '
                             'else echo "s NOT VERIFIED"; fi')
        a, _ = trim_kinds(depends, [[1], [2], [-1, 2]], [("d", (-1, 2))])
        expect("a verdict that moves without a look-alike's deletion is flagged",
               "deletion_rule_moved_the_verdict" in a.kinds, str(a.kinds))

        drat_trim = args.drat_trim or shutil.which("drat-trim")
        if drat_trim:
            print("the real drat-trim, one shrunk example per category:")
            for note, formula, steps in TRIM_EXAMPLES:
                a, _ = trim_kinds(drat_trim, formula, steps)
                expect(f"{note}: F={formula} proof={steps}",
                       note in a.notes and not a.mismatches, f"{a.notes} {a.kinds or ''}")
            for name, formula, steps in TRIM_AGREEMENTS:
                a, counts = trim_kinds(drat_trim, formula, steps)
                expect(f"both refuse the {name} case",
                       counts["drat_trim_default_agree"] == 1 and not a.mismatches, str(a.kinds))
            print("the documented semantics beside the real drat-trim:")
            old = globals()["LOOKALIKES"]
            globals()["LOOKALIKES"] = 100
            try:
                _, kinds, mismatches = run(Reference, External(external_rate, drat_trim, workdir))
                expect("every drat-trim disagreement has a named cause", not kinds,
                       str(dict(mismatches)))
                _, kinds, _ = run(LengthOnlyDeletion, External(external_rate, drat_trim, workdir))
                expect("the old deletion rule is still flagged with drat-trim in the run",
                       kinds & CRITICAL_KINDS, str(sorted(kinds)))
            finally:
                globals()["LOOKALIKES"] = old
        else:
            print("  drat-trim is not available: its behaviour was exercised only on stubs")

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
    parser.add_argument("--drat-trim-build", dest="drat_trim_build",
                        help="what to record about that binary, such as its commit")
    parser.add_argument("--results", default=f"campaign/results/{CORNER}.json",
                        help="where to write the results; empty to write nothing")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        return self_test(args)
    return main_run(args)


if __name__ == "__main__":
    sys.exit(main())
