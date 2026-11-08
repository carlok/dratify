# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Soundness campaign, the `api` corner: one proof, every way of handing it over.

The same proof goes through every shape the package offers, and every result
must agree on every field, with the oracle judging the proof itself:

* `check_proof` with text (several layouts), a `MemoryProof`, a list of steps
  (tuple and list literals), a tuple of steps, a generator, the text from
  `MemoryProof.to_text`, and the text a `ProofWriter` wrote (buffered,
  unbuffered, to a path), each on engine="python" and engine="native";
* the streaming Python API: `DRATChecker.check` on a list and on a generator,
  `DRATChecker.check_step` driven by hand, a final `check([])` after that, and
  `check` called twice on two pieces of the proof;
* the Rust crate driven directly, compiled here from `rust/src` with a small
  driver: `Checker::check`, `Checker::check_step`, `check(&[])` after that, and
  `check` on two pieces.

`check_step` alone does not set `ok` or `reason`: its contract is the bool it
returns, so that shape is compared on the counters and the bools, and `ok` and
`reason` are compared through the `check([])` that follows it.

Run from the repo root: `python -m campaign.gen_api`. `--self-test` runs the
harness against deliberately wrong checkers and requires it to flag each one.

Every mismatch makes the exit status non-zero, including those labelled with a
finding: a label explains a mismatch, it does not excuse it.
"""

from __future__ import annotations

import argparse
import collections
import dataclasses
import io
import json
import os
import pathlib
import random
import shutil
import subprocess
import sys
import tempfile
import time
import types

import dratify
from dratify import (CNF, DRATChecker, MemoryProof, ProofWriter, check_proof,
                     from_dimacs, parse_dimacs, parse_proof, register_native)
from dratify.proof import CheckResult

from campaign import oracle

REPO = pathlib.Path(__file__).resolve().parent.parent
RESULTS = REPO / "campaign" / "results" / "api.json"

DEFAULT_SEED = 20261108
DEFAULT_INSTANCES = 6000

FIELDS = CheckResult.__slots__
#: what `check_step` is not responsible for; see the module docstring
STREAM_UNSET = {"ok", "reason", "truth", "report"}

FLAG_COMBOS = [(True, True), (True, False), (False, True), (False, False)]

ENGINE_SHAPES = ("text", "text_oneline", "text_commented", "text_crlf", "memory",
                 "memory_to_text", "list", "list_with_list_lits", "tuple_of_steps",
                 "generator", "writer_buffered", "writer_unbuffered", "writer_path",
                 "formula_parsed")
STREAM_SHAPES = ("check", "check_generator", "check_step", "check_step_then_check",
                 "check_in_two_pieces")
RUST_SHAPES = ("rust_check", "rust_check_step", "rust_check_step_then_check",
               "rust_check_in_two_pieces")

# The labels name findings in campaign/findings/. UNEXPLAINED is everything else.
L_NO_VALIDATION = "api-1"
L_STALE_ROOT = "api-2"
L_FAILED_CLAUSE = "api-3"
L_BOUND = "api-4"
L_REENTRY = "api-5"
L_WRITER = "api-6"
L_UNORDERED = "api-7"
UNEXPLAINED = "UNEXPLAINED"

FINDINGS = [
    {"id": L_NO_VALIDATION, "severity": "Critical",
     "summary": "DRATChecker.check and check_step skip _validate_steps: a negative "
                "literal gets ok=True on a satisfiable formula, the 0.1.7 hole, "
                "still open on the public streaming API (Python only)"},
    {"id": L_STALE_ROOT, "severity": "Critical",
     "summary": "deleting a reason clause leaves its root assignment in place: "
                "d -1 2 0, -2 0, 0 gets ok=True on the satisfiable (1)(-1 2), both "
                "engines, every shape"},
    {"id": L_FAILED_CLAUSE, "severity": "Bug",
     "summary": "failed_clause keeps repeated literals on engine=native and drops "
                "them on engine=python"},
    {"id": L_BOUND, "severity": "Bug",
     "summary": "the variable bound in check_proof depends on the shape and on the "
                "text's length: 5 0 on a 2-variable formula is a verdict as text and "
                "ValueError as a list or MemoryProof, and 7 0 flips with a comment"},
    {"id": L_REENTRY, "severity": "Bug",
     "summary": "check on a used checker (Python and Rust; the only way to read a "
                "Rust stream's result) reports ok=True, reached_empty=True and "
                "'input formula is refuted' on a proof with no empty clause, and "
                "'every step verified' after a rejected step"},
    {"id": L_WRITER, "severity": "Note",
     "summary": "ProofWriter and MemoryProof.to_text turn a negative literal into a "
                "different clause, where check_proof on the same MemoryProof raises"},
    {"id": L_UNORDERED, "severity": "Bug",
     "summary": "_validate_steps lets a step's literals be a set: engine=python raises "
                "TypeError at the RAT check, engine=native returns a verdict"},
]


# --------------------------------------------------------------------------
# instances
# --------------------------------------------------------------------------


@dataclasses.dataclass
class Instance:
    index: int
    tag: str
    nvars: int                       # the header's count
    clauses: list                    # DIMACS, no tautologies
    steps: list                      # ("a" | "d", tuple of DIMACS)
    cut: int = 0                     # where check_in_two_pieces splits the proof

    def cnf(self) -> CNF:
        f = CNF(self.nvars)
        for c in self.clauses:
            f.add_dimacs(c)
        return f

    def internal(self) -> list:
        return [(k, tuple(from_dimacs(l) for l in lits)) for k, lits in self.steps]

    def describe(self) -> str:
        return f"#{self.index} {self.tag} n={self.nvars} F={self.clauses} P={self.steps}"


def _random_clause(rng, nvars, lo=1, hi=3):
    size = rng.randint(lo, min(hi, nvars))
    return [v if rng.random() < 0.5 else -v for v in rng.sample(range(1, nvars + 1), size)]


def _resolvent(rng, current):
    """A resolvent of two clauses present, which is RUP, or None."""
    for _ in range(12):
        if len(current) < 2:
            return None
        a, b = rng.sample(current, 2)
        pivots = [l for l in a if -l in b]
        if len(pivots) == 1:
            res = sorted((set(a) | set(b)) - {pivots[0], -pivots[0]}, key=abs)
            if not any(-l in res for l in res):
                return res
    return None


def _refutation(formula, order):
    """A tree-shaped refutation of an unsatisfiable formula, each lemma RUP."""
    lemmas = []
    current = [list(c) for c in formula]

    def walk(path):
        clause = [-l for l in path]
        if oracle.rup(current, clause):
            if clause:
                lemmas.append(clause)
                current.append(clause)
            return
        var = next((v for v in order if v not in {abs(l) for l in path}), None)
        if var is None:
            raise AssertionError("no conflict on a full assignment: F is satisfiable")
        walk(path + [var])
        walk(path + [-var])
        if clause:
            lemmas.append(clause)
            current.append(clause)

    walk([])
    return lemmas


def _make_formula(rng):
    kind = rng.choice(("unsat", "unsat", "unsat", "sat", "sat", "units", "units",
                       "root_conflict", "has_empty", "no_clauses", "repeated_lits"))
    nvars = rng.randint(2, 7)
    if kind == "unsat":
        for _ in range(60):
            n = rng.randint(2, 5)
            clauses = [_random_clause(rng, n, 1 if rng.random() < 0.1 else 2, 3)
                       for _ in range(rng.randint(4 * n, 8 * n))]
            if not oracle.satisfiable(clauses) and not oracle.propagate(clauses)[0]:
                return kind, n, clauses
        n = 2
        return kind, n, [[1, 2], [1, -2], [-1, 2], [-1, -2]]
    if kind == "sat":
        clauses = [_random_clause(rng, nvars) for _ in range(rng.randint(1, 2 * nvars))]
    elif kind == "units":
        # a chain, so the root assignment is not empty and has reason clauses
        chain = rng.sample(range(1, nvars + 1), nvars)
        clauses = [[chain[0] if rng.random() < 0.5 else -chain[0]]]
        for a, b in zip(chain, chain[1:]):
            if rng.random() < 0.7:
                head = clauses[0][0] if abs(clauses[0][0]) == a else a
                clauses.append([-head, b if rng.random() < 0.5 else -b])
        clauses += [_random_clause(rng, nvars, 2, 3) for _ in range(rng.randint(0, 3))]
    elif kind == "root_conflict":
        v = rng.randint(1, nvars)
        clauses = [[v], [-v]] + [_random_clause(rng, nvars, 2, 3) for _ in range(rng.randint(0, 3))]
        rng.shuffle(clauses)
    elif kind == "has_empty":
        clauses = [[]] + [_random_clause(rng, nvars) for _ in range(rng.randint(0, 3))]
    elif kind == "no_clauses":
        clauses = []
    else:
        clauses = [c + [rng.choice(c)] for c in
                   (_random_clause(rng, nvars) for _ in range(rng.randint(1, 2 * nvars)))]
    clauses = [c for c in clauses if not any(-l in c for l in c)]
    return kind, nvars, clauses


def _stale_root_attack(rng, index):
    """Delete a reason, then contradict what it implied. See api-2."""
    nvars = rng.randint(2, 5)
    u, w = rng.sample(range(1, nvars + 1), 2)
    u = u if rng.random() < 0.5 else -u
    w = w if rng.random() < 0.5 else -w
    clauses = [[u], [-u, w]]
    steps = [("d", (-u, w)), ("a", (-w,)), ("a", ())]
    return Instance(index, "stale_root_attack", nvars, clauses, steps, rng.randint(0, 3))


def _make_proof(rng, kind, nvars, clauses):
    """A proof that mixes every kind of step, and may or may not go through."""
    current = [list(c) for c in clauses]
    steps = []
    top = nvars
    gap = rng.random() < 0.06   # fresh variables far above the formula's: api-4

    plan = []
    if kind == "unsat" and rng.random() < 0.75:
        order = list(range(1, nvars + 1))
        rng.shuffle(order)
        plan = _refutation(clauses, order)

    def add_noise():
        nonlocal top
        op = rng.choices(("rup", "rat", "fresh", "bad", "del_present", "del_unit",
                          "del_absent", "del_empty"),
                         (28, 14, 8, 5, 22, 6, 6, 2))[0]
        if op == "rup":
            c = _resolvent(rng, current)
            if c is None:
                for _ in range(20):
                    cand = _random_clause(rng, nvars) if nvars else []
                    if oracle.rup(current, cand):
                        c = cand
                        break
            if c:
                steps.append(("a", tuple(c)))
                current.append(c)
        elif op == "rat" and nvars:
            for _ in range(20):
                c = _random_clause(rng, nvars)
                if oracle.rat(current, c, c[0]) and not oracle.rup(current, c):
                    steps.append(("a", tuple(c)))
                    current.append(c)
                    break
        elif op == "fresh" and top - nvars < 3:
            top += rng.randint(2, 7) if gap else 1
            new = top
            others = _random_clause(rng, nvars, 1, 2) if nvars else []
            c = [new if rng.random() < 0.5 else -new] + others
            steps.append(("a", tuple(c)))
            current.append(c)
        elif op == "bad" and nvars:
            for _ in range(20):
                c = _random_clause(rng, nvars)
                if not oracle.rup(current, c) and not oracle.rat(current, c, c[0]):
                    steps.append(("a", tuple(c)))  # rejected, so never in current
                    break
        elif op == "del_present":
            candidates = [c for c in current if len(set(c)) >= 2]
            if candidates:
                c = list(rng.choice(candidates))
                rng.shuffle(c)
                steps.append(("d", tuple(c)))
                current.remove(next(x for x in current if set(x) == set(c)))
        elif op == "del_unit":
            candidates = [c for c in current if len(set(c)) == 1]
            if candidates:
                steps.append(("d", tuple(rng.choice(candidates))))
        elif op == "del_absent" and nvars:
            c = _random_clause(rng, nvars, 2, 3) if nvars >= 2 else [1]
            if not any(set(x) == set(c) for x in current):
                steps.append(("d", tuple(c)))
        elif op == "del_empty":
            steps.append(("d", ()))

    for _ in range(rng.randint(0, 4)):
        add_noise()
    for lemma in plan:
        steps.append(("a", tuple(lemma)))
        current.append(list(lemma))
        if rng.random() < 0.12:
            add_noise()
    for _ in range(rng.randint(0, 3)):
        add_noise()

    ending = rng.random()
    if ending < 0.75:
        steps.append(("a", ()))
        if rng.random() < 0.3:
            # past the end: never checked, never counted
            steps.append(("a", (1,) if nvars else ()))
            if nvars >= 2:
                steps.append(("d", (1, 2)))

    # repeated literals, in additions and deletions, keeping the first literal
    out = []
    for k, lits in steps:
        if lits and rng.random() < 0.08:
            lits = lits + (rng.choice(lits),)
        out.append((k, lits))
    return out


def _bound_gap(rng, index):
    """A fresh variable far from the formula's: vacuously RAT. See api-4."""
    nvars = rng.randint(1, 4)
    clauses = [_random_clause(rng, nvars, 1, 2) for _ in range(rng.randint(1, 3))]
    fresh = nvars + rng.randint(2, 8)
    steps = [("a", (fresh if rng.random() < 0.5 else -fresh,))]
    if rng.random() < 0.3:
        steps.append(("a", ()))
    return Instance(index, "bound_gap", nvars, clauses, steps, rng.randint(0, len(steps)))


def make_instance(rng, index) -> Instance:
    roll = rng.random()
    if roll < 0.03:
        return _stale_root_attack(rng, index)
    if roll < 0.06:
        return _bound_gap(rng, index)
    kind, nvars, clauses = _make_formula(rng)
    steps = _make_proof(rng, kind, nvars, clauses)
    if kind == "unsat":
        nvars = rng.choice((nvars, nvars, nvars + rng.randint(1, 3)))   # header over-declares
    return Instance(index, kind, nvars, clauses, steps, rng.randint(0, len(steps)))


def writer_flush_instance(index) -> Instance:
    """Long enough to cross ProofWriter's 4096-entry buffer."""
    clauses = [[1, 2], [1, -2], [-1, 2], [-1, -2], [3, 4]]
    steps = [("d", (5, 6)) for _ in range(4200)] + [("a", (1,)), ("a", ())]
    return Instance(index, "writer_flush", 4, clauses, steps, 2100)


# --------------------------------------------------------------------------
# the ways of writing one proof down
# --------------------------------------------------------------------------


def text_lines(steps) -> list:
    out = []
    for kind, lits in steps:
        body = " ".join(str(l) for l in lits)
        out.append(("d " if kind == "d" else "") + (f"{body} 0" if lits else "0"))
    return out


def to_text(steps) -> str:
    return "".join(line + "\n" for line in text_lines(steps))


def commented(steps) -> str:
    out = ["c leading comment"]
    for line in text_lines(steps):
        out.append(line.replace("d ", "d", 1) if line.startswith("d ") and line != "d 0" else line)
        out.append("c x")
    return "\n".join(out) + "\n"


def to_memory(steps, rng_pick=False) -> MemoryProof:
    proof = MemoryProof()
    for kind, lits in steps:
        (proof.delete if kind == "d" else proof.add)(iter(lits))
    return proof


def to_writer(steps, sink, buffered) -> ProofWriter:
    writer = ProofWriter(sink, buffered=buffered)
    for kind, lits in steps:
        (writer.delete if kind == "d" else writer.add)(iter(lits))
    return writer


# --------------------------------------------------------------------------
# what is being tested; the self-test swaps this for something wrong
# --------------------------------------------------------------------------


class Real:
    name = "dratify"

    def whole(self, formula, proof, check_rat, apply_deletions, engine):
        return check_proof(formula, proof, check_rat=check_rat,
                           apply_deletions=apply_deletions, engine=engine)

    def checker(self, formula, check_rat, apply_deletions):
        return DRATChecker(formula, check_rat=check_rat, apply_deletions=apply_deletions)

    def rust_row(self, row):
        return row


def _snap(r) -> dict:
    out = {f: getattr(r, f) for f in FIELDS}
    out["truth"] = bool(r)
    out["report"] = r.report()
    return out


def _call(fn) -> dict:
    """A result, or the exception standing in for one. Both are compared."""
    try:
        return _snap(fn())
    except Exception as e:  # noqa: BLE001 - the type is what gets compared
        return {"exception": type(e).__name__, "message": str(e)}


def differing(a: dict, b: dict, ignore=frozenset()) -> list:
    if "exception" in a or "exception" in b:
        if a.get("exception") != b.get("exception"):
            return ["exception"]
        return []
    return [k for k in a if k not in ignore and a[k] != b.get(k)]


# --------------------------------------------------------------------------
# the oracle's verdict
# --------------------------------------------------------------------------


def _root(clauses):
    conflict, assigned = oracle.propagate(clauses)
    return (True, frozenset()) if conflict else (False, assigned)


@dataclasses.dataclass
class Judged:
    fields: dict
    stale: bool                      # a deletion changed what propagates at the root
    satisfiable: bool
    accepted_kinds: list             # what each step was, until the walk stopped
    judged: int


def judge(inst: Instance, check_rat, apply_deletions, counts) -> Judged:
    """Walk the proof under the rule dratify documents, by definition.

    dratify documents that only deletions of unit clauses are ignored, so this
    is the oracle's `length-one` flavour, restricted to what the flags enable.
    """
    formula = [list(c) for c in inst.clauses]
    sat = oracle.satisfiable(formula)
    fields = {"ok": False, "reached_empty": False, "steps": 0, "rup_steps": 0,
              "rat_steps": 0, "deletions": 0, "ignored_deletions": 0,
              "resolvents_checked": 0, "failed_step": -1, "failed_clause": None}
    kinds = []
    if oracle.propagate(formula)[0]:
        fields.update(ok=True, reached_empty=True)
        counts["formula_refuted_by_propagation"] += 1
        return Judged(fields, False, sat, kinds, 0)

    current = formula
    stale = False
    judged = 0
    for kind, lits in inst.steps:
        fields["steps"] += 1
        judged += 1
        distinct = list(dict.fromkeys(lits))
        if kind == "d":
            if len(distinct) <= 1:
                fields["ignored_deletions"] += 1
                counts["del_ignored_empty" if not distinct else "del_ignored_unit"] += 1
                kinds.append("d")
            elif apply_deletions:
                after, present = oracle.remove_one(current, distinct)
                if present:
                    if _root(after) != _root(current):
                        stale = True
                        counts["del_of_a_reason"] += 1
                    current = after
                    fields["deletions"] += 1
                    counts["del_applied"] += 1
                else:
                    fields["ignored_deletions"] += 1
                    counts["del_ignored_absent"] += 1
                kinds.append("d")
            else:
                counts["del_with_deletions_off"] += 1
                kinds.append("d")
            continue
        if len(distinct) != len(lits):
            counts["step_with_repeated_literal"] += 1
        is_rup = oracle.rup(current, lits)
        if is_rup:
            fields["rup_steps"] += 1
            counts["step_rup"] += 1
            kinds.append("rup")
            if not oracle.implies(current, lits):
                raise AssertionError(f"oracle: RUP but not implied, {inst.describe()}")
        elif check_rat and lits and oracle.rat(current, lits, lits[0]):
            fields["rat_steps"] += 1
            counts["step_rat_only"] += 1
            kinds.append("rat")
            if not oracle.preserves_sat(current, lits):
                raise AssertionError(f"oracle: RAT but not sat-preserving, {inst.describe()}")
            neg = -lits[0]
            have = set(lits)
            fields["resolvents_checked"] += sum(
                1 for d in current if neg in d
                and not any(-l in have for l in set(d) if l != neg))
        else:
            fields["failed_step"] = fields["steps"]
            fields["failed_clause"] = tuple(from_dimacs(l) for l in distinct)
            counts["step_rejected"] += 1
            if len(distinct) != len(lits):
                counts["rejected_step_with_repeated_literal"] += 1
            kinds.append("rejected")
            break
        if not lits:
            fields["reached_empty"] = True
            fields["ok"] = True
            break
        current = current + [distinct]
    return Judged(fields, stale, sat, kinds, judged)


def replay_agrees(inst: Instance, verdict: Judged) -> bool:
    """Keep `judge` honest: oracle.replay must read the proof the same way."""
    formula = [list(c) for c in inst.clauses]
    if oracle.propagate(formula)[0]:
        return True
    walked, _ = oracle.replay(formula, inst.steps, "length-one")
    for step, kind in zip(walked, verdict.accepted_kinds):
        if step.kind == "d":
            continue
        if step.rup != (kind == "rup"):
            return False
        if kind == "rejected" and step.acceptable:
            return False
    return True


# --------------------------------------------------------------------------
# Rust, driven directly. No Python binding exposes Checker::check_step.
# --------------------------------------------------------------------------

RUST_DRIVER = r"""
use dratify::{CheckResult, Checker, Lit};
use std::io::{self, BufRead, Write};

fn lits(s: &str) -> Vec<Lit> {
    s.split_whitespace().map(|t| t.parse().unwrap()).collect()
}

fn emit(out: &mut impl Write, tag: &str, r: &CheckResult) {
    let failed: Vec<String> = r.failed_clause.iter().map(|l| l.to_string()).collect();
    writeln!(out, "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}", tag, r.ok, r.reason, r.steps,
        r.rup_steps, r.rat_steps, r.deletions, r.ignored_deletions, r.resolvents_checked,
        r.failed_step, failed.join(" "), r.reached_empty).unwrap();
}

fn main() {
    let stdin = io::stdin();
    let mut input = stdin.lock().lines().map(|l| l.unwrap());
    let stdout = io::stdout();
    let mut out = io::BufWriter::new(stdout.lock());
    while let Some(head) = input.next() {
        let h: Vec<usize> = head.split_whitespace().map(|t| t.parse().unwrap()).collect();
        let (nvars, rat, del, nc, ns, cut) = (h[0] as u32, h[1] == 1, h[2] == 1, h[3], h[4], h[5]);
        let clauses: Vec<Vec<Lit>> = (0..nc).map(|_| lits(&input.next().unwrap())).collect();
        let steps: Vec<(bool, Vec<Lit>)> = (0..ns).map(|_| {
            let line = input.next().unwrap();
            (line.starts_with('d'), lits(&line[1..]))
        }).collect();

        let whole = Checker::new(nvars, &clauses, rat, del).check(&steps);
        emit(&mut out, "rust_check", &whole);

        // `result` is private: `check(&[])` is the only way to read the fields
        let mut c = Checker::new(nvars, &clauses, rat, del);
        let mut bools = String::new();
        for (is_del, l) in &steps {
            let accepted = c.check_step(*is_del, l);
            bools.push(if accepted { '1' } else { '0' });
            if !accepted || (!*is_del && l.is_empty()) {
                break;
            }
        }
        writeln!(out, "bools\t{}", bools).unwrap();
        let after = c.check(&[]);
        emit(&mut out, "rust_check_step_then_check", &after);

        let mut c = Checker::new(nvars, &clauses, rat, del);
        let first = c.check(&steps[..cut]);
        let second = if first.failed_step != -1 || first.reached_empty {
            first
        } else {
            c.check(&steps[cut..])
        };
        emit(&mut out, "rust_check_in_two_pieces", &second);
    }
}
"""


def build_rust(workdir: pathlib.Path) -> pathlib.Path | None:
    rustc = shutil.which("rustc")
    if rustc is None:
        return None
    rlib = workdir / "libdratify.rlib"
    subprocess.run([rustc, "--edition", "2021", "-C", "opt-level=2", "--crate-type", "rlib",
                    "--crate-name", "dratify", str(REPO / "rust" / "src" / "lib.rs"),
                    "-o", str(rlib)], check=True, capture_output=True)
    driver = workdir / "driver.rs"
    driver.write_text(RUST_DRIVER)
    binary = workdir / "driver"
    subprocess.run([rustc, "--edition", "2021", "-C", "opt-level=2", str(driver),
                    "--extern", f"dratify={rlib}", "-o", str(binary)],
                   check=True, capture_output=True)
    return binary


def run_rust(binary, jobs) -> list:
    """One (rows by shape, bools) per job, in order."""
    lines = []
    for inst, check_rat, apply_deletions in jobs:
        f = inst.cnf()
        steps = inst.internal()
        lines.append(f"{f.nvars} {int(check_rat)} {int(apply_deletions)} "
                     f"{len(f.clauses)} {len(steps)} {inst.cut}")
        lines += [" ".join(map(str, c)) for c in f.clauses]
        lines += [("d" if k == "d" else "a") + " " + " ".join(map(str, l)) for k, l in steps]
    done = subprocess.run([str(binary)], input="\n".join(lines) + "\n", text=True,
                          capture_output=True, check=True)
    rows = done.stdout.splitlines()
    out = []
    for i in range(0, len(rows), 4):
        whole, bools, after, pieces = rows[i:i + 4]
        out.append(({"rust_check": _rust_row(whole),
                     "rust_check_step_then_check": _rust_row(after),
                     "rust_check_in_two_pieces": _rust_row(pieces)},
                    bools.split("\t")[1]))
    return out


def _rust_row(line: str) -> dict:
    p = line.split("\t")
    failed_step = int(p[10 - 1])
    failed = tuple(int(x) for x in p[10].split())
    return {"ok": p[1] == "true", "reason": p[2], "steps": int(p[3]), "rup_steps": int(p[4]),
            "rat_steps": int(p[5]), "deletions": int(p[6]), "ignored_deletions": int(p[7]),
            "resolvents_checked": int(p[8]), "failed_step": failed_step,
            "failed_clause": failed if failed_step != -1 else None,
            "reached_empty": p[11] == "true"}


# --------------------------------------------------------------------------
# the run
# --------------------------------------------------------------------------


class Tally:
    def __init__(self):
        self.counts = collections.Counter()
        self.mismatches = collections.Counter()
        self.examples = {}
        self.judged = 0

    def mismatch(self, label, where, detail, inst):
        key = f"{label} {where}"
        self.mismatches[label] += 1
        self.examples.setdefault(key, f"{detail} on {inst.describe()[:400]}")

    def unexplained(self):
        return self.mismatches[UNEXPLAINED]


def _engine_shapes(inst, f, rat, dels, engine, impl, tmp):
    steps = inst.internal()
    text = to_text(inst.steps)
    memory = to_memory(steps)

    def writer(buffered):
        sink = io.StringIO()
        with to_writer(steps, sink, buffered):
            pass
        return sink.getvalue()

    def by_path():
        path = tmp / "proof.drat"
        with to_writer(steps, path, True):
            pass
        return path.read_text()

    return {
        "text": lambda: impl.whole(f, text, rat, dels, engine),
        "text_oneline": lambda: impl.whole(f, " ".join(text_lines(inst.steps)), rat, dels, engine),
        "text_commented": lambda: impl.whole(f, commented(inst.steps), rat, dels, engine),
        "text_crlf": lambda: impl.whole(f, text.replace("\n", "\r\n"), rat, dels, engine),
        "memory": lambda: impl.whole(f, memory, rat, dels, engine),
        "memory_to_text": lambda: impl.whole(f, memory.to_text(), rat, dels, engine),
        "list": lambda: impl.whole(f, list(steps), rat, dels, engine),
        "list_with_list_lits": lambda: impl.whole(f, [(k, list(l)) for k, l in steps], rat, dels, engine),
        "tuple_of_steps": lambda: impl.whole(f, tuple(steps), rat, dels, engine),
        "generator": lambda: impl.whole(f, (s for s in steps), rat, dels, engine),
        "writer_buffered": lambda: impl.whole(f, writer(True), rat, dels, engine),
        "writer_unbuffered": lambda: impl.whole(f, writer(False), rat, dels, engine),
        "writer_path": lambda: impl.whole(f, by_path(), rat, dels, engine),
        "formula_parsed": lambda: impl.whole(
            parse_dimacs(f.to_dimacs()), text, rat, dels, engine),
    }


def _drive_stream(impl, f, rat, dels, steps):
    checker = impl.checker(f, rat, dels)
    bools = []
    for kind, lits in steps:
        accepted = checker.check_step(kind, lits)
        bools.append(accepted)
        if not accepted or (kind == "a" and not lits):
            break
    return checker, bools


def _classify(shape, fields, base, other, inst):
    for snap in (base, other):
        if "can account for at most" in snap.get("message", ""):
            return L_BOUND
    if "exception" in base or "exception" in other:
        return UNEXPLAINED
    if "failed_clause" in fields and set(fields) <= {"failed_clause", "report"}:
        a, b = base["failed_clause"], other["failed_clause"]
        if a is not None and b is not None and tuple(dict.fromkeys(b)) == a:
            return L_FAILED_CLAUSE
    used_twice = shape in ("check_step_then_check", "check_in_two_pieces",
                           "rust_check_step_then_check", "rust_check_in_two_pieces")
    if used_twice:
        refuted = "input formula is refuted"
        if other["reason"].startswith(refuted) and not base["reason"].startswith(refuted):
            return L_REENTRY
        if base["reason"].startswith(refuted):
            return L_REENTRY
        if other["failed_step"] != -1 and other["reason"].startswith("every step verified"):
            return L_REENTRY
    if shape == "check_step" and base["reason"].startswith("input formula is refuted"):
        return L_REENTRY
    return UNEXPLAINED


def run_one(inst, impl, tally, rust_jobs, tmp, combos=FLAG_COMBOS):
    counts = tally.counts
    counts["instances"] += 1
    sat = oracle.satisfiable([list(c) for c in inst.clauses])
    counts["formula_sat" if sat else "formula_unsat"] += 1
    counts[f"formula_{inst.tag}"] += 1
    fresh = any(abs(l) > inst.nvars for _, lits in inst.steps for l in lits)
    counts["proof_with_fresh_variable"] += fresh

    for rat, dels in combos:
        counts[f"flags_rat={int(rat)}_del={int(dels)}"] += 1
        f = inst.cnf()
        clauses_before = list(f.clauses)
        verdict = judge(inst, rat, dels, counts)
        tally.judged += verdict.judged
        if rat and dels and not replay_agrees(inst, verdict):
            tally.mismatch(UNEXPLAINED, "judge-vs-replay", "harness disagrees with oracle.replay", inst)

        results = {}
        results["python/text"] = base = _call(
            lambda: impl.whole(f, to_text(inst.steps), rat, dels, "python"))

        # Every shape on both engines against that one.
        for engine in ("python", "native"):
            for shape, fn in _engine_shapes(inst, f, rat, dels, engine, impl, tmp).items():
                got = _call(fn)
                name = f"{engine}/{shape}"
                results[name] = got
                counts[f"shape_{name}"] += 1
                bad = differing(base, got)
                if bad:
                    tally.mismatch(_classify(shape if engine == "python" else "native",
                                             bad, base, got, inst),
                                   name, f"{bad}: {_brief(base, bad)} vs {_brief(got, bad)}", inst)
        got = _call(lambda: impl.whole(f, to_text(inst.steps), rat, dels, "auto"))
        counts["shape_auto/text"] += 1
        bad = differing(base, got)
        if bad:
            tally.mismatch(_classify("native", bad, base, got, inst), "auto/text",
                           f"{bad}: {_brief(base, bad)} vs {_brief(got, bad)}", inst)

        # The streaming Python API.
        steps = inst.internal()
        stream = {}
        stream["check"] = _call(lambda: impl.checker(f, rat, dels).check(list(steps)))
        stream["check_generator"] = _call(lambda: impl.checker(f, rat, dels).check(s for s in steps))

        bools = None
        try:
            checker, bools = _drive_stream(impl, f, rat, dels, steps)
            stream["check_step"] = _snap(checker.result)
            stream["check_step_then_check"] = _call(lambda: checker.check([]))
        except Exception as e:  # noqa: BLE001
            stream["check_step"] = {"exception": type(e).__name__, "message": str(e)}

        def pieces():
            c = impl.checker(f, rat, dels)
            first = c.check(steps[:inst.cut])
            if first.failed_step != -1 or first.reached_empty:
                return first
            return c.check(steps[inst.cut:])
        stream["check_in_two_pieces"] = _call(pieces)

        for shape, got in stream.items():
            counts[f"shape_stream/{shape}"] += 1
            ignore = STREAM_UNSET if shape == "check_step" else frozenset()
            bad = differing(base, got, ignore)
            if bad:
                tally.mismatch(_classify(shape, bad, base, got, inst), f"stream/{shape}",
                               f"{bad}: {_brief(base, bad)} vs {_brief(got, bad)}", inst)
            results[f"stream/{shape}"] = got

        rust_jobs.append((inst, rat, dels, base, bools))

        # The end-to-end question comes first, for every shape.
        for name, got in results.items():
            if got.get("ok") is True and verdict.satisfiable:
                counts["ok_on_satisfiable"] += 1
                label = L_STALE_ROOT if verdict.stale else UNEXPLAINED
                tally.mismatch(label, f"SOUNDNESS {name}", "ok=True on a satisfiable formula", inst)

        _oracle_compare(base, verdict, inst, tally, bools)

        counts["proof_ok"] += base.get("ok") is True
        counts["proof_rejected"] += base.get("failed_step", -1) != -1
        counts["proof_truncated"] += (base.get("ok") is False and base.get("failed_step") == -1)
        counts["proof_raised"] += "exception" in base
        counts["stepped_past_empty"] += (base.get("reached_empty") is True
                                         and base.get("steps", 0) not in (0, len(steps)))

        if list(f.clauses) != clauses_before:
            tally.mismatch(UNEXPLAINED, "formula-mutated", "checking changed the CNF", inst)

    _writer_properties(inst, tally)
    if inst.index % 5 == 0:
        _misuse_probes(inst, impl, tally)


def _brief(snap, fields):
    if "exception" in snap:
        return f"{snap['exception']}({snap['message'][:70]})"
    return {k: snap.get(k) for k in fields}


#: compared with what the oracle says each field should be
ORACLE_FIELDS = ("ok", "reached_empty", "steps", "rup_steps", "rat_steps", "deletions",
                 "ignored_deletions", "resolvents_checked", "failed_step", "failed_clause")


def _oracle_compare(base, verdict, inst, tally, bools):
    if "exception" in base:
        if "can account for at most" in base["message"]:
            # A variable the bound refuses is still a clause with a verdict.
            tally.mismatch(L_BOUND, "oracle/raised", f"raised, oracle says {verdict.fields}", inst)
        else:
            tally.mismatch(UNEXPLAINED, "oracle/raised", base["message"], inst)
        return
    if verdict.stale:
        # Past a deletion of a reason, the checker keeps the old root
        # assignment, so counts need not match the definition: api-2. What it
        # accepted must still preserve satisfiability, and that is checked here.
        tally.counts["proof_past_reason_deletion"] += 1
        _stale_steps(base, inst, tally)
        return
    expected = verdict.fields
    for field in ORACLE_FIELDS:
        if field == "resolvents_checked" and expected["failed_step"] != -1:
            continue                 # stops at the first failure, in an unspecified order
        if base[field] != expected[field]:
            tally.mismatch(UNEXPLAINED, f"oracle/{field}",
                           f"got {base[field]!r}, oracle says {expected[field]!r}", inst)


def _stale_steps(base, inst, tally):
    current = [list(c) for c in inst.clauses]
    done = base["steps"] - (1 if base["failed_step"] != -1 else 0)
    for kind, lits in inst.steps[:done]:
        distinct = list(dict.fromkeys(lits))
        if kind == "d":
            if len(distinct) >= 2:
                current, _ = oracle.remove_one(current, distinct)
            continue
        tally.judged += 1
        if not oracle.preserves_sat(current, lits):
            tally.counts["step_accepted_not_preserving_sat"] += 1
            tally.mismatch(L_STALE_ROOT, "SOUNDNESS step", f"accepted {lits}, not sat-preserving", inst)
            return
        current = current + [distinct]


def _writer_properties(inst, tally):
    """What a writer wrote must parse back to the steps it was given."""
    steps = inst.internal()
    memory = to_memory(steps)
    sink = io.StringIO()
    with to_writer(steps, sink, True) as writer:
        pass
    counts = tally.counts
    counts["writer_roundtrip"] += 1
    counts["writer_crossed_its_buffer"] += len(steps) >= 4096
    if parse_proof(sink.getvalue()) != steps:
        tally.mismatch(UNEXPLAINED, "writer-roundtrip", "ProofWriter text parses differently", inst)
    if parse_proof(memory.to_text()) != steps:
        tally.mismatch(UNEXPLAINED, "to_text-roundtrip", "to_text parses differently", inst)
    if parse_proof(to_text(inst.steps)) != steps:
        tally.mismatch(UNEXPLAINED, "parse-roundtrip", "text parses differently from the list", inst)
    if (writer.n_add, writer.n_del) != (memory.n_add, memory.n_del):
        tally.mismatch(UNEXPLAINED, "writer-counts", "n_add/n_del differ", inst)
    if memory.steps != steps:
        tally.mismatch(UNEXPLAINED, "memory-steps", "MemoryProof stored other steps", inst)


def _misuse_probes(inst, impl, tally):
    """The same wrong input, through the guarded path and the unguarded one."""
    counts = tally.counts
    rng = random.Random(inst.index)
    f = inst.cnf()
    sat = oracle.satisfiable([list(c) for c in inst.clauses])
    used = max((abs(l) for c in inst.clauses for l in c), default=1)
    negative = -rng.randint(1, 2 * used + 2)
    probes = [
        ("negative_literal", [("a", (negative,)), ("a", ())]),
        ("dimacs_negative_with_other", [("a", (negative, 0)), ("a", ())]),
        ("bad_kind", [("x", (0, 2)), ("a", ())]),
        ("float_literal", [("a", (1.5,)), ("a", ())]),
        ("beyond_the_bound", [("a", (2 * (f.nvars + 40),)), ("a", ())]),
    ]
    for name, steps in probes:
        counts[f"misuse_{name}"] += 1
        memory = MemoryProof()
        memory.steps = list(steps)
        for shape, proof in (("list", list(steps)), ("memory", memory)):
            for engine in ("python", "native"):
                guarded = _call(lambda: impl.whole(f, proof, True, True, engine))
                if guarded.get("exception") != "ValueError":
                    tally.mismatch(UNEXPLAINED, f"misuse/{name}/{engine}/{shape}",
                                   f"check_proof did not refuse: {_brief(guarded, ['ok'])}", inst)
                if guarded.get("ok") is True and sat:
                    tally.mismatch(UNEXPLAINED, f"SOUNDNESS misuse/{name}", "ok=True on sat", inst)

        direct = _call(lambda: impl.checker(f, True, True).check(list(steps)))
        if direct.get("exception") != "ValueError":
            label = L_NO_VALIDATION
            counts[f"misuse_{name}_not_refused_by_check"] += 1
            if direct.get("ok") is True and sat:
                counts["misuse_ok_on_satisfiable"] += 1
                tally.mismatch(label, f"SOUNDNESS check/{name}", f"ok=True on sat: {steps}", inst)
            else:
                tally.mismatch(label, f"check/{name}",
                               f"check_proof raises ValueError, check gives {_brief(direct, ['ok'])}", inst)
        try:
            c = impl.checker(f, True, True)
            accepted = [c.check_step(k, l) for k, l in steps]
            streamed = f"bools {accepted}, reached_empty={c.result.reached_empty}"
            if all(accepted) and c.result.reached_empty and sat:
                counts["misuse_check_step_refutes_satisfiable"] += 1
                tally.mismatch(L_NO_VALIDATION, f"SOUNDNESS check_step/{name}", streamed, inst)
            else:
                tally.mismatch(L_NO_VALIDATION, f"check_step/{name}", streamed, inst)
        except ValueError:
            pass
        except Exception as e:  # noqa: BLE001
            tally.mismatch(L_NO_VALIDATION, f"check_step/{name}", type(e).__name__, inst)

    # Literals with no order have no pivot. Both engines must say the same thing.
    counts["misuse_set_literals"] += 1
    unordered = [("a", frozenset({0, 3}))]
    py = _call(lambda: impl.whole(f, unordered, True, True, "python"))
    native = _call(lambda: impl.whole(f, unordered, True, True, "native"))
    bad = differing(py, native)
    if bad:
        tally.mismatch(L_UNORDERED, "misuse/set_literals",
                       f"python {_brief(py, bad)} vs native {_brief(native, bad)}", inst)

    # A writer has no validation either; check_proof refuses the same literals.
    if negative:
        counts["misuse_writer_negative"] += 1
        memory = MemoryProof()
        memory.add((negative,))
        sink = io.StringIO()
        with ProofWriter(sink) as writer:
            writer.add((negative,))
        written = sink.getvalue()
        refused = _call(lambda: impl.whole(f, memory, True, True, "python"))
        if refused.get("exception") == "ValueError":
            tally.mismatch(L_WRITER, "writer/negative",
                           f"check_proof refuses {negative}, ProofWriter wrote {written!r}, "
                           f"to_text wrote {memory.to_text()!r}", inst)


def _missing_native_probe(tally, impl_module):
    """Every shape must explain itself the same way when native is absent."""
    if dratify.native_implementation() is not impl_module:
        return
    register_native(None)
    try:
        if dratify.native_implementation() is None:
            f = parse_dimacs("p cnf 1 1\n1 0\n")
            for proof in ("0\n", [("a", ())], MemoryProof()):
                tally.counts["native_missing_probe"] += 1
                got = _call(lambda: check_proof(f, proof, engine="native"))
                if got.get("exception") != "RuntimeError":
                    tally.mismatch(UNEXPLAINED, "native-missing", str(got),
                                   Instance(0, "native_missing", 1, [[1]], []))
    finally:
        register_native(impl_module)


def _compare_rust(impl, tally, rust_jobs, binary):
    outputs = run_rust(binary, [(i, r, d) for i, r, d, _, _ in rust_jobs])
    for (inst, rat, dels, base, bools), (rows, rust_bools) in zip(rust_jobs, outputs):
        rows = impl.rust_row(rows)
        for shape, got in rows.items():
            tally.counts[f"shape_{shape}"] += 1
            if "exception" in base:
                # check_proof refused before any checker ran; the crate has no such bound.
                tally.counts["rust_compared_against_a_raise"] += 1
                continue
            compared = {k: base[k] for k in got}
            bad = differing(compared, got)
            if bad:
                tally.mismatch(_classify(shape, bad, compared, got, inst), shape,
                               f"{bad}: {_brief(compared, bad)} vs {_brief(got, bad)}", inst)
        tally.counts["shape_rust_check_step"] += 1
        if bools is not None:
            py = "".join("1" if b else "0" for b in bools)
            if py != rust_bools:
                tally.mismatch(UNEXPLAINED, "rust_check_step",
                               f"bools python {py} rust {rust_bools}", inst)


REQUIRED = [
    "formula_sat", "formula_unsat", "formula_refuted_by_propagation", "proof_ok",
    "proof_rejected", "proof_truncated", "stepped_past_empty", "step_rup", "step_rat_only",
    "step_rejected", "step_with_repeated_literal", "rejected_step_with_repeated_literal",
    "del_applied", "del_of_a_reason", "del_ignored_unit", "del_ignored_absent",
    "del_ignored_empty", "del_with_deletions_off", "proof_with_fresh_variable",
    "formula_stale_root_attack", "formula_bound_gap", "writer_crossed_its_buffer",
    "writer_roundtrip",
    "misuse_negative_literal", "misuse_bad_kind", "misuse_float_literal",
    "misuse_beyond_the_bound", "misuse_writer_negative", "misuse_set_literals",
    "native_missing_probe",
    *[f"flags_rat={int(r)}_del={int(d)}" for r, d in FLAG_COMBOS],
    *[f"shape_{e}/{s}" for e in ("python", "native") for s in ENGINE_SHAPES],
    "shape_auto/text",
    *[f"shape_stream/{s}" for s in STREAM_SHAPES],
    *[f"shape_{s}" for s in RUST_SHAPES],
]


def native_module():
    import cdclkit_native
    register_native(cdclkit_native)
    return cdclkit_native


def run(seed, instances, impl, binary, tmp, combos=FLAG_COMBOS) -> Tally:
    rng = random.Random(seed)
    tally = Tally()
    rust_jobs = []
    run_one(writer_flush_instance(0), impl, tally, rust_jobs, tmp, combos[:1])
    for index in range(1, instances + 1):
        run_one(make_instance(rng, index), impl, tally, rust_jobs, tmp, combos)
    if binary is not None:
        _compare_rust(impl, tally, rust_jobs, binary)
    return tally


# --------------------------------------------------------------------------
# self-test: the harness must flag checkers that are wrong in each way
# --------------------------------------------------------------------------


def _stub_result(ok, failed=False):
    r = CheckResult()
    r.ok = ok
    r.reached_empty = ok
    r.reason = "stub"
    if failed:
        r.failed_step = 1
        r.failed_clause = ()
    return r


class AcceptsEverything(Real):
    name = "accepts everything"

    def whole(self, formula, proof, check_rat, apply_deletions, engine):
        return _stub_result(True)

    def checker(self, formula, check_rat, apply_deletions):
        return types.SimpleNamespace(check=lambda steps: _stub_result(True),
                                     check_step=lambda k, l: True,
                                     result=_stub_result(True))


class RejectsEverything(Real):
    name = "rejects everything"

    def whole(self, formula, proof, check_rat, apply_deletions, engine):
        return _stub_result(False, failed=True)

    def checker(self, formula, check_rat, apply_deletions):
        return types.SimpleNamespace(check=lambda steps: _stub_result(False, failed=True),
                                     check_step=lambda k, l: False,
                                     result=_stub_result(False, failed=True))


class MemoryProofOffByOne(Real):
    name = "MemoryProof path miscounts one field"

    def whole(self, formula, proof, check_rat, apply_deletions, engine):
        r = super().whole(formula, proof, check_rat, apply_deletions, engine)
        if isinstance(proof, MemoryProof):
            r.rup_steps += 1
        return r


class NativeLiesAboutDeletions(Real):
    name = "native engine miscounts deletions"

    def whole(self, formula, proof, check_rat, apply_deletions, engine):
        r = super().whole(formula, proof, check_rat, apply_deletions, engine)
        if engine == "native":
            r.deletions += 1
        return r


class SwapsRupAndRat(Real):
    name = "every shape agrees, and all of them call RUP steps RAT"

    def whole(self, formula, proof, check_rat, apply_deletions, engine):
        r = super().whole(formula, proof, check_rat, apply_deletions, engine)
        r.rup_steps, r.rat_steps = r.rat_steps, r.rup_steps
        return r

    def checker(self, formula, check_rat, apply_deletions):
        inner = super().checker(formula, check_rat, apply_deletions)
        original = inner.check

        def check(steps):
            r = original(steps)
            r.rup_steps, r.rat_steps = r.rat_steps, r.rup_steps
            return r
        inner.check = check
        return inner


class StreamAcceptsEverything(Real):
    name = "check_step returns True for every step"

    def checker(self, formula, check_rat, apply_deletions):
        inner = super().checker(formula, check_rat, apply_deletions)
        original = inner.check_step

        def check_step(kind, lits):
            original(kind, lits)
            return True
        inner.check_step = check_step
        return inner


class RustDrifts(Real):
    name = "the Rust crate miscounts one field"

    def rust_row(self, row):
        row = {k: dict(v) for k, v in row.items()}
        row["rust_check"]["steps"] += 1
        return row


class WrongDeletionRule(Real):
    name = "ignores every deletion, on every shape"

    def whole(self, formula, proof, check_rat, apply_deletions, engine):
        return super().whole(formula, proof, check_rat, False, engine)

    def checker(self, formula, check_rat, apply_deletions):
        return super().checker(formula, check_rat, False)


STUBS = (AcceptsEverything, RejectsEverything, MemoryProofOffByOne, NativeLiesAboutDeletions,
         SwapsRupAndRat, StreamAcceptsEverything, RustDrifts, WrongDeletionRule)


def self_test(seed, binary, tmp) -> int:
    failed = 0
    for stub in STUBS:
        tally = run(seed, 60, stub(), binary, tmp, FLAG_COMBOS[:2])
        flagged = tally.unexplained()
        print(f"  {stub.name}: {flagged} unexplained mismatches"
              f"{'' if flagged else '   NOT FLAGGED'}")
        failed += not flagged
    print("self-test:", "FAILED" if failed else f"all {len(STUBS)} wrong checkers were flagged")
    return 1 if failed else 0


# --------------------------------------------------------------------------


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--seed", type=int, default=DEFAULT_SEED)
    ap.add_argument("--instances", type=int, default=DEFAULT_INSTANCES)
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--no-write", action="store_true", help="do not write results/api.json")
    ap.add_argument("--examples", type=int, default=30, help="mismatch examples to print")
    args = ap.parse_args(argv)

    module = native_module()
    start = time.time()
    with tempfile.TemporaryDirectory(prefix="gen_api") as d:
        tmp = pathlib.Path(d)
        binary = build_rust(tmp)
        if binary is None:
            print("rustc not on PATH: the Rust streaming API cannot be reached", file=sys.stderr)
        if args.self_test:
            return self_test(args.seed, binary, tmp)
        tally = run(args.seed, args.instances, Real(), binary, tmp)
    _missing_native_probe(tally, module)
    runtime = time.time() - start

    missing = [c for c in REQUIRED if not tally.counts[c]]
    print(f"seed {args.seed}, {tally.counts['instances']} instances, "
          f"{tally.judged} steps judged by the oracle, {runtime:.1f}s")
    for key in sorted(tally.counts):
        print(f"  {key}: {tally.counts[key]}")
    print("mismatches by label:", dict(tally.mismatches) or "none")
    for key, example in sorted(tally.examples.items())[:args.examples]:
        print(f"  [{key}] {example}")
    if missing:
        print("CATEGORIES NEVER REACHED:", missing)

    if not args.no_write:
        labels = {f["id"]: tally.mismatches[f["id"]] for f in FINDINGS}
        RESULTS.parent.mkdir(exist_ok=True)
        RESULTS.write_text(json.dumps({
            "corner": "api",
            "seeds": [args.seed],
            "instances": tally.counts["instances"],
            "steps": tally.judged,
            "per_category_counts": dict(sorted(tally.counts.items())),
            "mismatches_by_label": {**labels, UNEXPLAINED: tally.unexplained()},
            "runtime_seconds": round(runtime, 1),
            "findings": FINDINGS,
            "not_checked": NOT_CHECKED,
        }, indent=2) + "\n")

    if missing:
        return 2
    return 1 if sum(tally.mismatches.values()) else 0


NOT_CHECKED = [
    "cdclkit's own use of these APIs, and any proof a real solver wrote: proofs here "
    "are generated, tiny, and judged by the oracle",
    "a Python binding for Rust Checker::check_step: none exists, so the crate is "
    "compiled and driven directly from a Rust driver embedded in this file",
    "huge literals on the unguarded paths: DRATChecker and Rust Checker size their "
    "arrays for whatever literal they get, and Rust's docs say so. Only 40 variables "
    "past the formula were run, so the allocation itself was read, not exercised",
    "a ProofWriter closed late or never: only properly closed writers are compared",
    "re-using a checker after a rejected step beyond one more check([]) and two pieces",
    "the text grammar itself (parsing corner), and deletion semantics past the first "
    "deleted reason: there only ok=True on a satisfiable formula and sat-preservation "
    "of accepted steps are judged, not exact counts",
]


if __name__ == "__main__":
    sys.exit(main())
