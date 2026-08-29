# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""DRAT proof emission and an independent DRAT proof checker.

Why this file exists
--------------------
A SAT solver that answers SAT hands you a model, and a model is checkable in
linear time by anyone.  A solver that answers UNSAT hands you nothing -- and
UNSAT is exactly the answer people build safety arguments on.  The community's
answer is the **DRAT** proof format: the solver logs every clause it learns and
every clause it deletes, and a separate program replays the log and certifies
that the empty clause really follows.

This module implements both halves, and the checker deliberately shares *no*
code with the solver: it has its own propagation engine, its own clause store
and its own watch scheme.  A checker built out of the solver's own machinery
would certify the solver's bugs along with its results.

The two inference rules
-----------------------
**RUP** (reverse unit propagation).  A clause ``C = l1 v ... v lk`` is RUP with
respect to a formula ``F`` when assigning every ``li`` false and running unit
propagation on ``F`` yields a conflict.  That is precisely the statement that
``F`` entails ``C`` by a resolution derivation the checker can rediscover in
linear time.  Every clause a CDCL solver learns is RUP by construction: the
first-UIP clause is a resolvent chain over the trail.

**RAT** (resolution asymmetric tautology), the strictly stronger rule that puts
the "A" in DRAT.  ``C`` is RAT on pivot literal ``p in C`` w.r.t. ``F`` when for
every clause ``D`` of ``F`` containing ``~p``, the resolvent
``C u (D \\ {~p})`` is RUP.  RAT clauses need not be entailed by ``F`` -- they
only preserve satisfiability -- which is what lets a proof justify
*inprocessing* steps such as blocked-clause addition and bounded variable
elimination that add clauses no resolution proof would produce directly.

Both rules are checked here.  RUP is tried first because it succeeds for the
overwhelming majority of lines and costs one propagation.

Deletion
--------
Deletion lines are honoured, with the one universally adopted exception:
**deletions of unit clauses are ignored**.  A unit that has already been
propagated into the checker's root assignment cannot be cleanly retracted
without a full restart of propagation, and every mainstream checker
(drat-trim included) skips them.  Ignoring a deletion is always sound for an
UNSAT certificate -- it only leaves the checker with *more* clauses than the
solver had, which can never turn an invalid step into a valid one... with the
caveat that it also cannot turn a valid one invalid, since RUP is monotone in
the formula.  Monotonicity is what makes ignoring deletions safe; RAT is *not*
monotone, so a RAT step is checked against exactly the clauses present.

Formats
-------
Text DRAT, one clause per line, DIMACS literals terminated by ``0``, deletions
prefixed by ``d``::

    -1 2 0
    d 1 -2 3 0
    0

The trailing ``0`` on its own is the empty clause: the end of the proof.
"""

from __future__ import annotations

import io
import os
from typing import Iterable, Sequence

from .cnf import CNF
from .lits import F, T, U, from_dimacs, to_dimacs

__all__ = [
    "ProofWriter",
    "NullProof",
    "MemoryProof",
    "DRATChecker",
    "CheckResult",
    "parse_proof",
    "check_proof",
]


# --------------------------------------------------------------------------
# emission
# --------------------------------------------------------------------------


class NullProof:
    """A proof sink that discards everything (the default in the solver)."""

    __slots__ = ()

    def add(self, lits: Iterable[int]) -> None:  # pragma: no cover - trivial
        pass

    def delete(self, lits: Iterable[int]) -> None:  # pragma: no cover - trivial
        pass

    def close(self) -> None:  # pragma: no cover - trivial
        pass


class ProofWriter:
    """Writes a text DRAT proof to a file or stream.

    Literals arrive in internal encoding and are converted to DIMACS on the
    way out, which is the only place in the solver where that conversion
    happens during solving.
    """

    __slots__ = ("out", "_own", "n_add", "n_del", "buffered", "_buf")

    def __init__(self, target, buffered: bool = True) -> None:
        if isinstance(target, (str, os.PathLike)):
            self.out = open(target, "w", encoding="ascii")
            self._own = True
        else:
            self.out = target
            self._own = False
        self.n_add = 0
        self.n_del = 0
        self.buffered = buffered
        self._buf: list[str] = []

    def _emit(self, s: str) -> None:
        if self.buffered:
            self._buf.append(s)
            if len(self._buf) >= 4096:
                self.out.write("".join(self._buf))
                self._buf.clear()
        else:
            self.out.write(s)

    def add(self, lits: Iterable[int]) -> None:
        self.n_add += 1
        self._emit(" ".join(str(to_dimacs(l)) for l in lits) + (" 0\n" if lits else "0\n"))

    def delete(self, lits: Iterable[int]) -> None:
        self.n_del += 1
        self._emit("d " + " ".join(str(to_dimacs(l)) for l in lits) + " 0\n")

    def flush(self) -> None:
        if self._buf:
            self.out.write("".join(self._buf))
            self._buf.clear()
        try:
            self.out.flush()
        except Exception:  # pragma: no cover - stream without flush
            pass

    def close(self) -> None:
        self.flush()
        if self._own:
            self.out.close()

    def __enter__(self) -> "ProofWriter":
        return self

    def __exit__(self, *exc) -> None:
        self.close()


class MemoryProof:
    """Collects proof steps in memory as ``('a'|'d', tuple_of_internal_lits)``.

    Used by the test suite so a solve/check round trip needs no filesystem.
    """

    __slots__ = ("steps",)

    def __init__(self) -> None:
        self.steps: list[tuple[str, tuple[int, ...]]] = []

    def add(self, lits: Iterable[int]) -> None:
        self.steps.append(("a", tuple(lits)))

    def delete(self, lits: Iterable[int]) -> None:
        self.steps.append(("d", tuple(lits)))

    def close(self) -> None:
        pass

    def to_text(self) -> str:
        out = io.StringIO()
        for kind, lits in self.steps:
            if kind == "d":
                out.write("d ")
            out.write(" ".join(str(to_dimacs(l)) for l in lits))
            out.write(" 0\n" if lits else "0\n")
        return out.getvalue()

    @property
    def n_add(self) -> int:
        return sum(1 for k, _ in self.steps if k == "a")

    @property
    def n_del(self) -> int:
        return sum(1 for k, _ in self.steps if k == "d")


def parse_proof(text: str) -> list[tuple[str, tuple[int, ...]]]:
    """Parse a text DRAT proof into internal-literal steps."""
    steps: list[tuple[str, tuple[int, ...]]] = []
    for raw in text.splitlines():
        line = raw.strip()
        if not line or line[0] == "c":
            continue
        kind = "a"
        if line[0] == "d":
            kind = "d"
            line = line[1:].strip()
        lits: list[int] = []
        terminated = False
        for tok in line.split():
            d = int(tok)
            if d == 0:
                terminated = True
                break
            lits.append(from_dimacs(d))
        if not terminated and lits:
            raise ValueError(f"unterminated proof line: {raw!r}")
        steps.append((kind, tuple(lits)))
    return steps


# --------------------------------------------------------------------------
# the checker's own propagation engine
# --------------------------------------------------------------------------


class _Prop:
    """A minimal two-watched-literal propagator, independent of the solver.

    Kept deliberately small and dumb: no heuristics, no learning, no clause
    deletion during propagation.  Correctness here is worth more than speed,
    because everything else in this project is checked against it.
    """

    __slots__ = ("nvars", "val", "trail", "watches", "units", "clauses")

    def __init__(self, nvars: int) -> None:
        self.nvars = nvars
        self.val = bytearray(2 * nvars)
        self.trail: list[int] = []
        self.watches: list[list] = [[] for _ in range(2 * nvars)]
        self.units: list[int] = []
        self.clauses: list[list[int] | None] = []

    def grow(self, nvars: int) -> None:
        while self.nvars < nvars:
            self.nvars += 1
            self.val.extend((U, U))
            self.watches.append([])
            self.watches.append([])

    # -- clause store -------------------------------------------------------

    def attach(self, lits: list[int]) -> int:
        """Register a clause; returns its handle (index)."""
        h = len(self.clauses)
        self.clauses.append(lits)
        if len(lits) >= 2:
            self.watches[lits[0] ^ 1].append(h)
            self.watches[lits[1] ^ 1].append(h)
        elif len(lits) == 1:
            self.units.append(lits[0])
        return h

    def detach(self, h: int) -> None:
        lits = self.clauses[h]
        if lits is None:
            return
        if len(lits) >= 2:
            for a in (lits[0], lits[1]):
                ws = self.watches[a ^ 1]
                try:
                    ws.remove(h)
                except ValueError:
                    pass
        self.clauses[h] = None

    # -- assignment ---------------------------------------------------------

    def assign(self, lit: int) -> bool:
        """Set ``lit`` true.  Returns False if that contradicts the trail."""
        v = self.val[lit]
        if v == T:
            return True
        if v == F:
            return False
        self.val[lit] = T
        self.val[lit ^ 1] = F
        self.trail.append(lit)
        return True

    def backtrack(self, size: int) -> None:
        trail = self.trail
        val = self.val
        for i in range(len(trail) - 1, size - 1, -1):
            lit = trail[i]
            val[lit] = U
            val[lit ^ 1] = U
        del trail[size:]

    def propagate(self, qhead: int) -> bool:
        """Propagate from ``qhead``; True means a conflict was found."""
        val = self.val
        watches = self.watches
        trail = self.trail
        clauses = self.clauses
        while qhead < len(trail):
            p = trail[qhead]
            qhead += 1
            false_lit = p ^ 1
            ws = watches[p]
            i = j = 0
            n = len(ws)
            conflict = False
            while i < n:
                h = ws[i]
                lits = clauses[h]
                if lits is None:  # detached during this pass
                    i += 1
                    continue
                if lits[0] == false_lit:
                    lits[0] = lits[1]
                    lits[1] = false_lit
                first = lits[0]
                if val[first] == T:
                    ws[j] = h
                    i += 1
                    j += 1
                    continue
                found = False
                for k in range(2, len(lits)):
                    lk = lits[k]
                    if val[lk] != F:
                        lits[1] = lk
                        lits[k] = false_lit
                        watches[lk ^ 1].append(h)
                        found = True
                        break
                if found:
                    i += 1
                    continue
                ws[j] = h
                i += 1
                j += 1
                if val[first] == F:
                    conflict = True
                    while i < n:
                        ws[j] = ws[i]
                        i += 1
                        j += 1
                    break
                self.assign(first)
            del ws[j:]
            if conflict:
                return True
        return False


# --------------------------------------------------------------------------
# checker
# --------------------------------------------------------------------------


class CheckResult:
    """Outcome of a proof check."""

    __slots__ = (
        "ok",
        "reason",
        "steps",
        "rup_steps",
        "rat_steps",
        "deletions",
        "ignored_deletions",
        "resolvents_checked",
        "failed_step",
        "failed_clause",
        "reached_empty",
    )

    def __init__(self) -> None:
        self.ok = False
        self.reason = ""
        self.steps = 0
        self.rup_steps = 0
        self.rat_steps = 0
        self.deletions = 0
        self.ignored_deletions = 0
        self.resolvents_checked = 0
        self.failed_step = -1
        self.failed_clause: tuple[int, ...] | None = None
        self.reached_empty = False

    def __bool__(self) -> bool:
        return self.ok

    def __repr__(self) -> str:
        verdict = "VERIFIED" if self.ok else "REJECTED"
        return f"<CheckResult {verdict}: {self.reason}>"

    def report(self) -> str:
        head = "s VERIFIED" if self.ok else "s NOT VERIFIED"
        lines = [
            head,
            f"c {self.reason}",
            f"c proof steps checked : {self.steps}",
            f"c   by RUP            : {self.rup_steps}",
            f"c   by RAT            : {self.rat_steps} "
            f"({self.resolvents_checked} resolvents checked)",
            f"c deletions applied   : {self.deletions} "
            f"({self.ignored_deletions} unit deletions ignored)",
        ]
        if not self.ok and self.failed_clause is not None:
            body = " ".join(str(to_dimacs(l)) for l in self.failed_clause)
            lines.append(f"c first bad step {self.failed_step}: {body} 0")
        return "\n".join(lines)


class DRATChecker:
    """Forward DRAT checker.

    Forward means the proof is replayed in order and every addition is verified
    against the clauses present at that moment.  Backward checking (drat-trim's
    default) is faster on huge proofs because it skips lines that never
    contribute to the empty clause, but forward checking is what you want for a
    *self*-check: it verifies every step the solver actually took, including
    the ones that turned out to be useless, so a bug in a rarely-exercised
    inference cannot hide behind trimming.
    """

    def __init__(self, formula: CNF, check_rat: bool = True, apply_deletions: bool = True):
        self.formula = formula
        self.check_rat = check_rat
        self.apply_deletions = apply_deletions
        self.prop = _Prop(formula.nvars)
        # clause key -> list of live handles, for deletion lookup
        self._index: dict[tuple[int, ...], list[int]] = {}
        self._occ: list[list[int]] = [[] for _ in range(2 * formula.nvars)]
        self.result = CheckResult()
        self._root_conflict = False
        for c in formula.clauses:
            if not c:
                # the input already contains the empty clause: nothing to prove
                self._root_conflict = True
            self._insert(list(c))
        self._root_conflict = self._root_conflict or self._propagate_root()

    # -- clause bookkeeping -------------------------------------------------

    @staticmethod
    def _key(lits: Sequence[int]) -> tuple[int, ...]:
        return tuple(sorted(set(lits)))

    def _grow(self, lits: Sequence[int]) -> None:
        need = max((l >> 1) + 1 for l in lits) if lits else 0
        if need > self.prop.nvars:
            self.prop.grow(need)
            while len(self._occ) < 2 * self.prop.nvars:
                self._occ.append([])

    def _insert(self, lits: list[int]) -> int:
        self._grow(lits)
        h = self.prop.attach(lits)
        self._index.setdefault(self._key(lits), []).append(h)
        for l in lits:
            self._occ[l].append(h)
        return h

    def _erase(self, lits: Sequence[int]) -> bool:
        handles = self._index.get(self._key(lits))
        if not handles:
            return False
        h = handles.pop()
        stored = self.prop.clauses[h]
        self.prop.detach(h)
        if stored is not None:
            for l in stored:
                try:
                    self._occ[l].remove(h)
                except ValueError:
                    pass
        return True

    # -- propagation helpers ------------------------------------------------

    def _propagate_root(self) -> bool:
        """Propagate all unit clauses into the persistent trail."""
        for u in self.prop.units:
            if not self.prop.assign(u):
                return True
        return self.prop.propagate(0)

    def _is_rup(self, lits: Sequence[int]) -> bool:
        """True when negating ``lits`` and propagating yields a conflict."""
        if self._root_conflict:
            return True
        prop = self.prop
        mark = len(prop.trail)
        conflict = False
        for l in lits:
            if prop.val[l] == T:
                # the clause is already satisfied at root: its negation is
                # immediately inconsistent, so RUP holds trivially
                conflict = True
                break
            if not prop.assign(l ^ 1):
                conflict = True
                break
        if not conflict:
            conflict = prop.propagate(mark)
        prop.backtrack(mark)
        return conflict

    def _is_rat(self, lits: Sequence[int]) -> bool:
        """RAT on the first literal, the pivot convention DRAT mandates."""
        if not lits:
            return False
        pivot = lits[0]
        neg = pivot ^ 1
        if neg >= len(self._occ):
            return True  # no clause contains ~pivot: vacuously RAT
        clause_set = set(lits)
        for h in list(self._occ[neg]):
            d = self.prop.clauses[h]
            if d is None:
                continue
            resolvent = list(lits)
            tautology = False
            for l in d:
                if l == neg:
                    continue
                if (l ^ 1) in clause_set:
                    tautology = True
                    break
                if l not in clause_set:
                    resolvent.append(l)
            if tautology:
                continue
            self.result.resolvents_checked += 1
            if not self._is_rup(resolvent):
                return False
        return True

    # -- driver -------------------------------------------------------------

    def check_step(self, kind: str, lits: Sequence[int]) -> bool:
        r = self.result
        r.steps += 1
        # A proof may introduce variables the formula never mentions -- that is
        # exactly what an extended-resolution / definition-introduction step
        # does -- so the propagator has to grow before the literal is touched.
        if lits:
            self._grow(lits)
        if kind == "d":
            if len(lits) <= 1:
                r.ignored_deletions += 1
                return True
            if self.apply_deletions:
                if self._erase(lits):
                    r.deletions += 1
                else:
                    r.ignored_deletions += 1
            return True
        # addition
        if self._is_rup(lits):
            r.rup_steps += 1
        elif self.check_rat and self._is_rat(lits):
            r.rat_steps += 1
        else:
            r.failed_step = r.steps
            r.failed_clause = tuple(lits)
            r.reason = (
                "clause is neither RUP nor RAT with respect to the "
                "clauses available at this point"
                if self.check_rat
                else "clause is not RUP (RAT checking disabled)"
            )
            return False
        if not lits:
            r.reached_empty = True
            return True
        self._insert(list(lits))
        if len(lits) == 1:
            if not self.prop.assign(lits[0]):
                self._root_conflict = True
            elif self.prop.propagate(len(self.prop.trail) - 1):
                self._root_conflict = True
        return True

    def check(self, steps: Iterable[tuple[str, Sequence[int]]]) -> CheckResult:
        r = self.result
        if self._root_conflict:
            r.ok = True
            r.reached_empty = True
            r.reason = "input formula is refuted by unit propagation alone"
            return r
        for kind, lits in steps:
            if not self.check_step(kind, lits):
                r.ok = False
                return r
            if r.reached_empty:
                break
        if r.reached_empty:
            r.ok = True
            r.reason = "empty clause derived and every step verified"
        else:
            r.ok = False
            r.reason = (
                "every step verified, but the proof never derives the empty clause"
            )
        return r


def check_proof(
    formula: CNF,
    proof,
    check_rat: bool = True,
    apply_deletions: bool = True,
    engine: str = "auto",
) -> CheckResult:
    """Check ``proof`` against ``formula``.

    ``proof`` may be a :class:`MemoryProof`, a list of steps, or proof text.

    ``engine`` selects the implementation: ``"native"`` (Rust), ``"python"``,
    or ``"auto"`` -- native when the module is built, Python otherwise.

    The Python checker is **not** obsolete and is not going anywhere. It is the
    independent implementation that makes agreement meaningful: a checker
    exists to disagree with a buggy solver, so having only one -- written by
    the same author, against the same mental model as the solver -- is exactly
    the situation to distrust. The test suite runs both over every proof,
    including the corrupted ones, and requires identical verdicts.
    """
    if isinstance(proof, MemoryProof):
        steps: Iterable = proof.steps
    elif isinstance(proof, str):
        steps = parse_proof(proof)
    else:
        steps = proof
    steps = list(steps)

    if engine not in ("auto", "native", "python"):
        raise ValueError(f"unknown checker engine {engine!r}")
    if engine in ("auto", "native"):
        native = _native_check(formula, steps, check_rat, apply_deletions)
        if native is not None:
            return native
        if engine == "native":
            from . import _nativeinfo as _n

            raise RuntimeError(_n.BUILD_HINT)

    return DRATChecker(formula, check_rat=check_rat, apply_deletions=apply_deletions).check(
        steps
    )


#: A native checker registered by another package, or None.
#:
#: `dratify` does not ship Python bindings for its Rust checker yet. Something
#: that already has them -- `cdclkit`, which embeds the same crate -- can hand
#: one over rather than letting `engine="auto"` fall back to the pure-Python
#: checker, which is ~18x slower on large proofs.
#:
#: The registered module must expose `check_proof` with the same signature as
#: the built-in native path below.
_registered_native = None


def register_native(module) -> None:
    """Offer a native checker implementation to `check_proof`.

    Call with a module exposing `check_proof`, or with None to unregister.
    `dratify_native` is preferred when it is installed; this is the seam for
    everyone else.
    """
    global _registered_native
    if module is not None and not hasattr(module, "check_proof"):
        raise TypeError("a native checker module must expose check_proof")
    _registered_native = module


def _native_module():
    try:
        import dratify_native
        if hasattr(dratify_native, "check_proof"):
            return dratify_native
    except ImportError:
        pass
    return _registered_native


def _native_check(formula: CNF, steps, check_rat: bool, apply_deletions: bool):
    """Run the native checker, or return None when it is unavailable."""
    sable_native = _native_module()
    if sable_native is None:
        return None

    packed = [(kind == "d", list(lits)) for kind, lits in steps]
    (ok, reason, nsteps, rup, rat, dels, ignored, resolvents, failed_step,
     reached_empty) = sable_native.check_proof(
        formula.nvars, [list(c) for c in formula.clauses], packed,
        check_rat, apply_deletions)

    r = CheckResult()
    r.ok = ok
    r.reason = reason
    r.steps = nsteps
    r.rup_steps = rup
    r.rat_steps = rat
    r.deletions = dels
    r.ignored_deletions = ignored
    r.resolvents_checked = resolvents
    r.failed_step = failed_step
    r.reached_empty = reached_empty
    if failed_step > 0 and failed_step <= len(steps):
        r.failed_clause = tuple(steps[failed_step - 1][1])
    return r
