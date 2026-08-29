# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Clause and formula containers, plus DIMACS CNF input/output.

Two distinct objects live here and they are deliberately different:

``Clause``
    The solver's runtime clause.  Mutable, carries the two watched literals in
    slots 0 and 1, and holds the learnt-clause bookkeeping (LBD, activity,
    deletion mark).  Never used for storage or I/O.

``CNF``
    An immutable-ish *formula*: a variable count plus a list of clauses, each a
    tuple of internal literals.  This is what the parser produces, what the
    encoders build, what the proof checker consumes and what the brute-force
    reference solver evaluates.  It has no solver state at all.

Keeping them apart means the encoders and the checker can be tested without
instantiating a solver, and the solver never has to worry about I/O concerns
such as tautology filtering or duplicate literals -- ``CNF.add`` normalises on
the way in.
"""

from __future__ import annotations

import io
from typing import Iterable, Iterator, Sequence

from .lits import from_dimacs, to_dimacs

__all__ = ["Clause", "CNF", "parse_dimacs", "parse_dimacs_file", "write_dimacs"]


# --------------------------------------------------------------------------
# runtime clause
# --------------------------------------------------------------------------


class Clause:
    """A runtime clause with two watched literals in ``lits[0]`` and ``lits[1]``.

    Invariant maintained by the solver: if the clause is not satisfied at a
    lower level, ``lits[0]`` and ``lits[1]`` are either unassigned or assigned
    true, or the clause is conflicting / unit.  See
    :meth:`sable.solver.Solver._propagate` for the exact restoration logic.
    """

    __slots__ = ("lits", "learnt", "lbd", "act", "deleted", "seen")

    def __init__(self, lits: Sequence[int], learnt: bool = False, lbd: int = 0) -> None:
        self.lits: list[int] = list(lits)
        self.learnt = learnt
        self.lbd = lbd
        self.act = 0.0
        self.deleted = False
        self.seen = False  # scratch flag for subsumption / DB reduction

    def __len__(self) -> int:
        return len(self.lits)

    def __iter__(self) -> Iterator[int]:
        return iter(self.lits)

    def __getitem__(self, i: int) -> int:
        return self.lits[i]

    def __setitem__(self, i: int, v: int) -> None:
        self.lits[i] = v

    def __repr__(self) -> str:  # pragma: no cover - debugging aid
        kind = "learnt" if self.learnt else "orig"
        body = " ".join(str(to_dimacs(l)) for l in self.lits)
        return f"<Clause {kind} lbd={self.lbd} [{body}]>"


# --------------------------------------------------------------------------
# formula
# --------------------------------------------------------------------------


class CNF:
    """A CNF formula over variables ``0 .. nvars-1``.

    ``add`` performs three normalisations, all of them satisfiability
    preserving and all of them required by the rest of the toolkit:

    * duplicate literals are collapsed (``x v x = x``);
    * tautologies (``x v ~x``) are dropped entirely;
    * the variable count grows to cover every literal seen.

    The empty clause is kept: it is the canonical certificate of
    unsatisfiability and both the checker and the solver rely on being able to
    represent it.
    """

    __slots__ = ("nvars", "clauses", "comments", "_names", "header_mismatch")

    def __init__(self, nvars: int = 0) -> None:
        self.nvars = nvars
        self.clauses: list[tuple[int, ...]] = []
        self.comments: list[str] = []
        #: (declared_clauses, parsed_clauses) when a `p cnf` header disagreed
        #: with what was actually read, else None.
        #:
        #: Tolerating a stray `%` line or a missing final `0` is being liberal
        #: in what you accept. A clause count that disagrees with the header is
        #: not that -- it means the formula in memory is not the formula in the
        #: file. SATLIB's `dubois100.cnf` declares 800 clauses and parses to
        #: 396 here, which flipped it from unsatisfiable to satisfiable, and
        #: the benchmark compared two solvers on it for weeks without noticing
        #: because both were fed the *re-serialised* formula and so agreed.
        self.header_mismatch: tuple[int, int] | None = None
        self._names: dict[int, str] = {}

    # -- construction -------------------------------------------------------

    def new_var(self, name: str | None = None) -> int:
        """Allocate a fresh variable and return its 0-based index."""
        v = self.nvars
        self.nvars += 1
        if name is not None:
            self._names[v] = name
        return v

    def new_vars(self, n: int) -> list[int]:
        return [self.new_var() for _ in range(n)]

    def name(self, v: int) -> str:
        return self._names.get(v, f"x{v}")

    def set_name(self, v: int, name: str) -> None:
        self._names[v] = name

    def add(self, lits: Iterable[int]) -> bool:
        """Add a clause of internal literals.  Returns False if it was a tautology."""
        seen: set[int] = set()
        out: list[int] = []
        for l in lits:
            if l < 0:
                raise ValueError(
                    f"internal literals are non-negative; got {l} "
                    "(use lits.from_dimacs for signed input)"
                )
            if l in seen:
                continue
            if (l ^ 1) in seen:
                return False  # tautology
            seen.add(l)
            out.append(l)
            v = l >> 1
            if v >= self.nvars:
                self.nvars = v + 1
        self.clauses.append(tuple(out))
        return True

    def add_dimacs(self, dimacs_lits: Iterable[int]) -> bool:
        """Add a clause given as signed 1-based DIMACS literals."""
        return self.add(from_dimacs(d) for d in dimacs_lits)

    def extend(self, clauses: Iterable[Iterable[int]]) -> None:
        for c in clauses:
            self.add(c)

    # -- queries ------------------------------------------------------------

    @property
    def nclauses(self) -> int:
        return len(self.clauses)

    def __len__(self) -> int:
        return len(self.clauses)

    def __iter__(self):
        return iter(self.clauses)

    def literals(self) -> Iterator[int]:
        for c in self.clauses:
            yield from c

    def occurrence_counts(self) -> list[int]:
        counts = [0] * (2 * self.nvars)
        for c in self.clauses:
            for l in c:
                counts[l] += 1
        return counts

    def stats(self) -> dict[str, int | float]:
        sizes = [len(c) for c in self.clauses]
        total = sum(sizes)
        return {
            "vars": self.nvars,
            "clauses": len(self.clauses),
            "literals": total,
            "max_len": max(sizes) if sizes else 0,
            "min_len": min(sizes) if sizes else 0,
            "avg_len": (total / len(sizes)) if sizes else 0.0,
            "unit": sum(1 for s in sizes if s == 1),
            "binary": sum(1 for s in sizes if s == 2),
            "ternary": sum(1 for s in sizes if s == 3),
        }

    # -- evaluation ---------------------------------------------------------

    def is_satisfied_by(self, model: Sequence[bool]) -> bool:
        """True iff every clause has a true literal under ``model``."""
        for c in self.clauses:
            for l in c:
                v = l >> 1
                if v < len(model) and (model[v] != bool(l & 1)):
                    break
            else:
                return False
        return True

    def falsified_clauses(self, model: Sequence[bool]) -> list[tuple[int, ...]]:
        """All clauses with no true literal (used for error messages)."""
        bad = []
        for c in self.clauses:
            for l in c:
                v = l >> 1
                if v < len(model) and (model[v] != bool(l & 1)):
                    break
            else:
                bad.append(c)
        return bad

    def copy(self) -> "CNF":
        f = CNF(self.nvars)
        f.clauses = list(self.clauses)
        f.comments = list(self.comments)
        f._names = dict(self._names)
        return f

    # -- serialisation ------------------------------------------------------

    def to_dimacs(self) -> str:
        buf = io.StringIO()
        write_dimacs(self, buf)
        return buf.getvalue()

    def save(self, path: str) -> None:
        with open(path, "w", encoding="ascii") as fh:
            write_dimacs(self, fh)

    def __repr__(self) -> str:  # pragma: no cover - debugging aid
        return f"<CNF vars={self.nvars} clauses={len(self.clauses)}>"


# --------------------------------------------------------------------------
# DIMACS I/O
# --------------------------------------------------------------------------


def parse_dimacs(text: str, strict: bool = False) -> CNF:
    """Parse DIMACS CNF text.

    Tolerates the real-world deviations that appear in benchmark archives:
    clauses split across lines, a missing or wrong header, ``%`` / trailing
    ``0`` terminators from SATLIB files, and blank lines.  With ``strict=True``
    a header mismatch raises instead of being repaired.
    """
    f = CNF()
    declared_vars = declared_clauses = None
    pending: list[int] = []
    for lineno, raw in enumerate(text.splitlines(), 1):
        line = raw.strip()
        if not line:
            continue
        head = line[0]
        if head == "c":
            f.comments.append(line[1:].strip())
            continue
        if head == "%":
            break  # SATLIB terminator
        if head == "p":
            parts = line.split()
            if len(parts) < 4 or parts[1] != "cnf":
                raise ValueError(f"line {lineno}: malformed header {line!r}")
            declared_vars = int(parts[2])
            declared_clauses = int(parts[3])
            if declared_vars > f.nvars:
                f.nvars = declared_vars
            continue
        for tok in line.split():
            try:
                d = int(tok)
            except ValueError:
                raise ValueError(f"line {lineno}: bad token {tok!r}") from None
            if d == 0:
                f.add_dimacs(pending)
                pending = []
            else:
                pending.append(d)
    if pending:
        if strict:
            raise ValueError("input ends with an unterminated clause")
        f.add_dimacs(pending)
    if declared_vars is not None and declared_clauses is not None:
        if declared_vars != f.nvars or declared_clauses != len(f.clauses):
            if strict:
                raise ValueError(
                    f"header says {declared_vars} vars / {declared_clauses} "
                    f"clauses, found {f.nvars} / {len(f.clauses)}"
                )
            f.header_mismatch = (declared_clauses, len(f.clauses))
    return f


def parse_dimacs_file(path: str, strict: bool = False) -> CNF:
    with open(path, "r", encoding="utf-8", errors="replace") as fh:
        return parse_dimacs(fh.read(), strict=strict)


def write_dimacs(f: CNF, out) -> None:
    """Write ``f`` in DIMACS CNF format to a text stream."""
    for c in f.comments:
        out.write(f"c {c}\n")
    out.write(f"p cnf {f.nvars} {len(f.clauses)}\n")
    for c in f.clauses:
        out.write(" ".join(str(to_dimacs(l)) for l in c))
        out.write(" 0\n")


# --------------------------------------------------------------------------
# model helpers
# --------------------------------------------------------------------------


def model_to_dimacs(model: Sequence[bool]) -> list[int]:
    """Convert a boolean model into the signed literal list DIMACS expects."""
    return [(i + 1) if b else -(i + 1) for i, b in enumerate(model)]


def model_from_dimacs(lits: Sequence[int], nvars: int) -> list[bool]:
    model = [False] * nvars
    for d in lits:
        if d == 0:
            continue
        model[abs(d) - 1] = d > 0
    return model
