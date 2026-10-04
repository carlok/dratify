# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""A reference RUP checker built to be obviously correct rather than fast.

Why this exists. The Python and Rust checkers are differentially tested against
each other, and that comparison never noticed that both rejected valid proofs:
a lemma that was unit under the root assignment when it was added did not
extend the root trail, so later lemmas that depended on it failed. Two
implementations of one design share its mistakes. This one shares nothing.

There are no watched literals, no persistent trail, no clause ordering and no
incremental state. Every check recomputes unit propagation from scratch over
the whole clause set, so it is quadratic and only fit for small inputs, which
is all a fuzzer needs. Literals are DIMACS integers, so it does not depend on
`dratify.lits` either.

It checks RUP only, and treats every step as an addition. That is the subset
where "accepted" has a single unambiguous meaning; RAT and deletion semantics
are compared between the two real implementations instead.
"""

from __future__ import annotations


def propagates_to_conflict(clauses: list[tuple[int, ...]],
                           assumed: set[int]) -> bool:
    """Assume each literal in `assumed`, unit-propagate, report a conflict."""
    true = set(assumed)
    if any(-l in true for l in true):
        return True
    changed = True
    while changed:
        changed = False
        for c in clauses:
            if any(l in true for l in c):
                continue
            free = [l for l in c if -l not in true]
            if not free:
                return True
            if len(free) == 1:
                true.add(free[0])
                changed = True
    return False


def implied(clauses: list[tuple[int, ...]]) -> set[int] | None:
    """Literals unit propagation forces from nothing, or None on a conflict."""
    true: set[int] = set()
    changed = True
    while changed:
        changed = False
        for c in clauses:
            if any(l in true for l in c):
                continue
            free = [l for l in c if -l not in true]
            if not free:
                return None
            if len(free) == 1:
                true.add(free[0])
                changed = True
    return true


def check(formula: list[tuple[int, ...]],
          lemmas: list[tuple[int, ...]]) -> tuple[bool, int]:
    """(refuted, failed_step) with dratify's conventions.

    `failed_step` is the 1-based index of the first lemma that is not RUP, or
    -1. A refutation needs every lemma to be RUP and one of them to be empty.

    One convention is dratify's and is followed here on purpose: a formula
    that unit propagation alone refutes is refuted, whatever the proof says.
    That is sound -- the formula really is unsatisfiable -- and the first
    version of this reference disagreed with it, which looked for a moment
    like the checker accepting something it should not.
    """
    if propagates_to_conflict(formula, set()):
        return True, -1
    db = list(formula)
    for i, lemma in enumerate(lemmas, 1):
        if not propagates_to_conflict(db, {-l for l in lemma}):
            return False, i
        if not lemma:
            return True, -1
        db.append(lemma)
    return False, -1
