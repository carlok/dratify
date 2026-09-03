# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Literal and truth-value representation.

This package uses the standard "doubled index" literal encoding found in
MiniSat, Glucose and CaDiCaL:

    variable v          0-based integer in [0, nvars)
    positive literal    2*v
    negative literal    2*v + 1

Note the 0-based variable.  DIMACS numbers variables from 1, so the DIMACS
variable ``d`` is the internal variable ``d - 1``, and its positive literal is
``2*(d - 1)``.  Getting this wrong is the most common error when working with
this code; :func:`from_dimacs` is the only place the conversion belongs.

The encoding makes negation a single XOR (``lit ^ 1``), makes the variable a
single shift (``lit >> 1``) and lets every per-literal table be a flat array of
length ``2 * nvars`` indexed directly by the literal.  Nothing has to branch on
the sign of a literal while walking a clause.

Truth values are represented by the three-valued domain

    U = 0   undefined
    T = 1   true
    F = 2   false

stored in a ``bytearray`` of length ``2 * nvars``.  Both a literal and its
negation get an entry, kept complementary at all times by whatever is doing the
assigning -- here, unit propagation inside :mod:`dratify.proof`.  Reading
``val[lit]`` is then a single array index with no sign test.  ``flip(x)`` maps
T<->F and leaves U alone.

DIMACS literals (the signed non-zero integers used by the standard file format,
where variables are 1-based) are converted at the I/O boundary only; nothing
inside the checker ever sees a signed literal.
"""
from __future__ import annotations

__all__ = [
    "U",
    "T",
    "F",
    "flip",
    "neg",
    "var_of",
    "is_neg",
    "mk_lit",
    "from_dimacs",
    "to_dimacs",
    "lit_str",
    "clause_str",
]

# --------------------------------------------------------------------------
# three-valued logic
# --------------------------------------------------------------------------

U = 0  # undefined
T = 1  # true
F = 2  # false

#: ``_FLIP[x]`` is the negation of truth value ``x`` (U stays U).
_FLIP = (U, F, T)


def flip(x: int) -> int:
    """Negate a three-valued truth value: T<->F, U->U."""
    return _FLIP[x]


# --------------------------------------------------------------------------
# literals
# --------------------------------------------------------------------------


def neg(lit: int) -> int:
    """Return the complement of ``lit``."""
    return lit ^ 1


def var_of(lit: int) -> int:
    """Return the 0-based variable underlying ``lit``."""
    return lit >> 1


def is_neg(lit: int) -> bool:
    """True when ``lit`` is a negative (complemented) literal."""
    return bool(lit & 1)


def mk_lit(var: int, negated: bool = False) -> int:
    """Build the literal for 0-based ``var``, complemented iff ``negated``."""
    return (var << 1) | (1 if negated else 0)


def from_dimacs(d: int) -> int:
    """Convert a signed 1-based DIMACS literal into internal encoding."""
    if d == 0:
        raise ValueError("0 is not a DIMACS literal (it is the clause terminator)")
    v = abs(d) - 1
    return (v << 1) | (1 if d < 0 else 0)


def to_dimacs(lit: int) -> int:
    """Convert an internal literal back into signed 1-based DIMACS form."""
    v = (lit >> 1) + 1
    return -v if (lit & 1) else v


def lit_str(lit: int) -> str:
    """Human-readable form of a literal, e.g. ``x3`` or ``~x3``."""
    return ("~x" if (lit & 1) else "x") + str(lit >> 1)


def clause_str(lits) -> str:
    """Human-readable form of a clause given as internal literals."""
    return "(" + " v ".join(lit_str(l) for l in lits) + ")"
