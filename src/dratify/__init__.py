# SPDX-License-Identifier: Apache-2.0
"""Check a DRAT/DRUP proof of unsatisfiability, inside your Python process.

A SAT solver that answers "unsatisfiable" is asking to be trusted. A DRAT proof
is how it stops asking: the solver logs every clause it derives, and a checker
that shares no code with it replays the log and confirms the empty clause
really follows.

Emitting those proofs is common -- PySAT exposes them from six solver families
via ``with_proof=True`` / ``get_proof()``. *Checking* them from Python has not
been possible: ``drat-trim`` is C you have to compile and shell out to, and the
one checker on PyPI installs only on Linux x86-64 under Python <= 3.10.

    >>> from dratify import parse_dimacs, check_proof
    >>> formula = parse_dimacs(open("problem.cnf").read())
    >>> result = check_proof(formula, open("proof.drat").read())
    >>> result.ok
    True

Two engines, and that is the point
----------------------------------
The pure-Python checker has zero dependencies and runs anywhere Python does.
The optional Rust accelerator (``pip install "cdclkit[native]"``, which
registers itself here -- there is no ``dratify[native]`` extra) is roughly 15x
faster. Neither is the "real" one: proof checking is the one domain where two
independent implementations agreeing *is* the evidence, and these two have been
differentially tested against each other, on acceptances and on rejections.

Pass ``engine="python"``, ``engine="native"``, or ``engine="auto"`` (the
default: native when installed).

RUP and RAT are both checked. Checking is forward -- every step is verified,
rather than working backwards from the empty clause.
"""

from __future__ import annotations

from .cnf import CNF
from .lits import from_dimacs, to_dimacs
from .proof import (
    CheckResult,
    DRATChecker,
    register_native,
    MemoryProof,
    ProofWriter,
    check_proof,
    parse_proof,
    native_implementation,
)
from .cnf import parse_dimacs, parse_dimacs_file, write_dimacs
from . import _nativeinfo

__version__ = "0.1.5"

__all__ = [
    "CNF",
    # the return type of check_proof: this package ships py.typed, so it has to
    # be importable for anyone annotating what the API hands back
    "CheckResult",
    "DRATChecker",
    "MemoryProof",
    "ProofWriter",
    "check_proof",
    "parse_proof",
    "register_native",
    "parse_dimacs",
    "parse_dimacs_file",
    "write_dimacs",
    "from_dimacs",
    "to_dimacs",
    "native_available",
    "native_implementation",
    "__version__",
]


def native_available() -> bool:
    """True when the optional Rust checker is installed."""
    return _nativeinfo.available()
