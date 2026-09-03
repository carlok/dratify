#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Randomised testing of the two things this package promises.

`SECURITY.md` rates two failures High: a crash or hang on untrusted input, and
an exception a caller cannot distinguish from a verdict. Both are properties of
inputs nobody wrote down, which is what a fuzzer is for. The unit suite covers
the hostile cases someone thought of; this covers the ones nobody did.

Three properties, each a separate failure mode:

1. **The parsers terminate and fail cleanly.** Malformed input must raise
   `ValueError`, not `IndexError`, `MemoryError`, `RecursionError` or a hang.
   A caller writing `except ValueError` around a parse should not be surprised.

2. **The two checkers agree.** Every field of `CheckResult`, on the same random
   formula and the same random proof, for the Python and Rust implementations.
   This is the claim the package is sold on; a fuzzer is where it can be tested
   on inputs neither author chose.

3. **`ok` implies `reached_empty`.** A refutation that never derived the empty
   clause is not a refutation, and accepting one is the failure that matters
   most -- it is how a truncated proof passes for a valid one.

Deterministic given a seed, so a failure is reproducible:

    python tests/fuzz.py --seed 12345
"""

from __future__ import annotations

import argparse
import pathlib
import random
import string
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent.parent / "src"))

from dratify import (CNF, check_proof, parse_dimacs,  # noqa: E402
                     parse_proof, register_native)
from dratify.proof import DRATChecker, _native_check  # noqa: E402

#: exceptions a caller can reasonably be asked to catch from a parser
EXPECTED = (ValueError,)


def native():
    try:
        import cdclkit_native as impl
    except ImportError:
        return None
    return impl


# -- 1. parsers ------------------------------------------------------------

def random_text(rng: random.Random) -> str:
    """Something between plausible DIMACS and line noise."""
    alphabet = string.digits + "-0 \n\tpcnf%x" + string.printable[:20]
    n = rng.randrange(0, 400)
    body = "".join(rng.choice(alphabet) for _ in range(n))
    if rng.random() < 0.5:
        nv = rng.choice([0, 1, 5, -1, 10 ** 12, 2 ** 63])
        nc = rng.choice([0, 1, 5, -3, 10 ** 9])
        body = f"p cnf {nv} {nc}\n" + body
    return body


def fuzz_parsers(rng: random.Random, rounds: int) -> list[str]:
    failures = []
    for i in range(rounds):
        text = random_text(rng)
        for name, fn in (("parse_dimacs", parse_dimacs),
                         ("parse_proof", lambda t: list(parse_proof(t)))):
            try:
                fn(text)
            except EXPECTED:
                pass
            except Exception as e:                    # noqa: BLE001
                failures.append(
                    f"{name} raised {type(e).__name__} ({e}) on round {i}, "
                    f"not ValueError. Input:\n{text!r}")
    return failures


# -- 2 and 3. the checkers -------------------------------------------------

def random_formula(rng: random.Random) -> CNF:
    nvars = rng.randrange(1, 9)
    f = CNF(nvars)
    for _ in range(rng.randrange(1, 4 * nvars)):
        k = rng.randrange(1, min(4, nvars) + 1)
        lits = rng.sample(range(nvars), k)
        f.add([(v << 1) | rng.randrange(2) for v in lits])
    return f


def random_steps(rng: random.Random, nvars: int):
    steps = []
    for _ in range(rng.randrange(0, 12)):
        kind = "d" if rng.random() < 0.25 else "a"
        k = rng.randrange(0, min(3, nvars) + 1)
        lits = tuple((v << 1) | rng.randrange(2)
                     for v in rng.sample(range(nvars), k))
        steps.append((kind, lits))
    if rng.random() < 0.4:
        steps.append(("a", ()))                       # claim the empty clause
    return steps


FIELDS = ("ok", "reason", "steps", "rup_steps", "rat_steps", "deletions",
          "ignored_deletions", "resolvents_checked", "failed_step",
          "reached_empty")


def fuzz_checkers(rng: random.Random, rounds: int, impl) -> list[str]:
    failures = []
    for i in range(rounds):
        f = random_formula(rng)
        steps = random_steps(rng, f.nvars)
        check_rat = rng.random() < 0.8
        deletions = rng.random() < 0.8

        py = DRATChecker(f, check_rat=check_rat,
                         apply_deletions=deletions).check(steps)
        if py.ok and not py.reached_empty:
            failures.append(
                f"round {i}: the Python checker accepted a proof that never "
                f"derived the empty clause. formula={f.clauses} steps={steps}")

        if impl is None:
            continue
        nat = _native_check(f, steps, check_rat, deletions)
        if nat is None:
            continue
        for field in FIELDS:
            a, b = getattr(py, field), getattr(nat, field)
            if a != b:
                failures.append(
                    f"round {i}: checkers disagree on {field!r}: "
                    f"python={a!r} native={b!r}. formula={f.clauses} "
                    f"steps={steps} check_rat={check_rat} "
                    f"apply_deletions={deletions}")
                break
    return failures


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--seed", type=int, default=None,
                    help="reproduce a previous run")
    ap.add_argument("--rounds", type=int, default=2000)
    args = ap.parse_args()

    seed = args.seed if args.seed is not None else random.randrange(2 ** 32)
    print(f"seed {seed} (reproduce with --seed {seed}), "
          f"{args.rounds} rounds per property")

    impl = native()
    if impl is not None:
        register_native(impl)
        print(f"native checker: {impl.__name__}")
    else:
        print("native checker: absent -- the agreement property is not tested")

    failures = fuzz_parsers(random.Random(seed), args.rounds)
    failures += fuzz_checkers(random.Random(seed + 1), args.rounds, impl)

    if failures:
        print(f"\n{len(failures)} failure(s):\n", file=sys.stderr)
        for f in failures[:20]:
            print(f"  - {f}\n", file=sys.stderr)
        return 1
    print("no failures")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
