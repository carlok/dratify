#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Reproduce every performance number this project publishes.

Why this exists
---------------

The README used to quote a speed table, an "~18x faster" headline and an
agreement result against `drat-trim`, none of which could be reproduced from
this repository: the CNF files were not here, no script regenerated the
numbers, and nothing in CI checked them. A reader who wanted to verify the
central claim of the package had no way to.

Every figure printed by this script carries its provenance -- host, CPU, Python
version, checker versions, the exact command -- because a timing without a
machine attached is not a measurement.

Usage
-----

    python bench/repro.py --quick       # generated instances, no network
    python bench/repro.py               # adds fetched SATLIB instances
    python bench/repro.py --json out.json

`--quick` is what CI runs. It asserts the *ordering* (native faster than pure
Python) and never a specific multiple, because shared runners are too noisy for
a ratio to mean anything.

Requirements
------------

Proofs have to come from somewhere. This script prefers external solvers found
on PATH (`cadical`, `kissat`) so the proofs are not authored by anything in
this project, and falls back to `cdclkit` if it is installed. A checker that
only ever sees its own sibling's proofs is not being tested.
"""

from __future__ import annotations

import argparse
import io
import json
import os
import pathlib
import platform
import shutil
import subprocess
import sys
import time

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "src"))

import dratify  # noqa: E402
from dratify import (CNF, check_proof, parse_dimacs,  # noqa: E402
                     parse_proof, register_native, write_dimacs)


def _register_native() -> None:
    """Supply the Rust checker explicitly, as the test suite does.

    `cdclkit-native` embeds this crate but publishes it under its own name, so
    nothing finds it by accident. Registering by hand also means a run cannot
    silently measure the Python checker twice and call the result a speedup.
    """
    try:
        import cdclkit_native as impl
    except ImportError:
        return
    register_native(impl)

CACHE = pathlib.Path(__file__).with_name("instances")
SATLIB = "https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/RND3SAT/"


# -- instances --------------------------------------------------------------

def php(holes: int) -> str:
    """Pigeonhole: `holes + 1` pigeons into `holes` holes. Always UNSAT.

    Generated rather than downloaded so `--quick` needs no network, and hard
    enough that the proofs are worth timing.
    """
    pigeons = holes + 1

    def v(p: int, h: int) -> int:
        return p * holes + h + 1

    clauses = [[v(p, h) for h in range(holes)] for p in range(pigeons)]
    for h in range(holes):
        for p1 in range(pigeons):
            for p2 in range(p1 + 1, pigeons):
                clauses.append([-v(p1, h), -v(p2, h)])
    body = "".join(" ".join(map(str, c)) + " 0\n" for c in clauses)
    return f"p cnf {pigeons * holes} {len(clauses)}\n{body}"


#: `--quick` stops before php(10,9), which needs ~130s per pure-Python check on
#: an M-series laptop -- too slow for a per-push CI job to be worth having, and
#: slow enough that `--repeats 3` on it is a twenty-minute run.
QUICK_HOLES = (6, 7, 8)
FULL_HOLES = (6, 7, 8, 9)


def generated(holes) -> list[tuple[str, str]]:
    return [(f"php({h + 1},{h})", php(h)) for h in holes]


def fetched() -> list[tuple[str, str]]:
    """SATLIB uuf instances. Cached under bench/instances/ after first use."""
    import urllib.request

    CACHE.mkdir(exist_ok=True)
    out = []
    for name, url in (
        ("uuf100-01", SATLIB + "uuf100-430.tar.gz"),
        ("uuf250-01", SATLIB + "uuf250-1065.tar.gz"),
    ):
        cnf = CACHE / f"{name}.cnf"
        if not cnf.exists():
            import io
            import tarfile
            print(f"  fetching {url} ...", file=sys.stderr)
            try:
                raw = urllib.request.urlopen(url, timeout=120).read()
            except Exception as e:                     # offline, or moved
                print(f"  skipping {name}: {e}", file=sys.stderr)
                continue
            with tarfile.open(fileobj=io.BytesIO(raw)) as tf:
                member = next(m for m in tf.getmembers()
                              if m.name.endswith(f"{name}.cnf"))
                cnf.write_bytes(tf.extractfile(member).read())
        out.append((name, cnf.read_text()))
    return out


# -- proofs -----------------------------------------------------------------

def solvers() -> list[str]:
    return [s for s in ("cadical", "kissat") if shutil.which(s)]


def normalise(cnf_text: str, name: str) -> tuple[CNF, str]:
    """Parse the file, and re-serialise it for tools that cannot read it.

    SATLIB CNFs end with a `%` and a `0` line. CaDiCaL rejects them outright
    ("parse error: expected digit or '-'"), and so does PySAT; this parser
    accepts them, which is the only reason the rest of this script can run on
    the standard corpus at all.

    Re-serialising is not free of risk -- it is exactly how a formula silently
    becomes a different formula -- so the header guard is checked first and a
    mismatch stops the run rather than producing a number.
    """
    formula = parse_dimacs(cnf_text)
    if formula.header_mismatch is not None:
        declared, actual = formula.header_mismatch
        raise SystemExit(
            f"refusing to benchmark {name}: the header declares {declared} "
            f"clauses and {actual} were read. Re-serialising would hand the "
            f"tools a different formula than the one on disk.")
    buf = io.StringIO()
    write_dimacs(formula, buf)
    return formula, buf.getvalue()


def make_proofs(cnf_text: str, tmp: pathlib.Path) -> list[tuple[str, str]]:
    """Every (solver, DRAT proof) pair obtainable for this formula.

    All available solvers are used, not just the first: a checker that only
    ever sees one solver's output is tuned to one solver's habits. External
    solvers come first because a proof this project did not author is worth
    more than one it did; `cdclkit` is the fallback when none is installed.
    """
    cnf = tmp / "f.cnf"
    cnf.write_text(cnf_text)
    proof = tmp / "f.drat"
    out: list[tuple[str, str]] = []

    for name in solvers():
        proof.unlink(missing_ok=True)
        # Both solvers emit *binary* DRAT unless told otherwise, and this
        # checker reads the text format only.
        cmd = [name, "--no-binary", str(cnf), str(proof)]
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=1800)
        # 20 == UNSAT by SAT-competition convention
        if r.returncode == 20 and proof.exists() and proof.stat().st_size:
            out.append((name, proof.read_text()))
    if out:
        return out

    try:
        import cdclkit  # noqa: F401
    except ImportError:
        return out
    proof.unlink(missing_ok=True)
    r = subprocess.run([sys.executable, "-m", "cdclkit", "solve", str(cnf),
                        "--proof", str(proof), "--no-model"],
                       capture_output=True, text=True, timeout=1800)
    if r.returncode == 20 and proof.exists():
        out.append(("cdclkit", proof.read_text()))
    return out


# -- measurement ------------------------------------------------------------

def time_check(formula: CNF, steps, engine: str, repeats: int) -> float | None:
    """Best-of-N wall time for one full check, or None if engine is absent."""
    try:
        check_proof(formula, steps, engine=engine)
    except RuntimeError:
        return None                                   # native not installed
    best = float("inf")
    for _ in range(repeats):
        t = time.perf_counter()
        check_proof(formula, steps, engine=engine)
        best = min(best, time.perf_counter() - t)
    return best


def drat_trim(cnf_text: str, proof_text: str, tmp: pathlib.Path):
    """(verdict, seconds) from drat-trim, or (None, None) if not installed.

    drat-trim checks *backwards* from the empty clause, so it does strictly
    less work than a forward checker on a proof with unused steps. Comparing
    the two is comparing algorithms, not implementations -- which is the point:
    it is the cost of catching a corrupted step where it occurs.
    """
    if not shutil.which("drat-trim"):
        return None, None
    cnf, proof = tmp / "dt.cnf", tmp / "dt.drat"
    cnf.write_text(cnf_text)
    proof.write_text(proof_text)
    t0 = time.perf_counter()
    r = subprocess.run(["drat-trim", str(cnf), str(proof)],
                       capture_output=True, text=True, timeout=900)
    dt = time.perf_counter() - t0
    if "s VERIFIED" in r.stdout:
        return True, dt
    if "s NOT VERIFIED" in r.stdout:
        return False, dt
    return None, dt


def perturbations(proof_text: str) -> list[tuple[str, str]]:
    """Damaged proofs, derived from one that verifies.

    An agreement result on acceptances alone is weak: a checker that accepts
    everything agrees with every other checker on every valid proof. These are
    the cases that separate them.

    Two outcomes here are expected and neither is a failure:

    * Not every perturbation is invalid. Flipping the first literal of a step
      changes which literal RAT uses as its pivot, and the step is often still
      justified -- both checkers accept it.
    * drat-trim checks *backwards*, so it verifies only the lemmas the
      refutation actually needs. On uuf100-01 it reports "304 of 403 lemmas in
      core": a corrupted step among the other 99 is never looked at, and
      drat-trim returns VERIFIED. This checker verifies every step in order and
      rejects it. That divergence is the forward/backward trade-off stated in
      the README, and it is the one direction of disagreement that is a feature.

    The direction that would be a real finding is the reverse: this checker
    accepting a proof drat-trim rejects. `main` fails only on that.
    """
    lines = [ln for ln in proof_text.splitlines() if ln.strip()]
    out = []
    if len(lines) > 4:
        # the empty clause is never derived
        out.append(("truncated", "\n".join(lines[:len(lines) // 2]) + "\n"))
    for i, ln in enumerate(lines):
        parts = ln.split()
        if parts and parts[0] != "d" and len(parts) > 2:
            flipped = list(parts)
            flipped[0] = str(-int(parts[0]))
            out.append(("flipped literal",
                        "\n".join(lines[:i] + [" ".join(flipped)]
                                   + lines[i + 1:]) + "\n"))
            break
    # a refutation asserting the empty clause with nothing behind it
    out.append(("unjustified empty clause", "0\n"))
    return out


def caught_only_here(r: dict) -> bool:
    """A corrupted step this checker rejected and drat-trim never examined."""
    return (not r["dratify_accepted"]) and r["drat_trim_accepted"] is True


def verdict(r: dict) -> str:
    if r["agree"]:
        return "agree"
    if caught_only_here(r):
        return "caught here only"
    return "UNSOUND"


def provenance() -> dict:
    return {
        "host": platform.node(),
        "system": f"{platform.system()} {platform.release()}",
        "machine": platform.machine(),
        "cpu": platform.processor() or platform.machine(),
        "python": platform.python_version(),
        "dratify": dratify.__version__,
        "native": getattr(dratify.native_implementation(), "__name__", None),
        "solvers_available": solvers(),
        "drat_trim": bool(shutil.which("drat-trim")),
        "date": time.strftime("%Y-%m-%d"),
        "command": " ".join([pathlib.Path(sys.argv[0]).name] + sys.argv[1:]),
    }


# -- driver -----------------------------------------------------------------

def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--quick", action="store_true",
                    help="generated instances only; no network")
    ap.add_argument("--max-holes", type=int, metavar="N",
                    help="largest pigeonhole instance to run (default 8 with "
                         "--quick, 9 otherwise); php(10,9) is the slow one")
    ap.add_argument("--repeats", type=int, default=3,
                    help="timed runs per measurement, best taken (default 3)")
    ap.add_argument("--json", type=pathlib.Path,
                    help="write the full result set here")
    ap.add_argument("--assert-ordering", action="store_true",
                    help="exit non-zero unless native beats pure Python "
                         "everywhere it is available (what CI checks)")
    args = ap.parse_args()
    _register_native()

    import tempfile

    holes = QUICK_HOLES if args.quick else FULL_HOLES
    if args.max_holes is not None:
        holes = tuple(h for h in holes if h <= args.max_holes)
    instances = generated(holes) if args.quick else generated(holes) + fetched()
    prov = provenance()
    print(f"# {prov['system']} / {prov['machine']} / python {prov['python']}")
    print(f"# dratify {prov['dratify']}, native: {prov['native']}")
    print(f"# solvers: {', '.join(prov['solvers_available']) or 'none'}"
          f"   drat-trim: {'yes' if prov['drat_trim'] else 'not installed'}")
    print()
    header = f"{'instance':<16}{'solver':<10}{'steps':>9}{'python s':>11}{'native s':>11}{'ratio':>8}  drat-trim"
    print(header)
    print("-" * len(header))

    rows: list[dict] = []
    perturbed: list[dict] = []
    with tempfile.TemporaryDirectory() as td:
        tmp = pathlib.Path(td)
        for name, text in instances:
            formula, text = normalise(text, name)
            got = make_proofs(text, tmp)
            if not got:
                print(f"{name:<16}{'-':<10}{'':>9}  no proof obtained")
                continue
            for solver, proof_text in got:
                steps = list(parse_proof(proof_text))

                py = time_check(formula, steps, "python", args.repeats)
                nat = time_check(formula, steps, "native", args.repeats)
                dt, dt_s = drat_trim(text, proof_text, tmp)

                ratio = (py / nat) if (py and nat) else None
                rows.append({"instance": name, "solver": solver,
                             "steps": len(steps), "python_s": py,
                             "native_s": nat, "ratio": ratio,
                             "drat_trim_verified": dt, "drat_trim_s": dt_s,
                             "native_vs_drat_trim": (nat / dt_s)
                             if (nat and dt_s) else None})
                for label, bad in perturbations(proof_text):
                    mine = check_proof(formula, list(parse_proof(bad))).ok
                    theirs, _ = drat_trim(text, bad, tmp)
                    perturbed.append({"instance": name, "case": label,
                                      "dratify_accepted": mine,
                                      "drat_trim_accepted": theirs,
                                      "agree": theirs is None or mine == theirs})
                print(f"{name:<16}{solver:<10}{len(steps):>9}"
                      f"{py:>11.3f}"
                      f"{(f'{nat:.3f}' if nat is not None else '-'):>11}"
                      f"{(f'{ratio:.1f}x' if ratio else '-'):>8}"
                      f"  {'agrees' if dt else ('DISAGREES' if dt is False else '-')}")

    if perturbed:
        print()
        print(f"{'perturbed proof':<28}{'instance':<14}"
              f"{'dratify':<10}{'drat-trim':<11}verdict")
        print("-" * 72)
        for r in perturbed:
            them = ("accepts" if r["drat_trim_accepted"]
                    else "rejects" if r["drat_trim_accepted"] is False else "-")
            print(f"{r['case']:<28}{r['instance']:<14}"
                  f"{'accepts' if r['dratify_accepted'] else 'rejects':<10}"
                  f"{them:<11}{verdict(r)}")
        agreed = sum(1 for r in perturbed if r["agree"])
        rejected_by_both = sum(1 for r in perturbed
                               if not r["dratify_accepted"]
                               and r["drat_trim_accepted"] is False)
        caught = sum(1 for r in perturbed if caught_only_here(r))
        print(f"\n{agreed}/{len(perturbed)} agree; "
              f"{rejected_by_both} rejected by both")
        if caught:
            print(f"{caught} corrupted step(s) caught here and not by "
                  f"drat-trim, whose backward pass never reaches them -- "
                  f"this is the forward-checking trade-off, not a defect")

    result = {"provenance": prov, "rows": rows, "perturbations": perturbed}
    if args.json:
        args.json.write_text(json.dumps(result, indent=2) + "\n")
        print(f"\nwrote {args.json}")

    # Only one direction is alarming: this checker accepting what the
    # reference rejects. The reverse is the forward/backward difference.
    unsound = [r for r in perturbed
               if r["dratify_accepted"] and r["drat_trim_accepted"] is False]
    if unsound:
        print("\nERROR: this checker accepted a proof drat-trim rejected: "
              + ", ".join(f"{r['instance']}/{r['case']}" for r in unsound),
              file=sys.stderr)
        return 1

    disagreed = [r for r in rows if r["drat_trim_verified"] is False]
    if disagreed:
        print("\nERROR: drat-trim rejected a proof this checker accepted:",
              ", ".join(r["instance"] for r in disagreed), file=sys.stderr)
        return 1

    if args.assert_ordering:
        measured = [r for r in rows if r["ratio"] is not None]
        if not measured:
            print("\nERROR: no native measurements -- the native checker was "
                  "not installed, so this proved nothing.", file=sys.stderr)
            return 1
        slower = [r for r in measured if r["ratio"] < 1.0]
        if slower:
            print("\nERROR: pure Python beat the native checker on: "
                  + ", ".join(r["instance"] for r in slower), file=sys.stderr)
            return 1
        print(f"\nordering holds on {len(measured)} instances "
              f"(ratios {min(r['ratio'] for r in measured):.1f}x"
              f"-{max(r['ratio'] for r in measured):.1f}x)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
