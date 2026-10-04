# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Lemmas that are already unit when they are added.

Both checkers rejected valid proofs. When a lemma of two or more literals was
added, it was attached watching its first two literals whatever their values.
If the root assignment had already falsified all but one of them, the lemma
was unit at the root -- its last literal should have become true there, and
propagated -- but nothing noticed, and root literals are never revisited. A
later lemma that needed that implication was then rejected as neither RUP nor
RAT.

Found in a CaDiCaL 1.0.3 proof of SATLIB uuf100-0142 that drat-trim, in both
directions, verifies. The differential tests could not see it: both
implementations shared the design. `tests/naive.py` shares nothing, and the
property test below compares against it.

The same investigation found the second bug tested here: the guard against
hostile proof literals bounded them by the proof's *length*, so `6 0` -- a
four-character proof of a seven-variable formula -- was refused as malformed.
"""

from __future__ import annotations

import random
import unittest

from dratify import check_proof, parse_dimacs, parse_proof, register_native
from dratify.lits import from_dimacs

try:
    from tests import naive    # python -m unittest tests.test_root_units
except ImportError:            # discover -s tests, and tests/coverage_report.py,
    import naive               # put tests/ itself on the path instead

# 1 and 2 are false at the root. The lemma (1 2 3) is RUP, and once it is
# added 3 is true at the root, which yields 5 and then 6. Without (1 2 3),
# 6 is not RUP. (-6 7) stops 6 from being accepted vacuously as RAT.
FORMULA = """p cnf 7 7
-1 0
-2 0
1 2 3 4 0
1 2 3 -4 0
-3 5 0
-3 -5 6 0
-6 7 0
"""


def steps(*clauses):
    return [("a", tuple(from_dimacs(l) for l in c)) for c in clauses]


class TestUnitAtRoot(unittest.TestCase):
    engine = "python"

    def check(self, *clauses):
        return check_proof(parse_dimacs(FORMULA), steps(*clauses),
                           engine=self.engine)

    def test_a_lemma_unit_at_the_root_extends_the_root_assignment(self):
        r = self.check((1, 2, 3), (6,))
        self.assertEqual(r.failed_step, -1, r.reason)
        self.assertEqual(r.rup_steps, 2,
                         "6 is RUP once (1 2 3) is added; accepting it any "
                         "other way means the root implication was lost")

    def test_the_order_of_the_false_literals_does_not_matter(self):
        for lemma in [(1, 2, 3), (2, 1, 3), (3, 1, 2), (1, 3, 2), (3, 2, 1)]:
            with self.subTest(lemma=lemma):
                r = self.check(lemma, (6,))
                self.assertEqual(r.rup_steps, 2, r.reason)

    def test_and_the_whole_refutation_goes_through(self):
        r = check_proof(parse_dimacs(FORMULA.replace("p cnf 7 7", "p cnf 7 8")
                                     + "-7 0\n"),
                        steps((1, 2, 3), (6,), ()), engine=self.engine)
        self.assertTrue(r.ok, r.reason)

    def test_the_control_still_rejects(self):
        """Without the unit-at-root lemma, 6 really is not RUP or RAT."""
        r = self.check((6,))
        self.assertEqual(r.failed_step, 1)


def _native():
    """The Rust checker, or None. Registered explicitly, not by side effect.

    A class-level `skipUnless(native_available())` is evaluated at import,
    before anything has registered a checker, so it skips on every run --
    round 1 found exactly that in test_differential.py, and the first version
    of this class repeated it. The Rust checker had the same bug as the Python
    one, so these are the tests that matter most here.
    """
    try:
        import cdclkit_native as impl
    except ImportError:
        return None
    return impl


@unittest.skipIf(_native() is None,
                 "no native checker installed; CI installs cdclkit-native")
class TestUnitAtRootNative(TestUnitAtRoot):
    engine = "native"

    @classmethod
    def setUpClass(cls):
        register_native(_native())

    @classmethod
    def tearDownClass(cls):
        register_native(None)


class TestShortProofsOfLargeFormulas(unittest.TestCase):
    def test_a_short_proof_may_name_any_variable_the_formula_has(self):
        f = parse_dimacs(FORMULA)
        r = check_proof(f, "6 0\n")             # 4 characters, variable 6
        self.assertNotEqual(r.reason[:5], "proof", r.reason)

    def test_a_formula_with_many_variables_and_a_tiny_refutation(self):
        f = parse_dimacs("p cnf 1000 2\n999 0\n-999 0\n")
        self.assertTrue(check_proof(f, "0\n").ok)
        self.assertTrue(check_proof(f, "999 0\n0\n").ok)

    def test_the_hostile_input_guard_still_holds(self):
        f = parse_dimacs("p cnf 1 0\n")
        with self.assertRaises(ValueError):
            check_proof(f, "99999999999 0\n")

    def test_parse_proof_on_its_own_accepts_any_variable_index(self):
        """Parsing allocates nothing per variable; only the checker must bound."""
        self.assertEqual(parse_proof("1000000 0\n"),
                         [("a", (from_dimacs(1000000),))])


class TestAgainstTheNaiveReference(unittest.TestCase):
    """RUP-only, additions-only: the subset with one unambiguous answer.

    Uniformly random lemmas almost never trigger the bug this file is about.
    The first version of this test ran 1,500 rounds against the broken checker
    and passed. So the generator aims at it: lemmas built mostly from literals
    the root assignment has already falsified, plus one free literal, which is
    exactly a lemma that is unit at the root when it is added. Most candidates
    are kept only if the reference confirms they are RUP, so the proof is
    valid and any rejection is the checker's fault; some are kept unchecked,
    so rejections are compared as well.
    """

    ROUNDS = 1500

    @staticmethod
    def _literal(rng, nvars):
        v = rng.randrange(1, nvars + 1)
        return v if rng.random() < .5 else -v

    def _proof(self, rng, nvars, formula):
        lemmas: list[tuple[int, ...]] = []
        for _ in range(rng.randrange(2, 12)):
            root = naive.implied(formula + lemmas)
            if root is None:
                break
            falsified = [-l for l in root]
            k = rng.randrange(0, min(3, len(falsified)) + 1)
            lemma = set(rng.sample(falsified, k))
            free = self._literal(rng, nvars)
            if -free not in lemma:
                lemma.add(free)
            lemma = tuple(rng.sample(sorted(lemma), len(lemma)))
            valid = naive.propagates_to_conflict(formula + lemmas,
                                                 {-l for l in lemma})
            if valid or rng.random() < .15:
                lemmas.append(lemma)
        if rng.random() < .3:
            lemmas.append(())
        return lemmas

    def test_random_proofs_agree_with_a_checker_that_shares_nothing(self):
        rng = random.Random(20261004)
        for round_ in range(self.ROUNDS):
            nvars = rng.randrange(3, 9)
            formula = []
            for _ in range(rng.randrange(2, 3 * nvars)):
                k = rng.choice((1, 2, 2, 3, 3, 4))
                vs = rng.sample(range(1, nvars + 1), min(k, nvars))
                formula.append(tuple(v if rng.random() < .5 else -v for v in vs))
            lemmas = self._proof(rng, nvars, formula)

            text = f"p cnf {nvars} {len(formula)}\n" + "".join(
                " ".join(map(str, c)) + " 0\n" for c in formula)
            want_ok, want_step = naive.check(formula, lemmas)
            got = check_proof(parse_dimacs(text), steps(*lemmas),
                              check_rat=False, apply_deletions=False)
            if (got.ok, got.failed_step) != (want_ok, want_step):
                self.fail(
                    f"round {round_}: dratify says ok={got.ok} "
                    f"failed_step={got.failed_step}, the reference says "
                    f"ok={want_ok} failed_step={want_step}.\n"
                    f"formula={formula}\nlemmas={lemmas}")


if __name__ == "__main__":
    unittest.main()
