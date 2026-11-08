# Notes for coding agents

Short, and every item is a mistake that has actually been made.

## `ok` and `reached_empty` are different questions

```python
r = check_proof(formula, proof)
r.ok              # is this a valid refutation?
r.reached_empty   # was the empty clause actually derived?
```

A proof whose every step verifies but which never reaches the empty clause is
**not** a refutation — it is a valid but incomplete derivation. Conflating the
two is exactly how a truncated proof gets accepted. `CheckResult` also carries
`reason`, `steps`, `rup_steps`, `rat_steps`, `deletions`,
`ignored_deletions`, `resolvents_checked`, `failed_step`, `failed_clause`.

One exception to "actually derived": a formula that unit propagation refutes on
its own gets `ok=True` and `reached_empty=True` with `steps=0`, and the proof is
not read beyond parsing. `reason` says so. Refutation is also final in a proof:
once the clauses conflict at the root, later deletions cannot undo it and every
later addition passes. Both are sound, and neither lets a satisfiable formula
through. A proof whose steps conflict at the root still has to write its `0`.

## `proof` accepts several shapes

`check_proof(formula, proof, check_rat=True, apply_deletions=True, engine="auto")`
takes a `MemoryProof`, a list of steps, or **proof text** — so handing it the
contents of a `.drat` file works directly.

**Prefer text.** A list of steps is `("a" | "d", literals)` with **internal**
literals: non-negative, DIMACS `d` becomes `from_dimacs(d)`. Passing DIMACS
integers there is the most common mistake, and before 0.1.7 the pure-Python
checker did not notice: Python read the negative index from the end of an
array, and refutations of satisfiable formulas were accepted. It raises
`ValueError` now. Text goes through the parser, which converts for you.

## Engines

`engine="python"` always works. `engine="native"` needs a registered
implementation and raises `RuntimeError` with an explanation when there is
none. `engine="auto"` is the default and prefers native.

This package ships no compiled extension of its own. Something that embeds the
Rust crate can supply one via `register_native(module)`; today that is
`cdclkit-native`, so `pip install "cdclkit[native]"` makes the fast checker
available here.

## Rust: literals are a doubled index

```rust
// DIMACS  1 -> 0     -1 -> 1     2 -> 2     -2 -> 3
fn lit(d: i32) -> Lit {
    let v = (d.unsigned_abs() - 1) as Lit;
    (v << 1) | if d < 0 { 1 } else { 0 }
}
```

`Checker::new(nvars, &clauses, check_rat, apply_deletions)` — note `nvars`
comes **first**. Steps are `(is_deletion, literals)`.

The crate has no DIMACS or DRAT parser; it takes data structures. There is a
worked example that reads both file formats in
[cdclkit's tutorial](https://github.com/carlok/cdclkit/blob/main/docs/tutorial/code/rust-demo/src/bin/check_files.rs).

## Checking is forward, not backward

Every step is verified in order, rather than working backwards from the empty
clause as `drat-trim` does. That is slower on large proofs — roughly 2x on a
250,000-step one — and it catches a corrupted step where it occurs.

This is not a nuance. `drat-trim` checks only the lemmas its refutation needs
("304 of 403 lemmas in core" on uuf100-01); corrupt one of the other 99 and it
still reports VERIFIED, while this checker rejects. Run `python bench/repro.py`
to see it happen.

## A deletion is not always applied

A deletion is ignored when the clause, as a set, is unit under the root
assignment: exactly one literal true and all the others false. Clauses of at
most one literal are ignored too. Testing the length alone is the mistake that
got `ok=True` on a satisfiable formula: `(1) (-1 2)` with `d -1 2 0`, `-2 0`, `0`
erased the reason for 2 and left 2 true. An ignored clause stays in place for RUP
and RAT alike and counts in `ignored_deletions`, as does a clause that was not
there to delete.

## This checks proofs; it does not solve

If the task is to *find* a satisfying assignment, this is the wrong package.
Use `python-sat`, or `cdclkit` if a readable self-checking solver is wanted.
