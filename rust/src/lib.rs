// SPDX-License-Identifier: Apache-2.0
//! Check DRAT/DRUP proofs of unsatisfiability.
//!
//! A SAT solver that answers "unsatisfiable" is asking to be trusted. A DRAT
//! proof is how it stops asking: the solver logs every clause it derives, and
//! a checker that shares no code with it replays the log and confirms the
//! empty clause really follows.
//!
//! Both proof rules are checked. **RUP** (reverse unit propagation) is the
//! common case. **RAT** (resolution asymmetric tautology) is the rule that
//! puts the "A" in DRAT: a clause `C` is RAT on pivot `p` when, for every
//! clause `D` containing `~p`, the resolvent `C ∪ (D \ {~p})` is RUP.
//!
//! Checking is **forward** -- every step is verified in order, rather than
//! working backwards from the empty clause. That is slower on large proofs
//! than backward checking, and it catches a corrupted step where it occurs.
//!
//! ```
//! use dratify::{Checker, Lit};
//! // (a ∨ b) (a ∨ ¬b) (¬a ∨ b) (¬a ∨ ¬b), in the doubled-index encoding
//! // where variable v has literals 2v (positive) and 2v+1 (negative).
//! let formula: Vec<Vec<Lit>> = vec![
//!     vec![0, 2], vec![0, 3], vec![1, 2], vec![1, 3],
//! ];
//! let mut c = Checker::new(2, &formula, true, true);
//! assert!(c.check_step(false, &[0]));   // "a" is RUP
//! assert!(c.check_step(false, &[]));    // and then the empty clause is
//! ```
//!
//! This crate is the engine behind the `dratify` Python package, which ships
//! an independent pure-Python implementation of the same checker. The two are
//! differentially tested against each other, on rejections as well as
//! acceptances -- proof checking is the one domain where two implementations
//! agreeing *is* the evidence.

/// A literal in the doubled-index encoding: variable `v` has literals
/// `2v` (positive) and `2v + 1` (negative).
pub type Lit = u32;

/// The negation of a literal.
#[inline]
pub fn neg(l: Lit) -> Lit {
    l ^ 1
}

/// The variable a literal belongs to.
#[inline]
pub fn var_of(l: Lit) -> u32 {
    l >> 1
}

mod checker;

pub use checker::{CheckResult, Checker};
