//! sigil-neo: a small dependently typed language (clean-slate rewrite).
//!
//! # Theory (ECC-shaped: impredicative `*` + predicative `Type` levels)
//! - Sorts: `*` (impredicative bottom) and `Type(l)` levels. `* : Type0`;
//!   `Type(n) : Type(n+1)`; cumulativity goes up (`*` and lower levels lift).
//! - Surface: `*` is the bottom; bare `Type` is an ambiguous level (fresh
//!   variable per occurrence, typical ambiguity); `Type0`, `Type1`, ...
//!   are concrete levels. (`#` is gone.)
//! - Dependent functions `(x : A) -> B`, lambdas `\x. e` / `fun x => e`,
//!   application `f x`, annotated/unannotated `let x (: A)? = v in body`.
//! - Pi: impredicative into `*` (any domain level — ECC's `(Type_i, Prop)`),
//!   otherwise predicative `max`. Hence Leibniz `path` lives in `*` for data
//!   at any level and eliminates definitionally, while Hurkens' `V` lands in
//!   `Type0` (its `*`-membership switch is rejected).
//! - No symbolic level `max`/`+1`: formation mints a fresh level variable
//!   with `<=` bounds (computed directly when all sides are concrete).
//!   Constraints are cycle-checked per definition (Bellman-Ford) —
//!   paradoxes surface as universe inconsistencies.
//! - Universe polymorphism: bare `Type` elaborates ambiguously; definitions
//!   generalize over their level variables (schemes + retained constraints);
//!   every reference instantiates freshly (`Global(ix, inst)`), so one
//!   definition serves all levels.
//! - Predicative Sigma/sums with full projections/case (`max`, same footing
//!   as Coq's `Type` configuration). Eliminator motives may target any level
//!   (predicative large elimination); neutral-headed annotations are still
//!   rejected. No general fixpoint (total language).
//! - Set quotients `Quot A R` (`examples/quot.sig`): predicative formation
//!   (`max` of carrier and relation-codomain levels; `R` validated as a
//!   binary family on `A` — bare relations only, no equivalence proofs);
//!   `quot_mk` introduction (check-only); `quot_lift` with explicit
//!   respectfulness proof (iota on canonical classes); `quot_sound` turning
//!   `R`-proofs into `path` proofs — the one axiom (stuck-neutral, like
//!   `absurd`; no exactness/reflection). Dependent `quot_ind` with
//!   transport-stated coherence (`*`-motives: Leibniz transport needs
//!   `*`-families).
//!   Truncation as squash (derived from the trivial relation — no `Prop` sort).
//! - `Void : *` (empty type, no constructors) with primitive vacuous
//!   eliminator `absurd : (A:Type(?a)) -> Void -> A` (stuck-neutral, no iota
//!   rule needed; level-polymorphic). Explosion into any level.
//! - `Unit : *` with sole value `()` and dependent eliminator `unit_rect`
//!   (iota `unit_rect P b () ≡ b`; motives at any level). Definitional
//!   uniqueness: every neutral converts with `()` (Unit-eta, no axiom).
//! - `W`-types: `W : (A:Type(?a)) -> (B:(A -> Type(?b))) -> Type(?m)` with
//!   `?a, ?b <= ?m`; `W A B` applications compute their level from the
//!   actuals, so small-data trees still live in `*`. `sup` introduction and
//!   dependent `w_rect` (iota builds an IH closure, so it fires in `eval`
//!   where environments exist). Nat derived two ways (`examples/nat.sig`):
//!   structurally via `W` with a split Bool family (formation/intro plus
//!   non-dependent recursion via `match`-refined steps, plus dependent
//!   induction via funext/Unit-eta transports under a generalized motive)
//!   and computationally via Church
//!   numerals (impredicative iteration; `plus one one ≡ two` proven).
//! - Holes (`_` in term position, `examples/holes.sig`): the elaborator fills
//!   what the expected type determines (functions eta-expand, `()` inhabits
//!   `Unit`, `_` annotations infer like unannotated `let`s) and solves the
//!   rest by Miller-pattern unification against rigid terms; anything still
//!   undetermined fails the def with a located typed-hole error (never a
//!   guess, never silence). One assignment per hole ever (occurs-checked,
//!   level-bounded to its oldest context); unknowns never alias; zonked
//!   globals are asserted meta-free before recording.
//! - Totality: fuel-bounded reduction + nesting-depth caps in evaluation and
//!   parsing turn divergence/deep input into clean errors, never host
//!   stack overflow.
//! - Top-level `def name : T = v;` checked in order; no forward/self reference.
//! - Bidirectional checking + Normalisation-by-Evaluation (NbE) conversion with
//!   beta/delta, eta for functions, and cumulativity (`* <= Type(n)`).
//! - Weak maps and fibers with quotient splicing (`examples/wmap.sig`,
//!   ported from Lean, all args explicit): retractions, fiber transport,
//!   both quotient maps, and the canonical roundtrip equation; full
//!   coherence (`quot_ind` + representative existence) documented as future
//!   work in the file.
//! - Telescope definitions (`def f (x:A) ... [: R] = b`): binders scope in
//!   order like Pi domains; with `: R` it is pure sugar for Pi/Lam. Without
//!   it, the codomain is inferred — the body's type is elaborated and the
//!   recorded type closes the telescope over it (inference produces types,
//!   never values, so saturated family applications can never prove `T : T`).
//!   Neutrals denoting types also check in formation position (formation
//!   fallback instead of conversion); non-sort expectations still use
//!   infer+convert (`Nat : Nat` rejected). Function subsumption
//!   (contravariant domains, covariant codomains) lets small-motive steps
//!   check against level-general types, without ever passing a small proof
//!   off as a large one.
//!
//! CONSISTENCY GATE: `fail_hurkens_star.sig` must keep failing. Unrestricted
//! large elimination into the impredicative bottom is the historically loaded
//! configuration (cf. Coq's singleton restriction); if that probe ever
//! checks, motives must be restricted back to small levels.
//!
//! # Architecture (all safe Rust, std-only, `forbid(unsafe_code)`)
//! ```text
//! source text -> lexer (tokens+spans) -> parser (surface AST)
//!   -> scope check (surface -> de Bruijn core) -> bidirectional check (NbE conv)
//! ```
//! Previous implementation (`E:\Code\sigil`) mixed theory, unsafe memory
//! management (`RcBox`, `UnsafeCell`, manual allocators) and an unchecked SIMD
//! lexer; it is kept for reference but not reused here.

#![forbid(unsafe_code)]

mod lexer;
mod parser;
mod levels;
mod core;
mod subst;
mod check;
mod cli;

fn main() {
    cli::run();
}
