# Theory

`sigil-neo` is ECC-shaped: an impredicative bottom sort `*` under a
predicative hierarchy `Type0 : Type1 : ...`. Total, bidirectional,
cumulative upward, with NbE conversion. This file explains each choice and
where it lives in code. For the rules themselves (formation, introduction,
elimination, computation), see [`rules.md`](rules.md).

## Sorts and axioms

- `Sort ::= Star (*) | Type(Level)`, `Level ::= Const(n) | Var(a)`
  (`src/core.rs:Sort`, `src/levels.rs:Level`). No symbolic `Succ`/`Max`.
- Axioms (`src/check.rs:infer_sort_value`): `* : Type0`,
  `Type(n) : Type(n+1)`, `Type(?a) : Type(?m)` with `?a < ?m` (fresh
  successor, no symbolic successor node).
- Surface: `*` bottom, bare `Type` ambiguous (fresh variable per occurrence,
  generalized per definition), `Type0`, `Type1`, ... concrete.
- `Star` is not a level: for constraint math it ranks as `-1`, so
  `Star <= anything` is free and `anything <= Star` (other than `Star`) is
  unsatisfiable (`src/levels.rs` header).

## Universes: typical ambiguity + schemes

Bare `Type` elaborates ambiguously. Each definition generalizes over its
level variables: a `Scheme { vars, constraints }` (`src/check.rs:Scheme`)
retaining the constraints generated during checking. Every *use* mints fresh
instance variables (`Global(ix, inst)`, `src/check.rs:Scope::resolve`) and
re-records the retained constraints substituted through the instance map
(`src/check.rs:infer` `Global` arm). Conversion compares instances pairwise
by mutual `<=` (equality, not subtyping).

Because retained constraints can mention variables that appear nowhere in
the recorded type/value, generalization must also collect
`level_vars_constraint` (`src/core.rs`), or one use's bounds leak into the
next as spurious cycles.

Constraints are difference constraints (`Le`/`Lt` over `i64` ranks),
checked per successful def by Bellman-Ford with all-zero init plus a
`>= 0` floor (`src/levels.rs:check_satisfiable`). Stores are checkpointed
per def and rolled back on failure, so a failed comparison leaves no trace.

## Pi: impredicative into `*`, predicative `max` otherwise

`pi_sort(sdom, scod)` (`src/check.rs`):

- codomain a `*`-type → `*`, for *any* domain level (ECC `(Type_i, Prop)`).
- otherwise → predicative `max`: computed directly when both sides are
  concrete, else a fresh variable with `<=` bounds from both sides.

Consequences (all intended):

- Leibniz `path` with motives `(T -> *)` lives in `*` for `T` at any level
  and eliminates definitionally by application (why: next section).
- `* -> *`, `T -> *` live in `Type0`; quantifying over `Type(n)` lands in
  `Type(n+1)`; Hurkens' `V` lands in `Type0`, never `*`
  (`examples/fail_hurkens_star.sig` is the consistency gate: if it ever
  checks, motives go back to small levels).
- No `Type(n) : Type(n)` (`examples/fail_levels.sig`, `fail_typetype.sig`).

## Leibniz equality (`path`): why the formulation is allowed

`path T a b ≡ (P : (T -> *)) -> P a -> P b` (`examples/path.sig`) lives in
`*` for `T` at *any* level. Step by step through `pi_sort`:

1. `T -> *` lives in `Type0` (predicative: the codomain *type* `*` has sort
   `Type0`, so `max(sT, Type0)` is `Type0`-ish however small or large `T`
   is — even `T : Type5` gives a `Type`-level motive type, never `*`).
2. `(P a) -> (P b)` lives in `*`: both sides are `*`-types (each `P x : *`),
   so the impredicative arm fires.
3. The whole `(P : (T -> *)) -> ...` lives in `*`: its codomain (step 2) is
   a `*`-type, and the impredicative arm ignores the domain level
   (`Type0` from step 1) — exactly ECC's `(Type_i, Prop)` rule.

So impredicativity is spent only where the *result* is small. The domain
level never leaks downward: quantifying over `Type(n)` itself still lands
in `Type(n+1)`, which is why Hurkens' `V` lands in `Type0`, never `*`.
Elimination is equally small: `path_subst` takes motives `M : T -> *` and
eliminates by plain application (`p M v`), so a `path` proof only ever
produces `*`-family instances. Lifting a small proof into a large family
(`P : T -> Type`) is rejected — the Pi would live in `Type0`, not `*`, and
conversion is equality, not lifting (`examples/fail_leib_lift.sig`). No
primitive `Eq`, no `Prop` sort.

## Conversion vs subsumption

Conversion (`src/core.rs:conv`) is *equality*: beta/delta + eta for functions,
pairs, and Unit; sorts by equality (distinct concrete levels fail; variable-involving sorts
record both-direction `<=` and hold). `*` does *not* lift inside `conv`.

One-directional cumulativity (`*` and lower levels lift) and function
subsumption (contravariant domains, covariant codomains) live in the
checker's `expect_conv` / `require_sort_le`, not in `conv`. This keeps small
and large motive families from being equated inside conversion
(`liftPath`-shaped ascriptions stay rejected) while `*`-motives still check
against level-general primitives through subsumption.

Evaluation is fuel-bounded (`FUEL_LIMIT = 100_000`) with nesting caps
(`EVAL_DEPTH_LIMIT`, `DEPTH_LIMIT`). Divergence and hostile nesting become
checked errors, never hangs or host overflows. `whnf` unfolds globals
(backwards-only references, so unfolding is well-founded) and fires
eliminator iota for redexes completed by unfolding.

## Dependent functions

Infer for `Var / Sort / App / Ann`; check `Lam` against `Pi`, everything
else via infer + `expect_conv`, except neutrals denoting types in sort
position, which formation-check (applied families in formation position;
`Nat : Nat` still fails since its expectation is no sort).

Telescope defs (`def f (x:A)... [: R] = b`): binders scope like Pi domains.
With `: R`, pure Pi/Lam sugar. Without, the body's *type* is inferred and
the recorded type closes the telescope over it — inference produces types,
never values, so saturated family applications can never claim `T : T`
(`examples/fail_alias*.sig`).

## Predicative Sigma

`(x : A) and B` / `A and B` live at the *larger* of their parts (`max`,
fresh-bounded variable when variables involved). `Void and * : Type0`, never
`*`. `(a, b)` is values only. `fst`/`snd` project with iota; `sig_rect A B P f p : P (a,b)` with iota
`f a b` is the dependent eliminator (primitive, all args explicit, motives
at any level — Coq's `sigT`-in-`Type` configuration). Pair-eta holds
definitionally (`p ≡ (fst p, snd p)` in conversion, like function and Unit
eta). See `examples/sigma.sig`.

## Predicative sums and `match`

`A or B` forms predicatively (`max`); `inl`/`inr` check against a known sum;
`either_rect A B P f g e : P e` eliminates with iota on both sides (motives
at any level). Same cautious footing as Sigma.

Dependent `match e return P { inl a => b1 | inr b => b2 } : P e`
(`examples/match.sig`): exactly one `inl`/`inr` clause, no nesting,
`*`-motives. Iota on canonical scrutinees fires in `eval`. A *variable*
scrutinee refines branch contexts by first-order total substitution of the
constructor pattern for the scrutinee level (`src/subst.rs`: values need no
shifting since levels are absolute; core indices resolve through the closure
environment in stack order past the pending binder; any doubt leaves the
node unchanged — fail-safe toward stuckness, never toward ill-typing).
Non-variable scrutinees elaborate plainly like the eliminator.

## `Void` and `Unit`

- `Void : *`, no constructors. `absurd : (A:Type(?a)) -> Void -> A` is a
  stuck-neutral primitive (no iota needed — no canonical scrutinee exists).
  Level-polymorphic explosion. See `examples/void.sig`.
- `Unit : *` with `()` and `unit_rect P b u` (motives at any level,
  iota `b`). `()` infers unambiguously, unlocking closed sum inhabitants
  (`inl ()`). Definitional uniqueness: every neutral `u : Unit` converts
  with `()` (Unit-eta, no axiom). See `examples/unit.sig`.

## Quotients and truncation

`Quot A R` (`examples/quot.sig`): predicative formation (`max`; `R`
validated as `A -> A -> Type _`, no equivalence proofs required).
`quot_mk` introduction (check-only). `quot_lift A R B f h q : B` needs
explicit respectfulness (`h : forall a b, R a b -> LEIB(B, f a, f b)`,
Leibniz inlined); iota on canonical classes. `quot_ind` is dependent with
transport-stated coherence and `*`-motives (Leibniz transport applies the
proof to `P` itself, which needs `P : Q -> *` — same reason `path_subst`
pins its motive). `quot_sound A R a b h` turns `R`-proofs into `path` proofs
— the one axiom (stuck-neutral, no exactness/reflection).

`Squash A` is derived as `Quot A` by the trivial relation. `squash_rect`
needs an explicit constancy proof; that obligation is what makes Prop-free
truncation sound. Computation holds definitionally.

## W-types and Nat

`W : (A:Type(?a)) -> (B:(A -> Type(?b))) -> Type(?m)` with `?a, ?b <= ?m`
(`src/check.rs:w_type` — the only hand-built type recording constraints).
Complete `W A B` spines compute their level from the actuals, so small-data
trees still live in `*`. `sup` introduction, dependent `w_rect` with iota
`s a f (λb. w_rect ... (f b))`. The IH closure needs an environment, so
W-iota fires in `eval` (which has one), never in `do_apply`/`whnf`; it
quotes components one level above the environment and evaluates in a mirror
environment so free variables keep their levels.

Nat is derived two ways (`examples/nat.sig`): structurally via `W` over a
split Bool family (formation, intro, `nat_rec` computing definitionally via
`match`-refined `w_rect` steps, full `nat_ind` via derived funext +
Unit-eta transports under a generalized motive), and computationally via
Church numerals (`plus one one ≡ two` by beta alone; Geuvers: dependent
induction not derivable there).

Leibniz `path T a b ≡ (P:(T -> *) -> P a -> P b)` lives in `*` and
eliminates by application (`path_subst`). Funext
(`examples/funext.sig`) is derived from quotient classes + `quot_sound`
transport + iota-under-eta, no exactness.

## Holes

`_` scopes to `Core::Hole` (globally unique ids). Check fills determined
shapes (Pi eta-expansion, `()` for `Unit`) or records a metavariable;
`expect_conv` routes through Miller-pattern `unify` (occurs check + level
bound to the oldest context, postponement with drain, zonking). `let`-style
`_`-annotations infer like unannotated lets. Unsolved holes fail the def
with located errors; recorded globals are asserted meta-free
(`examples/holes.sig`, `fail_hole*.sig`).

## Totality and non-goals

Fuel + evaluation-nesting + parser-depth caps make the checker total on host
behavior: divergence is a checked error. Deliberate non-goals: `Type(n) :
Type(n)`, general fixpoints, raw mu/nu combinators (recursion via `W`,
co-recursion deferred to guarded M-types), proof-irrelevance/cubical
extensions (needed for full quotient coherence discharge).
