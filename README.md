# sigil-neo

A clean-slate, dependently typed language. Successor to `E:\Code\sigil`,
which is kept for reference but **not reused**: the old implementation mixed its
theory with `unsafe` memory management (`RcBox`, `UnsafeCell`, hand-rolled
allocators) and an unchecked SIMD lexer. This rewrite is **100% safe Rust**
(`#![forbid(unsafe_code)]`), standard-library only (no dependencies).

## Theory (ECC-shaped: impredicative `*` + predicative `Type` levels)

- Sorts: `*` (impredicative bottom) and `Type(l)` levels. `* : Type0`;
  `Type(n) : Type(n+1)`; cumulativity goes up. Surface syntax: `*` is the
  bottom, bare `Type` is an ambiguous level (fresh variable per occurrence,
  typical ambiguity, generalized per definition), `Type0`, `Type1`, ... are
  concrete levels. (`#` is gone.)
- Dependent functions `(x : A) -> B`, non-dependent `A -> B`, lambdas
  `\x y. e` (or `fun x y => e`), application `f x y`, annotated parens
  `(e : T)`, annotated/inferred `let x (: A)? = v in body`.
- **Pi**: impredicative into `*` (any domain level — ECC's `(Type_i, Prop)`
  rule), otherwise predicative `max`. No symbolic level `max`/`+1` faces:
  formation mints a fresh level variable with `<=` bounds (computed directly
  when all sides are concrete). Constraints are cycle-checked per definition
  (Bellman-Ford) — paradoxes surface as universe inconsistencies.
- **Universe polymorphism**: bare `Type` elaborates ambiguously; definitions
  generalize over their level variables (schemes with retained constraints);
  every reference instantiates freshly (`Global(ix, inst)` in the core), so
  one `id` serves `Type0` and `Type5` alike. Conversion compares instances
  pairwise (both-direction `<=` on variables).

- **Leibniz equality is definitional**: `path T a b ≡ ∀ (P : T -> *) -> P a
  -> P b` lives in `*` for `T` at any level and eliminates by plain
  application — no primitive `Eq`, no `Prop` sort (see `examples/path.sig`).
  Data-level rewriting works because data lives in `*` too.
- **`Void : *` with `absurd : (A:Type(?a)) -> Void -> A`** (primitive,
  stuck-neutral, level-polymorphic). Explosion into any level.
- **Predicative Sigma**: `(x : A) and B`, `A and B`, `(a, b)` values only,
  `fst`/`snd` with iota, plus dependent eliminator
  `sig_rect A B P f p` (primitive, motives at any level, iota on complete
  redexes — `fst`/`snd` are definable from it). Formation takes the *max* of
  its parts, so `Void and *` fits `Type0`, never `*`. Pair-eta holds
  definitionally (`p ≡ (fst p, snd p)`).
- **Predicative sums**: `A or B` with `inl`/`inr` (check-only against a known
  sum) and dependent eliminator `either_rect A B P f g e` (motives at any
  level, iota on both sides), plus dependent `match` with refinement
  (`examples/match.sig`). Same cautious footing as Sigma (Coq's
  `sum`-in-`Type` configuration).
- **Set quotients**: `Quot A R` (`examples/quot.sig`) — predicative formation
  (`max`; `R` validated as a binary family, no equivalence proofs required),
  `quot_mk` introduction (check-only), `quot_lift` with explicit
  respectfulness proof (iota on canonical classes), `quot_sound` turning
  `R`-proofs into `path` proofs — the one axiom (stuck-neutral, no
  exactness/reflection). Dependent `quot_ind` with transport-stated coherence
  (`*`-motives: Leibniz transport needs `*`-families).
- **Propositional truncation, derived** (no `Prop`): `Squash A` is `Quot A`
  by the trivial relation; `squash_rect` needs an explicit constancy proof —
  that obligation is what makes Prop-free truncation sound. Computation
  (`squashBeta`) holds definitionally.
- **Dependent `match`**: `match e return P { inl a => b1 | inr b => b2 } :
  P e` (`examples/match.sig`) — exactly one `inl`/`inr` clause, no nesting,
  iota on canonical scrutinees. A *variable* scrutinee refines the branch
  contexts (first-order total substitution); anything else elaborates
  plainly, like the eliminator. Neutral-headed annotations (match or
  eliminator) are rejected — they infer to `P e`, not a literal sort.
- **`Unit : *` with `()` and `unit_rect P b u`** (dependent eliminator, motives
  at any level, iota `unit_rect P b () ≡ b`). Definitional uniqueness: every
  neutral converts with `()` (Unit-eta, no axiom). Unlocks closed sum
  inhabitants (`inl ()`).
- **W-types**: `W : (A:Type(?a)) -> (B:(A->Type(?b))) -> Type(?m)` with
  `?a, ?b <= ?m`; complete `W A B` spines compute their level from the
  actuals (small-data trees still live in `*`). `sup` introduction and
  dependent `w_rect` (iota builds an IH closure, so it fires in `eval` where
  environments exist — never in `do_apply`/`whnf`). Nat derived two ways
  (`examples/nat.sig`): structurally via `W` with a split Bool family —
  formation, introduction, non-dependent recursion (`nat_rec`, computing
  definitionally, via `match`-refined `w_rect` steps) — and computationally
  via Church numerals (`plus one one ≡ two` proven, by beta alone).
  Dependent induction on `WNat`: the `inl`-case goes through on derived
  funext (`examples/funext.sig`: classes by `quot_sound`, reflexivity
  transported along the class-path, conversion closing by iota-under-eta —
  no exactness used); the `inr`-case goes through on Unit-eta. Full `nat_ind`
  assembly (inner-match motive plumbing) is the remaining step.
- **Totality**: fuel-bounded reduction + evaluation-nesting and parser-depth
  caps turn divergence and hostile input into clean errors — the checker
  never hangs or overflows the host stack (regression-tested).
- Deliberate non-goals that stay out: `Type(n) : Type(n)` (Girard-analog —
  pinned by `examples/fail_levels.sig`), general fixpoints (the language is
  total). Hurkens' `V` lands in `Type0`, never `*`
  (`examples/fail_hurkens_star.sig` — the consistency gate: if it ever
  checks, motives go back to small levels).
- Cumulativity upward (`*` and lower levels lift), beta/delta + eta
  conversion (cumulativity-aware on sorts; fuel-limited, so divergence is an
  error, never a hang).
- Top-level `def name : T = v;` checked in order; no forward/self references.

## Roadmap

Nat `natrec`/induction (blocked on casing for W-derived Nat and large
elimination for Church Nat — needs a casing or funext fork decision),
general recursion via W (done) and co-recursion via M-types (positivity +
guardedness, not raw mu/nu combinators). Dependent quotient coherence
discharge needs irrelevance-style reasoning (same reason Lean's `Quot.ind`
targets `Prop`) — a `Prop`/proof-irrelevance or cubical fork would unlock it.

Pitfall: `(x : A)`-prefix overloading means `(P:((x:A) and B x -> *))`
misparses (the named-`and` swallows the `->`); group first:
`(P:(((x:A) and B x) -> *))`. Same for `or`: `(A or B -> *)` is
`A or (B -> *)`, so motive domains need `((A or B) -> *)`.

## Usage

```sh
cargo run -- check examples/prelude.sig   # exits 0
cargo run -- check examples/path.sig      # exits 0
cargo run -- check examples/void.sig      # exits 0
cargo run -- check examples/sigma.sig     # exits 0
cargo run -- check examples/either.sig    # exits 0
cargo run -- check examples/match.sig     # exits 0
cargo run -- check examples/quot.sig      # exits 0
cargo run -- check examples/funext.sig    # exits 0
cargo run -- check examples/unit.sig      # exits 0
cargo run -- check examples/nat.sig       # exits 0
cargo run -- check examples/fail_match.sig # exits 1 with the errors
cargo run -- check examples/fail_levels.sig # exits 1 with the errors
cargo test                                # 100+ unit tests
```

## Layout

- `src/lexer.rs` — safe tokenizer with spans (`*`, `Type` levels, `--`/`//` comments).
- `src/parser.rs` — recursive descent, surface AST, backtracking only for
  `(x : A) -> B` vs `(e : T)`.
- `src/core.rs` — sorts, de Bruijn core/values/closures, `eval`/`whnf`/
  `quote`/`conv`, pretty-printing.
- `src/levels.rs` — universe levels, constraints, Bellman-Ford satisfiability.
- `src/subst.rs` — first-order total substitution of constructor patterns
  for variable scrutinee levels (match refinement).
- `src/check.rs` — scope checking + bidirectional elaboration, per-def errors.
- `src/cli.rs` — `check <file>` CLI.
- `examples/` — `prelude.sig`, `path.sig` (should pass), `fail_*.sig`
  (should fail, each documenting one boundary).
