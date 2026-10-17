# Soundness argument

An auditable inventory of what sigil-neo's soundness relies on: per rule,
the trusted premise, why it holds, where it is enforced in code, and where
it is pinned by tests. Cross-references: [`rules.md`](rules.md) for the
rule statements, [`theory.md`](theory.md) for the design rationale.

**Status.** Nothing below is fully mechanized yet; the soundness case
today is (a) adaptation of prior art (Luo's ECC for the core calculus),
(b) local code-enforced invariants ("type-preserving by construction",
"fail-safe toward stuckness"), and (c) an adversarial test corpus that
pins every known attack path. The final section lists what full assurance
still requires.

## What soundness means here

1. **Checker totality** — no crash, no hang on any input. Largely bought
   by construction: 100% safe Rust, `#![forbid(unsafe_code)]`, stdlib only,
   and fuel/depth caps on every evaluation gateway (`eval`, `whnf`,
   `do_apply`, `quote`, `conv` — `src/core.rs`). Exhaustion is an
   `EvalError`/`CheckError`, never a wrong answer or a hang.
2. **Type safety** — subject reduction (typing survives beta, delta, every
   iota, eta, and `match` refinement) and canonical forms. This is where
   most of the inventory below lives.
3. **Consistency** — no closed term of `Void`. Via `absurd` this yields:
   nothing is provably always-false; in particular `Type0 : Type0` is
   underivable, and the impredicative bottom cannot be levered into a
   paradox.

## Design-level anchors (why the calculus shape is safe)

- **ECC shape, by construction.** `* : Type0` with `Type(n) : Type(n+1)`
  (`infer_sort_value`, `src/check.rs:1261`) is Luo's ECC bottom `*`
  (Prop-analogue) under a predicative hierarchy — a calculus with a known
  set-theoretic model and consistency proof (Luo 1994). Extensions are
  kept inside the predicative configurations that survive in prior art
  (Coq's `sigT`/`sum`-in-`Type`).
- **Stratification cannot collapse.** `Type(n) : Type(n)` is rejected
  directly ✗ (`examples/fail_levels.sig`, `fail_typetype.sig`,
  `fail_pi_level.sig`) and structurally: no symbolic `Succ`/`Max` nodes
  (`src/levels.rs`), so integer-represented levels cannot hide a
  self-containment; cycle formation surfaces as an unsatisfiable
  difference constraint.
- **The impredicative lever is capped.** Impredicativity into `*`
  (`pi_sort` `src/check.rs:1434`) is the historically loaded rule; it is
  safe only as long as nothing *projects* out of `*`-types into large
  types. Nothing does: `path` eliminates by application on `*`-motives
  only (`✗ examples/fail_leib_lift.sig`), `absurd` targets `A : Type ?`
  from an uninhabited `Void`, and everything inhabiting `*` (Sigma, sums,
  `W`, `Quot`) forms **predicatively** via `max` (`predicative_max`,
  `src/check.rs:1414`) — a small pair/sum/tree/quotient never smuggles a
  large component. Large elimination into `Type0` of predicatively formed
  data is permitted and is not a lever (`examples/either.sig` `bigcase`
  comment). The gate: `examples/fail_hurkens_star.sig` must keep failing
  (if it ever checks, the impredicative arm must revert to small motives).
- **Termination of unfolding is structural.** Globals reference *earlier*
  defs only — forward and self references are rejected ✗
  (`examples/fail_forward.sig`, `fail_self.sig`), so delta unfolds
  well-foundedly. There are no fixpoints and no primitives capable of
  building one ✗ (`examples/fail_bogus_rec.sig`). Behavior divergence is
  impossible; fuel exhaustion is the only failure mode.
- **Batch checking with markers.** Referencing a failed def is rejected
  (no cascade becoming "meaningful" later), and every def's universe
  constraints are solved (Bellman-Ford, `levels.rs:check_satisfiable`)
  before its global is recorded; stores are checkpointed per def and
  rolled back, so a failed comparison leaves no trace.

## Subject-reduction premises, per rule

Each item: the rule's sound premise, the argument, the enforcement point,
and the pin.

### Beta, delta, eta (Pi)

- **Premise**: beta/delta preserve typing (standard application-calculus
  fact); eta is sound *for well-typed inputs only* — `conv` never sees
  types (`src/core.rs:1062` signature), so comparing ill-typed terms can
  over-identify (e.g. any neutral with `()`).
- **Why it holds**: bidirectional checking guarantees the invariant —
  `conv` (and `unify`) are only ever called on elaborated, well-typed,
  meta-zonked values (`expect_conv` `src/check.rs:2789`; `conv` runs only
  on meta-free pairs, `src/check.rs:2820`). Under that contract, eta and
  Unit-eta (`src/check.rs:113-115`) identify terms of the *same* type.
- **Enforcement**: the caller contract above; pinned by the whole
  checking suite passing and by `examples/prelude.sig` `etaDemo`.
- **Known limitation** (see *Not claimed* below): the contract is
  enforced by code paths and tests, not by an engine-internal argument.

### Sigma (pairs)

- **Introduction** (`check_pair` `src/check.rs:2876`): `(a, b)` checks
  only against a known Sigma — bare pairs cannot claim types
  (✗ `examples/fail_alias_let.sig`/`fail_alias_fst.sig` pin the
  corresponding smuggling of families through lets/projections).
- **Formation** (`predicative_max`): the `max` rule is what keeps
  projection sound — component types come from the Sigma's *validated*
  type, so `fst p : A` cannot manufacture largeness the formation refused
  (✗ `examples/fail_proj.sig`, `fail_sigma.sig`).
- **Iota**: `fst`/`snd`/`sig_rect` reduce by spine analysis in `do_apply`
  plus `whnf` routing; the `sig_rect` minor premise checks the reduct
  `f a b` against `P (a, b)` *at check time*, so iota is type-preserving
  by construction (`src/check.rs:62-71`).
- **Pair eta** (`src/core.rs:1140-1165`): components convert with
  projections; sound under the same conv contract as above.

### Sums (`or`) and `match`

- **Introduction** (`check_inject` `src/check.rs:2914`): the goal must
  whnf to a canonical sum, and the payload checks against the matching
  side; bare injections are rejected ✗ (`examples/fail_either.sig`).
- **`either_rect`/`match` iota** (`src/core.rs`): both sides reduce on
  canonical scrutinees; reducts are pre-checked against `P (inl a)` /
  `P (inr b)` at the minor premises.
- **`match` refinement** (`src/subst.rs:1-33`, all load-bearing notes
  tested): substitution of the constructor pattern for the scrutinee level
  is (i) first-order and total (variable-against-constructor-only,
  one-pattern-variable — binary sums, so no shifting), (ii) exact — a core
  index is replaced only when it resolves to *exactly* `Var(lx)` through
  the closure environment (level arithmetic from environment length is
  unsound and is not used), and (iii) fail-safe — on any doubt nodes are
  left unchanged, which only subtracts refinement: it can cause
  incompleteness (stuckness), never admit ill-typed terms, because
  nothing new becomes convertible. Pins: `src/subst.rs` unit tests
  (`underflow_is_identity`, `var_hit_and_miss`, …) and
  `examples/match.sig` (the refinement flagship `transport`).

### `Void` and `Unit`

- **No `Void` introduction exists**: no constructors; `absurd`
  applications are stuck-neutral, so evaluation can never manufacture a
  canonical `Void` (✗ `examples/fail_void.sig`). This is the concrete
  form of the consistency claim.
- **Unit eta** (`src/check.rs:107-115`): every neutral `u : Unit`
  converts with `()`. Sound under the conv contract; discharges payload
  equalities that older formulations needed axioms for
  (`examples/funext.sig`, `examples/nat.sig`).

### `W` (trees)

- **Formation** (`w_type` `src/check.rs:1446`): `?a, ?b <= ?m` — the
  formation level bounds both parts; complete spines recompute the level
  from actuals (`w_types_match_surface_spellings`), so small trees stay
  in `*`. ✗ `examples/fail_w.sig`.
- **Introduction**: `sup` has an explicit, validated Pi type
  (`sup_type`). ✗ malformed uses in `fail_w.sig`, `fail_bogus_rec.sig`.
- **Iota and the environment problem** (`w_rect_env_redex`,
  `src/core.rs:638-666`): the IH closure needs an environment, so W-iota
  fires only in `eval` — and *only there*: any redex `eval` leaves stuck
  has a truly neutral scrutinee, which later `whnf` calls over the same
  globals leave stuck too, so the eval-only firing is sound and complete
  given fixed globals (`src/core.rs:648-655`). IH components are quoted
  one level above the environment (quoting at `level + 1` lifts past the
  new binder for free — no explicit lift pass to get wrong).
- **Pin**: `examples/nat.sig` runs full `nat_ind` end-to-end (formation,
  iota, refinement, eta interplay all exercised).

### Quotients and truncation

- **Formation**: predicative `max`; the relation is validated as
  `A -> A -> Type ?` — no equivalence proofs are *demanded*, so coherence
  obligations surface at elimination, not formation ✗
  (`examples/fail_quot_sort.sig`, `fail_quot.sig`).
- **`quot_lift`**: respectfulness `h : (a b : A) -> R a b -> LEIB(B, f a,
  f b)` is an *explicit* proof obligation (Leibniz inlined) — the
  eliminator cannot slide along non-respecting functions. Motive is
  non-dependent `B`; the dependent eliminator `quot_ind` is pinned to
  `*`-motives with transport-stated coherence, the same shape that makes
  Lean's `Quot.ind` sound.
- **`quot_sound`** is the system's one axiom (stuck-neutral, no iota, no
  exactness/reflection ✗ `examples/fail_quot_stuck.sig`): relation proofs
  become `path` proofs between classes. Consistency is *relative to* the
  set-quotient model — the same standing Lean-type-theoretic axiom, not a
  computation rule.
- **`Squash`** (derived): elimination requires an explicit constancy
  proof, which is precisely the obligation that makes Prop-free
  truncation sound; computation holds definitionally
  (`examples/quot.sig` `squashBeta`).

### Metas and holes

- **`unify`** (`src/check.rs:2017/2042/2088`): Miller-pattern solving only,
  with occurs check and the instance bound to the oldest context it
  mentions (an approximation of the standard pattern fragment), plus
  postponement-with-drain and zoned reporting; unsolved holes fail the
  def. Recorded globals are asserted meta-free before recording
  (`src/check.rs:1946`, `src/main.rs:60`), so no live meta can escape
  into a global's value. Pins: `examples/holes.sig`,
  ✗ `fail_hole*.sig`, `fail_alias` family.
- Conservative by design: postponement costs completeness, never
  soundness.

## The adversarial corpus (regression gates)

Every known attack path is pinned; run them as part of `cargo test`
(`include_str!` over `examples/`):

| Gate file | Attack it blocks |
|---|---|
| `fail_hurkens_star.sig` | **Consistency gate**: impredicativity + large motives → Hurkens' `V` in `*` |
| `fail_levels.sig`, `fail_typetype.sig`, `fail_pi_level.sig` | `Type : Type` via concrete or inferred levels |
| `fail_alias*.sig`, `fail_tele.sig` | Saturated families smuggled as terms (via aliases, lets, projections, telescopes) |
| `fail_k_conv.sig` | K-as-conversion over-identifying branches |
| `fail_leib_lift.sig` | Leibniz proofs lifted into large motives |
| `fail_quot*.sig` | Bad carrier/relation shapes; stuck eliminations |
| `fail_forward.sig`, `fail_self.sig`, `fail_bogus_rec.sig` | Non-terminating or self-referential unfolding |
| `fail_hole*.sig` | Unchecked/meta solutions escaping |
| `fail_void.sig`, `fail_unit.sig` | Sort confusion (`() : Void`, `Unit : Unit`) |
| `fail_either.sig`, `fail_match.sig` | Bare injections, non-sum scrutinees, bad motives |

Plus the positive corpus (each `examples/*.sig`) doubles as an
end-to-end exercise: `nat.sig`/`funext.sig` exercise the entire
W-iota + refinement + eta machinery.

## Not claimed (yet)

Honest boundaries of the current assurance:

1. **`conv`'s well-typedness contract is enforced socially, not
   mechanically.** The engine cannot locally prove it is only fed
   well-typed values. Mitigation on the roadmap: debug-mode guards, or
   eventual typed conversion.
2. **Strong normalization is not proven.** Divergence is prevented
   operationally (fuel/depth caps make the checker total); the terms' own
   normalizability is empirical, backed by no fixpoints/no
   forward-refs + the ECC anchor.
3. **`quot_sound` is an adopted axiom** — consistent relative to a
   set-quotient model, but the model is not built here.
4. **No mechanized metatheory.** The pen-and-paper subject-reduction
   argument is distributed across the code comments above.

## Roadmap to full assurance

1. **Engine invariants** (days): debug assertions on the conv/unify input
   contract; property tests — generated well-typed conversions must be
   symmetric and transitive in outcome; the `Void`-search oracle: a
   fuel-bounded generator enumerating candidate closed `Void` inhabitants
   must fail on every one.
2. **Grow the corpus** (ongoing): port the remaining standard paradoxes
   (Russell/Girard encodings, Coquand-style domain attacks) as new
   `fail_*` pins.
3. **Pen-and-paper metatheory** (weeks): the standard lemma list —
   context well-formedness, validity, subject reduction per reduction
   kind (beta, delta, each iota, eta, refinement substitution, W
   closure), then normalization. The genuinely nonstandard deltas are
   W-iota's environment quoting (`src/core.rs:662-665`) and `match`
   refinement (`src/subst.rs`).
4. **Mechanization** (months, definitive): embed the core in Lean or
   Isabelle — syntax, typing, small-step reduction, Progress, Subject
   Reduction; then consistency by model. Given the ECC shape, the
   shortest definitive route is a set-theoretic/ω-set model following
   Luo, into which Sigma/sums/`W`/quotients extend standardly and
   `quot_sound` is validated as the Lean-style axiom.
