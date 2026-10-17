# Formation, introduction, elimination, computation

Every type former of `sigil-neo` as its four rule kinds, as implemented.
Each rule carries its code anchor; ✗ lines fail by design and each such
boundary is pinned in an `examples/fail_*.sig` file (tour in
`docs/examples.md`). Snippets check with `cargo run -- check`.

## Notation

- `Γ` — a context (telescope of `x : T` bindings); `Γ, x : A` extends it
  with `x : A`. Judgments `Γ ⊢ t : T` are read by the bidirectional checker
  (`src/check.rs:check`) as "check `t` against `T`" or "infer `T` for `t`"
  depending on the form of `t` (see *Checking direction* below).
- `s`, `s₁`, `s₂` — sorts; the two sort families are `*` and `Type(l)`.
- `max(s₁, s₂)` — the larger sort (`predicative_max`,
  `src/check.rs:1414`): computed when both sides are concrete, else a fresh
  level variable with `<=` bounds from both sides — no symbolic max nodes.
- `b[a/x]` — capture-avoiding substitution of `a` for `x` in `b`.
- `LEIB(X, u, v)` — the Leibniz shape *inlined* at use sites:
  `(P : (X -> *)) -> P u -> P v` (the statement `path X u v` makes;
  `src/check.rs` header). Primitives inline it rather than depending on
  the derived `path` — that is why the notation exists.
- `≡` — definitional equality: holds in `conv` (`src/core.rs:1062`, NbE —
  beta + delta + iota + eta), so it needs no proof term. `quot_sound` is
  the one axiom: equations between classes go through that proof.

## Checking direction

Introductions never infer (`src/check.rs:check`): lambdas check against a
Pi, pairs against a Sigma, `inl`/`inr` against a known sum, `quot_mk`
against a known quotient — bare, their types are ambiguous (any sum, any
Sigma; and ✗ pairs are never type spellings, `examples/fail_sigma.sig`).
Two exceptions with fully determined types: `()` infers
(`infer` `Pt` arm) and `sup` infers (a primitive with an explicit Pi
type). Eliminators always infer (via `infer`'s App arm). The rules below
mark the check-only introductions.

Motives: `sig_rect`/`either_rect`/`unit_rect`/`w_rect` take motives at any
level (predicative formation keeps large elimination honest);
`match` and `quot_ind` are pinned to `*`-motives (`docs/theory.md`).

## Sorts

- **Formation** (axioms, `infer_sort_value` `src/check.rs:1261`):

```text
⊢ *        : Type0
⊢ Type(n)  : Type(n+1)
⊢ Type(?a) : Type(?m)          -- fresh ?m with ?a < ?m
```

  Bare `Type` elaborates to a fresh level variable per occurrence and
  generalizes per definition (`docs/theory.md`).
- **Introduction**: the connectives below are how sorts are inhabited;
  sorts themselves have none.
- **Elimination / Computation**: none (no universe case analysis).

```sigil
def climb : Type1 = Type0;   -- ok: Type0 : Type1
```

✗ `Type(n) : Type(n)` and `* : *` (`examples/fail_levels.sig`,
`fail_typetype.sig`).

## Pi: `(x : A) -> B` / `A -> B`

- **Formation** (`pi_sort` `src/check.rs:1434`):

```text
Γ ⊢ A : s₁     Γ, x:A ⊢ B : s₂
─────────────────────────────────   s = pi_sort(s₁, s₂)
Γ ⊢ (x : A) -> B : s
```

  `pi_sort`: codomain a `*`-type → `*`, for *any* domain level
  (impredicative, ECC's `(Type_i, Prop)`); otherwise predicative
  `max(s₁, s₂)`.
- **Introduction** (check-only, `check` `src/check.rs:2639`):

```text
Γ, x:A ⊢ b : B
────────────────────────────
Γ ⊢ \x. b : (x : A) -> B
```

- **Elimination** (`infer` App; computed by `do_apply` `src/core.rs:486`):

```text
Γ ⊢ f : (x : A) -> B     Γ ⊢ a : A
──────────────────────────────────
Γ ⊢ f a : B[a/x]
```

  No other eliminator.
- **Computation** (all hold in `conv`):

```text
(\x. b) a  ≡  b[a/x]        -- beta
g          ≡  body          -- delta: defined globals unfold
f          ≡  \x. f x       -- eta
```

  Delta is well-founded (backward-only references); `examples/path.sig`
  `id_subst` is *proved* by delta + beta alone. Cumulativity (`*` and lower
  levels lift) and function subsumption (`A' <: A`, `B <: B'` give
  `(A -> B) <: (A' -> B')`) live in the checker's `expect_conv`
  (`src/check.rs:2789`) / `require_sort_le` (`src/check.rs:1387`), not in
  `conv` (`docs/theory.md`).

```sigil
def polyid : (P : * -> *) -> (u : *) -> P u -> P u = \P u x. x;   -- impredicative arm
def applyType : (F : * -> *) -> (A : *) -> * = \F A. F A;         -- * -> * : Type0
```

✗ `examples/fail_pi_level.sig`: stratification enforced through `pi_sort`.

## Sigma: `(x : A) and B` / `A and B`

- **Formation** (`predicative_max` via `infer_sort` `src/check.rs:1203`):

```text
Γ ⊢ A : s₁     Γ, x:A ⊢ B : s₂
─────────────────────────────────
Γ ⊢ (x : A) and B : max(s₁, s₂)
```

  Predicative: a small Sigma never smuggles a large component —
  `Void and * : Type0`, never `*`. `(a, b)` is values only (✗
  `def s : * = (Void, Void);`, `examples/fail_sigma.sig`).
- **Introduction** (check-only, `check_pair` `src/check.rs:2876`):

```text
Γ ⊢ a : A     Γ ⊢ b : B[a/x]     Γ ⊢ (x : A) and B : s
──────────────────────────────────────────────────────
Γ ⊢ (a, b) : (x : A) and B
```

  Bare pairs cannot infer (no Sigma to check against — see *Checking
  direction*).
- **Elimination** (`sig_rect_type` `src/check.rs:3067`; iota routed by
  `do_apply` + `whnf`):

```text
Γ ⊢ p : (x : A) and B
────────────────────────────────
Γ ⊢ fst p : A     Γ ⊢ snd p : B (fst p)
```

  `sig_rect A B P f p : P p` with `f : (a:A) -> (b:B a) -> P (a, b)`;
  motives at any level; `fst`/`snd` are definable from it
  (`examples/sigma.sig` `fst2`/`snd2`).
- **Computation** (all in `conv`):

```text
fst (a, b)              ≡  a
snd (a, b)              ≡  b
sig_rect A B P f (a, b) ≡  f a b
p                       ≡  (fst p, snd p)      -- eta
```

```sigil
def vpair : * = Void and Void;
def big : Type = Void and *;                       -- any Type0 part forces Type0
def mk : (v:Void) -> ((x:Void) and Void) = \v. (absurd Void v, absurd Void v);
```

## Sums: `A or B`

- **Formation** (same `predicative_max` route as Sigma):

```text
Γ ⊢ A : s₁     Γ ⊢ B : s₂
─────────────────────────────
Γ ⊢ A or B : max(s₁, s₂)
```

  Large sides live in `Type0`: `Void or * : Type0`.
- **Introduction** (check-only, `check` `src/check.rs:2639`; ✗ bare
  injections `examples/fail_either.sig`):

```text
Γ ⊢ a : A     S ≡ A or B         Γ ⊢ b : B     S ≡ A or B
────────────────────────         ─────────────────────────
Γ ⊢ inl a : S                    Γ ⊢ inr b : S
```

- **Elimination**:
  - `either_rect A B P f g e : P e` (`either_rect_type`
    `src/check.rs:3126`) with `f : (a:A) -> P (inl a)`,
    `g : (b:B) -> P (inr b)`; motives at any level.
  - dependent `match e return P { inl a => b1 | inr b => b2 } : P e` — one
    clause per side, no nesting, `*`-motives only (`docs/theory.md` why);
    a *variable* scrutinee refines branch contexts by first-order total
    substitution of the pattern for the scrutinee level (`src/subst.rs`),
    fail-safe toward stuckness, never toward ill-typing.
- **Computation** (iota, both sides):

```text
either_rect A B P f g (inl a)  ≡  f a
either_rect A B P f g (inr b)  ≡  g b
```

  `match` iota fires on canonical scrutinees and stays stuck on neutrals;
  refinement makes `h : B e` usable at `B (inl a)` with no transport
  (`examples/match.sig` `transport`).

```sigil
def vsum : * = Void or Void;
def bigsum : Type = Void or *;
def inlDemo : (v:Void) -> (Void or Void) = \v. inl (absurd Void v);
```

## Void

- **Formation** (axiom, `infer_sort_value` `src/check.rs:1261`):

```text
⊢ Void : *
```

- **Introduction**: none — no constructors.
- **Elimination** (`absurd_type` `src/check.rs:3036`):
  `absurd A v : A` for `A` at any level — stuck-neutral primitive,
  level-polymorphic explosion.
- **Computation**: none. `absurd` applications never reduce (no canonical
  `Void` value exists to drive iota), so evaluation can never manufacture
  one — consistency is sharply statable: no closed `Void` term exists by
  construction (`examples/void.sig`, ✗ `fail_void.sig`).

```sigil
def exfalso : (A:*) -> Void -> A = \A v. absurd A v;
```

## Unit

- **Formation** (axiom, `infer_sort_value` `src/check.rs:1261`):

```text
⊢ Unit : *
```

- **Introduction**: `()` — infers (`infer` `Pt` arm): single constructor,
  no missing side (see *Checking direction*). This is what unlocks closed
  sum inhabitants (`inl ()`).
- **Elimination** (`unit_rect_type` `src/check.rs:3536`):
  `unit_rect P b u : P u` with `b : P ()`; motives at any level.
- **Computation** (in `conv`):

```text
unit_rect P b ()  ≡  b         -- iota
u : Unit          ≡  ()        -- eta: every neutral converts with ()
```

  Unit-eta is what discharges payload equalities in the `WNat` `inl`-case
  (`examples/funext.sig`, `examples/nat.sig`). Sound for well-typed inputs
  — same approximation class as cumulativity-in-conversion
  (`src/check.rs:113`).

```sigil
def unitVal : Unit = ();
def leftIsUnit : Unit = either_rect Unit Unit (\_. Unit) (\_. ()) (\_. ()) (inl ());
```

## W: `W A B` (well-founded trees)

- **Formation** (`w_type` `src/check.rs:1446` — the only hand-built type
  recording constraints):

```text
Γ ⊢ A : Type ?a     Γ, x:A ⊢ B : Type ?b     ?a ≤ ?m     ?b ≤ ?m
──────────────────────────────────────────────────────────────────
Γ ⊢ W A B : Type ?m
```

  A complete spine recomputes its level from the actuals
  (`w_types_match_surface_spellings`), so small-data trees stay in `*`:
  `def WNat : * = W Bool Bf;`.
- **Introduction** (`sup_type` `src/check.rs:3187` — infers, all args
  explicit):

```text
Γ ⊢ a : A     Γ, b : B a ⊢ f : W A B
────────────────────────────────────
Γ ⊢ sup A B a f : W A B
```

- **Elimination** (`w_rect_type` `src/check.rs:3462`):
  `w_rect A B P s t : P t` with
  `s : (a:A) -> (f:(b:B a) -> W A B) -> ((b:B a) -> P (f b)) -> P (sup A B a f)`;
  motives at any level — the general recursion scheme behind `Nat`
  (`examples/nat.sig`).
- **Computation**:

```text
w_rect A B P s (sup A B a f)  ≡  s a f (\b. w_rect A B P s (f b))
```

  The reduct builds an induction-hypothesis closure, so (unlike every
  other iota) this one needs an environment: it fires in `eval`
  (`src/core.rs:350`), never in `do_apply`/`whnf`; sound and complete
  given fixed globals — anything left stuck has a truly neutral scrutinee
  that later `whnf` calls leave stuck too.

```sigil
def Bool : * = Unit or Unit;
def Bf : Bool -> * = \b. match b return (\_. *) { inl _ => Void | inr _ => Unit };
def WNat : * = W Bool Bf;
def wzero : WNat = sup Bool Bf (inl ()) (\x. absurd WNat x);
```

## Quotients: `Quot A R` (and `Squash`)

- **Formation** (formation-checked in `check_ty`/`infer_sort`,
  `src/check.rs:1217`):

```text
Γ ⊢ A : Type s₁     Γ ⊢ R : (a:A) -> (b:A) -> Type s₂
──────────────────────────────────────────────────────
Γ ⊢ Quot A R : max(s₁, s₂)
```

  `R` is validated as a bare relation — no equivalence proofs required
  (✗ bad shapes `examples/fail_quot*.sig`).
- **Introduction** (check-only, `check`): `quot_mk a` against a known
  quotient.
- **Elimination**:
  - `quot_lift A R B f h q : B` (`quot_lift_type` `src/check.rs:3238`)
    with respectfulness `h : (a b : A) -> R a b -> LEIB(B, f a, f b)`
    (inlined — see *Notation*).
  - `quot_ind A R P f coh q : P q` (`quot_ind_type` `src/check.rs:3372`) —
    dependent, `*`-motives only, coherence `coh` stated via `quot_sound`
    transport (`docs/theory.md` why).
  - `quot_sound A R a b h : path (Quot A R) (quot_mk a) (quot_mk b)`
    (`quot_sound_type` `src/check.rs:3308`) — the one axiom: turns
    relation proofs into equality proofs.
- **Computation**:

```text
quot_lift A R B f h (quot_mk a)  ≡  f a        -- iota (same on quot_ind)
quot_sound A R a b h             — no iota: stuck-neutral (no exactness)
```

  Derived truncation: `Squash A := Quot A (\_ _. Unit)`; `squash_rect`
  demands an explicit constancy proof, discharged by expanding to
  `quot_lift`'s respectfulness; `squashBeta` computes definitionally
  (`examples/quot.sig`).


## Leibniz `path` (derived, not primitive)

- **Formation**: `path T a b := (P : (T -> *)) -> (P a) -> (P b)`, and
  `path T a b : *` for `T` at *any* level — the whole reason the
  impredicative bottom exists (`docs/theory.md`).
- **Introduction**: reflexivity is a term, not a primitive:
  `id_path T v := \P h. h`.
- **Elimination**: `path_subst T a b p M v : M b` — apply the proof to the
  motive (`p M v`). This *is* application; there is no other eliminator.
- **Computation**: none of its own — it is a definition, so delta + beta
  alone give it:

```text
path_subst T v v (id_path T v) M h  ≡  h
```

  provable by `id_path (M v) h` with no further work (`examples/path.sig`
  `id_subst`).
- ✗ a large-family lift (`P : T -> Type`) is rejected — conversion is
  equality, not lifting (`examples/fail_leib_lift.sig`).


## Derived data (no rules of their own)

`Nat` is not primitive: it is derived on top of the rules above, two ways
(`examples/nat.sig`) — structurally as `WNat := W Bool Bf` with the
`match`-refined `w_rect` step (formation, introduction, recursion and full
dependent induction all check), and as a Church encoding admitted by the
impredicative-into-`*` Pi rule (numerals compute by beta alone; dependent
induction underivable there).
