# Examples tour

Conventions: `cargo run -- check <file>` exits `0` for `examples/*.sig`
(without `fail_` prefix) and `1` for `examples/fail_*.sig`. Each `fail_*`
file documents one boundary and is pinned by a test in `src/check.rs` or
`src/subst.rs`. `cargo test` includes every file below via `include_str!`
(no cwd fragility).

## Should pass

| File | What it proves |
|---|---|
| `prelude.sig` | Polymorphic `id`, `const`, `compose`, `* -> *` application, impredicative `P : * -> *` use, annotated/inferred `let`, eta. |
| `path.sig` | Definitional Leibniz `path`, `path_subst`, `id_path`, `path_symm`, computation `id_subst` by delta+beta. No primitive `Eq`. |
| `void.sig` | `exfalso`, `absurdVoid`, explosion at `T -> T`. No closed `Void` inhabitant exists. |
| `sigma.sig` | Small/large Sigma formation (`Void and * : Type0`), intro, `fst`/`snd`, `fst` applying through, `sig_rect`-defined projections. |
| `either.sig` | Small/large sums, `inl`/`inr` intro, full case `either_rect`, predicative large elimination into `Type0`. |
| `match.sig` | Non-dependent case, closed iota (`pickL`/`pickR`), payload-carrying swap, flagship refinement (`transport`), dependent case, large motives. |
| `quot.sig` | Small/large `Quot` formation, classes, `quot_lift` collapse + `collapseBeta`, `quot_sound` transport, vacuous `quot_ind` over empty quotient, derived `Squash` + `squash_rect` + `squashBeta`. |
| `funext.sig` | Derived funext from quotient classes + `quot_sound` transport + iota-under-eta, plus first use (WNat `inl`-case transport). No exactness. |
| `unit.sig` | `unitVal`, `unit_rect`, first closed sum computation on `inl ()` / `inr ()`. |
| `nat.sig` | W-derived `WNat` (formation, `wzero`/`wsucc`, `nat_rec` computing, full `nat_ind`, `wplus` + commutativity) and Church `Nat` (`plus one one ≡ two`). |
| `holes.sig` | `_ : Unit` is `()`, function eta, holes in pairs, `_` annotation inference, solving through application (`id_path _ ()`). |
| `wmap.sig` | Weak maps, fibers, quotient splicing ported from Lean (transports, both quotient maps, roundtrip equation). Coherence proofs documented as future work in-file. |
| `afsnat.sig` | AFS refinement `Nat := Σ(ν:NatStar) Lim(ν)` (arXiv:1802.02820 §4): subtype + `Lim′` certificates (`nlim`/`limZero`/`limSucc`/`limTwo`), `rec` as `pr₁`-application, definitional `beta_zero`/`beta_succ`, numeral computation, and the `etaMid` pointwise-η engine — all with no `uip`. |

## Should fail (boundaries)

| File | Boundary pinned |
|---|---|
| `fail_alias.sig` | Saturated families are types, never terms: `bigalias Void : Void` rejected (`Type(?n) :! Void`). |
| `fail_alias_let.sig`, `fail_alias_fst.sig` | Smuggled families via `let`/pair projection rejected. |
| `fail_ann.sig`, `fail_letann.sig` | Unchecked ascriptions / unchecked `let`s in types rejected. |
| `fail_app.sig` | Bad applications rejected. |
| `fail_bogus_rec.sig` | Bogus recursion shapes rejected. |
| `fail_either.sig`, `fail_match.sig` | Non-sum scrutinees, bad motives, bare injections rejected. |
| `fail_forward.sig`, `fail_self.sig` | Forward/self references rejected. |
| `fail_hole.sig` | Undetermined holes fail with typed-hole errors; infer-position holes need annotations. |
| `fail_hole_universe.sig` | Unchecked hole solutions against universe levels rejected. |
| `fail_hurkens_star.sig` | Consistency gate: Hurkens' `V` in `*` rejected (must stay `Type0`). |
| `fail_k_conv.sig` | Non-convertible branches rejected. |
| `fail_leib_lift.sig` | Small-to-large proof ascriptions (`liftPath`) rejected. |
| `fail_levels.sig`, `fail_pi_level.sig`, `fail_typetype.sig` | `Type0 : Type0`-style stratification enforced. |
| `fail_proj.sig`, `fail_sigma.sig` | Term projections as types, bad Sigma formation rejected. |
| `fail_tele.sig` | Bad telescope binders rejected. |
| `fail_quot*.sig` | Bad carrier/relation shape, stuck eliminations rejected. |
| `fail_unit.sig`, `fail_void.sig`, `fail_w.sig` | `() : Void`, `Unit : Unit`, bad `W` shapes rejected. |

Run the whole tour:

```sh
cargo run -- check examples/prelude.sig  # 0
cargo run -- check examples/nat.sig       # 0
cargo run -- check examples/afsnat.sig    # 0
cargo run -- check examples/fail_match.sig   # 1
cargo run -- check examples/fail_levels.sig  # 1
```
