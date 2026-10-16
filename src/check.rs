//! Scope checking (surface -> de Bruijn core) + bidirectional type checking.
//!
//! ## Scope
//! - Locals resolve to `Bound` indices; shadowing allowed; `_` becomes a
//!   fresh inaccessible binder (`$wild<n>` internally, `_` on display).
//! - Globals resolve to `Global(ix)` for earlier `def`s only. Forward and
//!   self references are rejected (keeps unfolding well-founded without a
//!   separate productivity analysis; recursion/fixpoints are deferred).
//! - Referencing a *failed* earlier def is also an error (avoids cascades).
//!
//! ## Typing (bidirectional, ECC-shaped, cumulative upward)
//! - Sorts: `*` (impredicative bottom); `Type(l)` levels above. `* : Type0`;
//!   `Type(n) : Type(n+1)`; `Type(?a) : Type(?m)` with `?a < ?m`.
//! - `infer`: Var / Sort / App / Ann.
//! - `check`: Lam against Pi; everything else via `infer` + `expect_conv`
//!   (cumulativity for sorts, subsumption for functions, unification after),
//!   except neutrals denoting types against sort expectations, which
//!   formation-check instead (applied families in formation position;
//!   `Nat : Nat` still fails since its expectation is no sort).
//! - Telescope defs (`def f (x:A) ... [: R] = b`): with `: R`, sugar for
//!   Pi/Lam; without, the body's *type* is inferred and the recorded type
//!   closes the telescope over it (codomain inference for families).
//! - Holes (`_` in term position, `examples/holes.sig`): scope to
//!   `Core::Hole` (globally unique ids); `check` fills determined shapes
//!   (Pi eta-expansion, `()` for `Unit`) or records a metavariable;
//!   `expect_conv` routes through `unify` (Miller-pattern solving with
//!   occurs check + level bound, postponement with drain, zonking); unsolved
//!   holes fail the def with located typed-hole errors; `_` annotations
//!   infer like unannotated `let`s.
//! - `infer_sort(t)`: the sort `s` such that `t : s`.
//! - Pi formation (impredicative into `*`, predicative `max` otherwise).
//! - Conversion: NbE `conv` (beta/delta + eta; conversion is equality —
//!   sorts compare by equality, level variables by mutual `<=`).
//!   Fuel-limited; exhaustion is a checked error, never a hang.
//!   One-directional cumulativity (`*` and lower levels lift) and
//!   function subsumption live in the checker's `expect_conv`, not here.
//! - Universe constraints (`<=`/`<` over levels) accumulate in a global
//!   monotone store, checkpointed per def and cycle-checked (Bellman-Ford)
//!   at each successful def end. A failed comparison leaves no trace.
//!
//! ## Pi rule (sorts of domain-type × codomain-type → Pi sort)
//! - codomain a `*`-type → `*` (impredicative, ANY domain level — ECC's
//!   `(Type_i, Prop)`; Leibniz `path` needs exactly this).
//! - otherwise → predicative `max` (computed when concrete; fresh variable
//!   with `<=` bounds when variables are involved — no symbolic max nodes).
//! Consequences, all intended:
//! - Leibniz `path` (motives `(T -> *)`-typed) lives in `*` for `T` at any
//!   level and eliminates definitionally.
//! - `* -> *`, `T -> *` live in `Type0`; quantifying over `Type(n)` lands in
//!   `Type(n+1)`; Hurkens' `V` lands in `Type0`, not `*`.
//! - Predicative Sigma/sums with full projections/case: formation is `max`
//!   (a small pair/sum never smuggles a large component). No `Type(n)` that
//!   contains itself (Girard-analog, checked directly + by the solver).
//!
//! ## Sigma (predicative — the cautious part)
//! `(x : A) and B` / `A and B` live at the LARGER of their parts (`max`,
//! computed when concrete, fresh-bounded variable otherwise). A small Sigma
//! never smuggles a large component, so projecting can never manufacture
//! largeness. Concretely: `Void and *` fits `Type0`, never `*` (pinned below).
//! `(a, b)` is values only (never a type spelling).
//!
//! ## `sig_rect` (dependent eliminator — implemented, same cautious footing)
//! `sig_rect A B P f (a, b) : P (a, b)` with iota `sig_rect A B P f (a, b) ≡ f a b`
//! (primitive constant, all args explicit, motives at any level). Safe for the
//! same reason predicative Sigma is: it eliminates a predicative Sigma,
//! exactly Coq's `sigT`-in-`Type` configuration. Iota is type-preserving
//! by construction (the reduct `f a b` is checked against `P (a, b)` at the
//! minor premise), spends fuel like beta, and fires via spine analysis in
//! `do_apply` (so global-aliased eliminators count) plus `whnf` routing (so
//! redexes completed by unfolding still reduce). Pair-eta holds definitionally
//! (`p ≡ (fst p, snd p)` in `conv`, like function and Unit eta).
//!
//! ## `either_rect` (sums — same cautious footing as Sigma)
//! `A or B` forms predicatively (`max`); `inl`/`inr` check against known
//! sums; `either_rect A B P f g e : P e` with iota on both sides (primitive
//! constant, motives at any level, sides at any level — large sides are now
//! expressible, predicative formation keeps them honest).
//!
//! ## Quotients (`Quot A R` — predicative set-quotients, `examples/quot.sig`)
//! Formation needs `A : Type ?` and `R : A -> A -> Type ?` (validated shape —
//! bare relations, no equivalence proofs required); the quotient lives at the
//! `max`. `quot_mk a` checks against a known quotient (ambiguous bare, like
//! injections). `quot_lift A R B f h q : B` needs explicit respectfulness
//! (`h : ∀ a b, R a b → LEIB(B, f a, f b)`, Leibniz inlined); iota
//! `lift … (quot_mk a) ≡ f a` fires in `do_apply` on complete spines.
//! `quot_sound A R a b h` turns `R`-proofs into `path` proofs (delta+beta
//! interop with the inlined shape) — the one axiom: stuck-neutral primitive,
//! no iota, no exactness (reflection stays out).
//! `quot_ind` (dependent, `*`-motives only — Leibniz transport applies the
//! proof to `P` itself, which needs `P : Q -> *`, exactly why `path_subst`
//! pins its motive) carries transport-stated coherence; see its builder.
//! Truncation (`Squash`) is derived from the trivial relation, not primitive.
//!
//! ## `match` (dependent case — `either_rect` with refinement)
//! `match e return P { inl a => b1 | inr b => b2 } : P e` (exactly one
//! `inl`/`inr` clause, no nesting; `*`-motives). Iota on canonical
//! scrutinees fires in `eval` (needs no environment beyond the redex
//! itself, but lives there alongside W-iota). Variable scrutinees refine:
//! branch contexts substitute the constructor pattern for the scrutinee
//! level (first-order and total — `subst.rs`; non-variable scrutinees
//! elaborate plainly). Goals apply the motive closure to the pattern value
//! (never motive-core in the pushed environment — off-by-push). The pattern
//! binder denotes the *payload*; the injection shape is what the scrutinee
//! refined to. Neutral-headed annotations (match or eliminator) infer to
//! `P e`, not a literal sort, so they are rejected like all such heads.
//!
//! ## `Unit` (`Unit : *`, `()` inferable, `unit_rect` dependent, Unit-eta)
//! Single-constructor types need no paradox review: `Unit` adds no smuggling
//! (no content to project) and `unit_rect P b u : P u` eliminates into
//! motives at any level with iota `unit_rect P b () ≡ b`. `()` infers
//! unambiguously (unlike pairs/sums there is no missing side), so it joins
//! the neutrals; this also unlocks closed sum inhabitants (`inl ()`).
//! Conversion identifies every neutral with `()` (definitional uniqueness —
//! no axiom): `u : Unit` and `()` are convertible, sound for well-typed
//! inputs (same approximation class as cumulativity-in-conversion).
//!
//! ## `W` (well-founded trees — the general (co)recursion scheme)
//! `W : (A:Type(?a)) -> (B:(A->Type(?b))) -> Type(?m)` with `?a, ?b <= ?m`;
//! complete `W A B` spines compute their level from the actuals (small-data
//! trees still live in `*`). `sup` introduction and dependent `w_rect` (all
//! primitive constants, all args explicit, motives at any level). The iota rule
//! `w_rect A B P s (sup A B a f) ≡ s a f (λb. w_rect A B P s (f b))` builds
//! an induction-hypothesis closure, so unlike every other iota it needs an
//! environment: it fires in `eval` (which has one), never in `do_apply` /
//! `whnf` (which work on bare values). Sound and complete given fixed
//! globals — `eval` normalizes every canonically-headed redex (unfolding the
//! scrutinee first, so global-aliased trees count); anything left stuck has
//! a truly neutral scrutinee that later `whnf` calls leave stuck too.
//!
//! ## Nat, derived two ways (`examples/nat.sig`), induction included
//! - STRUCTURAL (`WNat := W Bool Bf` with split `Bf(inl)=Void`,
//!   `Bf(inr)=Unit` written by `match`): formation, introduction,
//!   non-dependent recursion (`nat_rec`, computing definitionally), AND
//!   dependent induction (`nat_ind`) all check. The ingredients, each
//!   load-bearing: (i) branch refinement substitutes patterns into `ih`'s
//!   type, where canonical patterns let stuck families reduce by iota;
//!   (ii) definitional Unit-eta discharges payload equalities; (iii) funext
//!   derived from quotients (`examples/funext.sig` — classes by
//!   `quot_sound`, reflexivity transported along the class-path, conversion
//!   closing by iota-under-eta, no exactness) discharges child-function
//!   equalities; (iv) the inner `match` motive generalizes over every
//!   scrutinee-dependent premise (`f2`, `ih2` as motive binders), since
//!   `f : Bf a` cannot fit `Bf a2` for abstract `a2`.
//! - COMPUTATIONAL (Church `Nat := (T:*) -> T -> (T -> T) -> T`, admitted by
//!   impredicativity into `*`): closed numerals compute definitionally by
//!   beta alone (`plus one one ≡ two`, proven); dependent induction still
//!   missing (Geuvers: underivable for Church encodings).
//!
//! CONSISTENCY GATE: `fail_hurkens_star.sig` must keep failing. Motives at
//! any level plus the impredicative bottom is the historically loaded shape
//! (cf. Coq's singleton restriction on `Prop`); if that probe ever checks,
//! motives go back to small levels.
//!
//! ## Universe polymorphism (typical ambiguity + explicit instances)
//! Bare surface `Type` elaborates to a fresh level variable per occurrence.
//! Each definition is generalized over the variables in its type+value,
//! retaining the constraints added while checking it (schemes live alongside
//! globals). Every *reference* mints a fresh instance (`Global(ix, inst)` in
//! the core — positional, in scheme order): inference substitutes the
//! instance into the stored type and re-adds retained constraints
//! (substituted); evaluation unfolds by substituting into the stored value
//! (pure — instances are data). Conversion compares instances pairwise,
//! recording both-direction `<=` on variables. So one `id` serves `Type0`
//! and `Type5` alike (pinned by tests below); conflicting requirements never
//! meet across uses. Primitives are schematic for free (fresh variables per
//! `infer` call, no retained constraints).
use crate::core::{pretty_core, pretty_value, conv, eval, whnf, subst_level_value, level_vars_value, level_vars_constraint, Closure, Core, Env, EvalError, GlobalDef, GlobalVals, Sort, Value, FUEL_LIMIT, DEPTH_LIMIT};
use crate::levels::{subst_level_constraint, Constraint, Level, Rel, check_satisfiable, fresh_level_var};
use crate::subst::{subst_val, contains_meta, occurs_meta, free_levels_value};
use crate::lexer::{Span, line_col};
use crate::parser::{SDecl, SExpr};
use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::fmt;

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub struct CheckError {
    pub msg: String,
    pub span: Option<Span>,
}

impl CheckError {
    pub fn new(msg: impl Into<String>) -> Self {
        Self { msg: msg.into(), span: None }
    }
    pub fn spanned(msg: impl Into<String>, span: Span) -> Self {
        Self { msg: msg.into(), span: Some(span) }
    }
}

impl fmt::Display for CheckError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.span {
            Some(sp) => write!(f, "{} (at {}..{})", self.msg, sp.start, sp.end),
            None => write!(f, "{}", self.msg),
        }
    }
}

impl std::error::Error for CheckError {}

impl From<EvalError> for CheckError {
    fn from(e: EvalError) -> Self {
        CheckError::new(e.msg)
    }
}

// ---------------------------------------------------------------------------
// Scoping
// ---------------------------------------------------------------------------

struct Scope<'a> {
    locals: Vec<String>,
    /// Global name -> (def index, scheme arity). Arity drives instance
    /// minting: each reference gets that many fresh level variables.
    globals: &'a HashMap<String, (usize, usize)>,
    failed: &'a [bool],
    wild_counter: u32,
    /// Hole-id supply, by value (initialized from the checker's supply and
    /// written back like `wild_counter`: elaboration mints further ids from
    /// the same sequence, so surface and generated holes never collide).
    holes: Cell<u32>,
}

impl<'a> Scope<'a> {
    fn resolve(&self, name: &str) -> Option<Core> {
        // Locals shadow globals (innermost first).
        for (i, n) in self.locals.iter().rev().enumerate() {
            if n == name {
                return Some(Core::Bound(i));
            }
        }
        if let Some((ix, arity)) = self.globals.get(name) {
            // Fresh universe instance per reference (typical ambiguity:
            // each use varies independently; the checker records the
            // scheme's retained constraints, substituted).
            let inst: Vec<Level> =
                (0..*arity).map(|_| Level::Var(fresh_level_var())).collect();
            return Some(Core::Global(*ix, inst));
        }
        None
    }
}

fn fresh_wild(counter: &mut u32) -> String {
    let n = *counter;
    *counter += 1;
    // `$` can never be written by the lexer (idents are alnum/_/'), so this
    // can never be referenced by later user code. Displayed as `_`.
    format!("$wild{n}")
}

fn display_name(internal: &str) -> String {
    if internal.starts_with("$wild") { "_".to_string() } else { internal.to_string() }
}

fn scope_expr(s: &mut Scope<'_>, e: &SExpr) -> Result<Core, CheckError> {
    match e {
        SExpr::Var { name, span } => {
            match s.resolve(name) {
                Some(c) => {
                    if let Core::Global(g, _) = c {
                        if s.failed.get(g).copied().unwrap_or(false) {
                            return Err(CheckError::spanned(
                                format!("reference to failed definition '{name}'"),
                                *span,
                            ));
                        }
                    }
                    Ok(c)
                }
                None => {
                    // Forward reference or typo: distinguish for a better msg.
                    if s.globals.contains_key(name) {
                        Err(CheckError::spanned(
                            format!("forward reference to '{name}' (defs are checked in order; no forward or recursive references in the MVP)"),
                            *span,
                        ))
                    } else {
                        Err(CheckError::spanned(format!("unbound variable '{name}'"), *span))
                    }
                }
            }
        }
        SExpr::Wild { span } => {
            // A term hole: fresh id from the hole supply (unique across the
            // whole program — never reset, so a recorded id always means the
            // same hole). Elaboration resolves the id to at most one
            // metavariable per definition (see `ensure_meta`); binders named
            // `_` are unaffected (those use `wild_counter`).
            let id = s.holes.get();
            s.holes.set(id + 1);
            Ok(Core::Hole { id, span: *span })
        }
        SExpr::Sort { sort, .. } => Ok(Core::Sort(*sort)),
        SExpr::Void { .. } => Ok(Core::Void),
        SExpr::Absurd { .. } => Ok(Core::Absurd),
        SExpr::Unit { .. } => Ok(Core::Unit),
        SExpr::Pt { .. } => Ok(Core::Pt),
        SExpr::UnitRect { .. } => Ok(Core::UnitRect),
        SExpr::W { .. } => Ok(Core::W),
        SExpr::Sup { .. } => Ok(Core::Sup),
        SExpr::WRect { .. } => Ok(Core::WRect),
        SExpr::Pi { param, param_span: _, dom, cod, .. } => {
            let dom_c = scope_expr(s, dom)?;
            let internal = if param == "_" { fresh_wild(&mut s.wild_counter) } else { param.clone() };
            s.locals.push(internal.clone());
            let cod_c = scope_expr(s, cod);
            s.locals.pop();
            Ok(Core::Pi {
                name: display_name(&internal),
                dom: Box::new(dom_c),
                cod: Box::new(cod_c?),
            })
        }
        SExpr::Arrow { dom, cod, .. } => {
            let dom_c = scope_expr(s, dom)?;
            // Non-dependent arrow: binder inaccessible.
            let internal = fresh_wild(&mut s.wild_counter);
            s.locals.push(internal);
            let cod_c = scope_expr(s, cod);
            s.locals.pop();
            Ok(Core::Pi {
                name: "_".to_string(),
                dom: Box::new(dom_c),
                cod: Box::new(cod_c?),
            })
        }
        SExpr::Sigma { param, param_span: _, dom, cod, .. } => {
            let dom_c = scope_expr(s, dom)?;
            let internal = if param == "_" { fresh_wild(&mut s.wild_counter) } else { param.clone() };
            s.locals.push(internal.clone());
            let cod_c = scope_expr(s, cod);
            s.locals.pop();
            Ok(Core::Sigma {
                name: display_name(&internal),
                dom: Box::new(dom_c),
                cod: Box::new(cod_c?),
            })
        }
        SExpr::And { dom, cod, .. } => {
            let dom_c = scope_expr(s, dom)?;
            // Non-dependent pair type: binder inaccessible.
            let internal = fresh_wild(&mut s.wild_counter);
            s.locals.push(internal);
            let cod_c = scope_expr(s, cod);
            s.locals.pop();
            Ok(Core::Sigma {
                name: "_".to_string(),
                dom: Box::new(dom_c),
                cod: Box::new(cod_c?),
            })
        }
        SExpr::Tuple { first, second, .. } => {
            // Always `Core::Pair` (pair values only — never a type spelling;
            // use `and` for product types).
            Ok(Core::Pair(
                Box::new(scope_expr(s, first)?),
                Box::new(scope_expr(s, second)?),
            ))
        }
        SExpr::Fst { arg, .. } => Ok(Core::Fst(Box::new(scope_expr(s, arg)?))),
        SExpr::Snd { arg, .. } => Ok(Core::Snd(Box::new(scope_expr(s, arg)?))),
        SExpr::SigRect { .. } => Ok(Core::SigRect),
        SExpr::Match { scrut, motive, l_name, l_body, r_name, r_body, .. } => {
            // Branch bodies scope with their pattern binder pushed (shadowing
            // allowed, inner wins — same as lambda clauses). Exhaustiveness
            // was enforced syntactically (exactly inl+inr).
            let scrut_c = scope_expr(s, scrut)?;
            let motive_c = scope_expr(s, motive)?;
            let internal_l = if l_name == "_" {
                fresh_wild(&mut s.wild_counter)
            } else {
                l_name.clone()
            };
            s.locals.push(internal_l.clone());
            let l_body_c = scope_expr(s, l_body);
            s.locals.pop();
            let internal_r = if r_name == "_" {
                fresh_wild(&mut s.wild_counter)
            } else {
                r_name.clone()
            };
            s.locals.push(internal_r.clone());
            let r_body_c = scope_expr(s, r_body);
            s.locals.pop();
            Ok(Core::Match {
                scrut: Box::new(scrut_c),
                motive: Box::new(motive_c),
                l_name: display_name(&internal_l),
                l_body: Box::new(l_body_c?),
                r_name: display_name(&internal_r),
                r_body: Box::new(r_body_c?),
            })
        }
        SExpr::Or { dom, cod, .. } => {
            Ok(Core::Either(
                Box::new(scope_expr(s, dom)?),
                Box::new(scope_expr(s, cod)?),
            ))
        }
        SExpr::Inl { arg, .. } => Ok(Core::Inl(Box::new(scope_expr(s, arg)?))),
        SExpr::Inr { arg, .. } => Ok(Core::Inr(Box::new(scope_expr(s, arg)?))),
        SExpr::EitherRect { .. } => Ok(Core::EitherRect),
        SExpr::Quotient { dom, rel, .. } => Ok(Core::Quotient(
            Box::new(scope_expr(s, dom)?),
            Box::new(scope_expr(s, rel)?),
        )),
        SExpr::QuotMk { arg, .. } => Ok(Core::QuotMk(Box::new(scope_expr(s, arg)?))),
        SExpr::QuotLift { .. } => Ok(Core::QuotLift),
        SExpr::QuotInd { .. } => Ok(Core::QuotInd),
        SExpr::QuotSound { .. } => Ok(Core::QuotSound),
        SExpr::Lam { params, body, span: _ } => {
            let mut cur_body = scope_lam_params(s, params, body)?;
            // `params` were pushed inside; `scope_lam_params` pops them.
            let _ = &mut cur_body;
            Ok(cur_body)
        }
        SExpr::App { fun, arg, .. } => {
            let f = scope_expr(s, fun)?;
            let a = scope_expr(s, arg)?;
            Ok(Core::app(f, a))
        }
        SExpr::Let { name, name_span: _, ann, val, body, .. } => {
            let ann_c = match ann {
                Some(a) => Some(Box::new(scope_expr(s, a)?)),
                None => None,
            };
            // `val` (and `ann`) cannot see the new binder (non-recursive).
            let val_c = scope_expr(s, val)?;
            let internal = if name == "_" { fresh_wild(&mut s.wild_counter) } else { name.clone() };
            s.locals.push(internal.clone());
            let body_c = scope_expr(s, body);
            s.locals.pop();
            Ok(Core::Let {
                name: display_name(&internal),
                ann: ann_c,
                val: Box::new(val_c),
                body: Box::new(body_c?),
            })
        }
        SExpr::Ann { term, ty, .. } => {
            let e = scope_expr(s, term)?;
            let t = scope_expr(s, ty)?;
            Ok(Core::Ann(Box::new(e), Box::new(t)))
        }
    }
}

/// Helper: scope a lambda's parameter list (each `_` fresh), then body.
fn scope_lam_params(s: &mut Scope<'_>, params: &[(String, Span)], body: &SExpr) -> Result<Core, CheckError> {
    let mut internals: Vec<String> = Vec::new();
    for (p, _) in params {
        let internal = if p == "_" { fresh_wild(&mut s.wild_counter) } else { p.clone() };
        // Duplicate binder in one telescope shadows (allowed); no error.
        s.locals.push(internal.clone());
        internals.push(internal);
    }
    let body_c = scope_expr(s, body);
    for _ in params {
        s.locals.pop();
    }
    let mut cur = body_c?;
    for internal in internals.into_iter().rev() {
        cur = Core::Lam { name: display_name(&internal), body: Box::new(cur) };
    }
    Ok(cur)
}

// ---------------------------------------------------------------------------
// Checker state
// ---------------------------------------------------------------------------

/// A checked (or failed) top-level definition.
#[derive(Debug, Clone)]
pub struct Decl {
    pub name: String,
    pub ty: Core,
    pub val: Core,
    pub ok: bool,
    pub error: Option<String>,
}

/// A universe scheme: the level variables a definition was generalized over
/// (in instance order) plus the constraints mentioning them. Uses freshen
/// every variable and re-add retained constraints (substituted), so one
/// definition serves all levels.
#[derive(Debug, Clone, Default)]
pub struct Scheme {
    /// Scheme variable ids, in instance order (`inst[i]` replaces `vars[i]`).
    pub vars: Vec<u32>,
    /// Constraints retained from checking (over `vars`).
    pub constraints: Vec<Constraint>,
}

impl Scheme {
    fn arity(&self) -> usize {
        self.vars.len()
    }
}

/// Typing context: parallel stacks for types and values of locals.
#[derive(Debug, Clone, Default)]
struct Ctx {
    types: Env,  // types of levels
    values: Env, // values of levels
}

impl Ctx {
    fn len(&self) -> usize {
        self.types.len()
    }
    fn push(&mut self, ty: Value, val: Value) {
        self.types.push(ty);
        self.values.push(val);
    }
    fn pop(&mut self) {
        self.types.pop();
        self.values.pop();
    }
}

pub struct Checker {
    /// Global names in source order.
    pub gnames: Vec<String>,
    /// Global types (as values, for application checking) by def index.
    gtypes: Vec<Option<Value>>,
    /// Global values (for delta) by def index.
    gvals: GlobalVals,
    /// Universe schemes by def index (parallel to globals; empty for failed
    /// defs, which poisons later references before instantiation matters).
    gschemes: Vec<Scheme>,
    /// Whether each def failed (poisons later references).
    failed: Vec<bool>,
    /// Checked decls in order.
    pub decls: Vec<Decl>,
    wild_counter: u32,
    /// Universe constraints collected during checking (global, monotone).
    /// Solved (cycle-checked) at each successful def end; truncated back to a
    /// per-def checkpoint on failure so speculative constraints (e.g. recorded
    /// by `conv` before it returns `false`) never leak into later defs.
    ucons: RefCell<Vec<Constraint>>,
    /// Metavariables elaborated from `_` holes, indexed by hole id (hole ids
    /// are globally unique, so entries are never reused: checkpoint is a
    /// length, rollback truncates — same discipline as `ucons`). `None`
    /// entries are dense fill (ids minted at scope time may never elaborate,
    /// e.g. inside a failed-early definition).
    metas: RefCell<Vec<Option<MetaEntry>>>,
    /// Deferred conversion problems involving metas (flex-flex pairs and
    /// non-pattern flex-rigid pairs). Revisited whenever an assignment lands
    /// and drained at each successful def end; leftovers with unassigned
    /// metas become typed-hole errors, never recorded facts.
    postponed: RefCell<Vec<(Value, Value)>>,
    /// Fresh-hole supply for elaboration-generated holes (determined
    /// eta-expansion introduces inner holes). Never reset or rolled back:
    /// uniqueness is forever, like `wild_counter`.
    hole_supply: Cell<u32>,
    /// Program source, for rendering hole spans as line:col in error
    /// messages (set once per `check_program`).
    source: RefCell<String>,
}

/// Per-def checkpoint: lengths of the three monotone stores.
#[derive(Clone, Copy)]
struct Checkpoint {
    ucons: usize,
    metas: usize,
    postponed: usize,
}

/// Outcome of one unification step. `Defer` means consistent-so-far
/// (postponed, or solved without changing the verdict): callers accept, the
/// end-of-def drain decides. Only `Mismatch` is a type error here; internal
/// `Err` is fuel/exhaustion, never a mismatch.
#[derive(Debug, PartialEq, Eq)]
enum UOut {
    Eq,
    Defer,
    Mismatch,
}

/// One elaborated `_` hole: at most one metavariable per surface hole per
/// definition (re-encounters — e.g. quote-then-infer roundtrips — resolve the
/// same id; see `ensure_meta`).
#[derive(Debug, Clone)]
struct MetaEntry {
    /// Surface location of the `_` (for typed-hole errors).
    span: Span,
    /// The hole's type, if known (check-mode elaboration always knows it;
    /// lazy unify contact may not — then it stays `None` and only the
    /// span is reported).
    ty: Option<Value>,
    /// Minimum context length across encounters. Solutions may only mention
    /// levels below this (contexts grow append-only, so those levels mean
    /// the same thing in every encounter — the context-independence that
    /// makes one assignment sound for all occurrences).
    origin_len: usize,
    /// The solution, if assigned (always a fully-checked-against-context
    /// value: Miller-pattern spine, occurs-checked, level-bounded).
    assigned: Option<Value>,
}

impl Checker {
    pub fn new() -> Self {
        Self {
            gnames: Vec::new(),
            gtypes: Vec::new(),
            gvals: GlobalVals::new(),
            gschemes: Vec::new(),
            failed: Vec::new(),
            decls: Vec::new(),
            wild_counter: 0,
            ucons: RefCell::new(Vec::new()),
            metas: RefCell::new(Vec::new()),
            postponed: RefCell::new(Vec::new()),
            hole_supply: Cell::new(0),
            source: RefCell::new(String::new()),
        }
    }

    pub fn has_errors(&self) -> bool {
        self.failed.iter().any(|f| *f)
    }

    pub fn report(&self) -> String {
        let mut s = String::new();
        for (i, d) in self.decls.iter().enumerate() {
            s.push_str(&format!(
                "def {} ({}) : {}\n  = {}\n",
                d.name,
                if d.ok { "ok" } else { "FAIL" },
                pretty_core(&d.ty, &self.gnames),
                pretty_core(&d.val, &self.gnames),
            ));
            if let Some(e) = &d.error {
                s.push_str(&format!("  error: {e}\n"));
            }
            let _ = i;
        }
        if !self.has_errors() {
            s.push_str("=> all definitions checked OK\n");
        } else {
            s.push_str("=> some definitions FAILED to check\n");
        }
        s
    }

    fn globals_map(&self) -> HashMap<String, (usize, usize)> {
        // First occurrence wins: later duplicates are recorded as failures
        // (see `check_program`), and later references must keep resolving to
        // the original — pointing them at the failed duplicate entry would
        // poison uses of a good definition (fail-closed either way, but the
        // error would blame the wrong def).
        let mut m = HashMap::new();
        for (i, n) in self.gnames.iter().enumerate() {
            let arity = self.gschemes.get(i).map(|s| s.arity()).unwrap_or(0);
            m.entry(n.clone()).or_insert((i, arity));
        }
        m
    }

    /// Check a whole program. Continues past failures (poisoning later refs).
    pub fn check_program(&mut self, decls: Vec<SDecl>) {
        // Duplicate top-level names are rejected up front (all later dups fail).
        let mut seen: HashMap<String, usize> = HashMap::new();
        for (i, d) in decls.iter().enumerate() {
            if let Some(first) = seen.get(&d.name) {
                let _ = (i, first);
            } else {
                seen.insert(d.name.clone(), i);
            }
        }
        let mut dup_count: HashMap<String, usize> = HashMap::new();
        for d in &decls {
            *dup_count.entry(d.name.clone()).or_insert(0) += 1;
        }
        for d in decls {
            if dup_count.get(&d.name).copied().unwrap_or(0) > 1 {
                // Only the first occurrence is checked; the rest fail.
                let first = *seen.get(&d.name).expect("seen");
                let this_index = self.gnames.len();
                if self.gnames.iter().any(|n| n == &d.name) && first < this_index + 1 {
                    // This is a repeat occurrence: record failure without checking.
                    let dup_name = d.name.clone();
                    self.push_failed(d.name, Core::Sort(Sort::Star), Core::Sort(Sort::Star),
                        format!("duplicate definition '{dup_name}' (first at decl {first})"));
                    continue;
                }
            }
            // Reserved names that would clash with syntax.
            if matches!(d.name.as_str(), "Type" | "def" | "let" | "in" | "fun") {
                self.push_failed(d.name, Core::Sort(Sort::Star), Core::Sort(Sort::Star),
                    "reserved name (clashes with a keyword)".to_string());
                continue;
            }
            self.check_decl(d);
        }
    }

    fn push_failed(&mut self, name: String, ty: Core, val: Core, msg: String) {
        self.gnames.push(name.clone());
        self.gtypes.push(None);
        self.gvals.push(None);
        self.gschemes.push(Scheme::default());
        self.failed.push(true);
        self.decls.push(Decl { name, ty, val, ok: false, error: Some(msg) });
    }

    /// Desugar `def f (x:A) (y:B) : R = b` to the plain form: Pi telescope
    /// for the annotation, nested lambdas for the value. Scoping then treats
    /// both identically (same binders, shadowing, `_` handling) — the only
    /// new surface is the telescope itself.
    fn desugar_telescope(
        &self,
        params: Vec<(String, SExpr)>,
        ret: SExpr,
        body: SExpr,
    ) -> (SExpr, SExpr) {
        let mut ty = ret;
        let mut lam_params: Vec<(String, Span)> = Vec::new();
        let mut lam_span = body.span();
        for (pname, pty) in params.into_iter().rev() {
            let span = Span::new(pty.span().start, ty.span().end);
            lam_span = Span::new(pty.span().start, lam_span.end);
            lam_params.push((pname.clone(), pty.span()));
            ty = SExpr::Pi {
                param: pname,
                param_span: pty.span(),
                dom: Box::new(pty),
                cod: Box::new(ty),
                span,
            };
        }
        lam_params.reverse();
        let val = SExpr::Lam { params: lam_params, body: Box::new(body), span: lam_span };
        (ty, val)
    }

    fn check_decl(&mut self, d: SDecl) {
        // Universe checkpoint: anything recorded while checking this def is
        // rolled back on failure (a failed comparison must leave no trace).
        let ckpt = self.ucheckpoint();
        if d.params.is_empty() {
            let ty = d.ret.expect("parser guarantees an annotation without a telescope");
            return self.check_decl_plain(d.name, ty, d.body, ckpt);
        }
        match d.ret {
            // Pure sugar: a Pi telescope plus nested lambdas is exactly the
            // plain form (same Core after scoping, same checking).
            Some(ret) => {
                let (ty_s, val_s) = self.desugar_telescope(d.params, ret, d.body);
                self.check_decl_plain(d.name, ty_s, val_s, ckpt)
            }
            // Codomain inference: the telescope elaborates below; the body
            // must be a type (formation-checked) and the recorded type closes
            // the telescope over it.
            None => self.check_decl_infer(d.name, d.params, d.body, ckpt),
        }
    }

    fn check_decl_plain(&mut self, name: String, ty: SExpr, val: SExpr, ckpt: Checkpoint) {
        let gmap = self.globals_map();
        let mut scope = Scope {
            locals: Vec::new(),
            globals: &gmap,
            failed: &self.failed,
            wild_counter: self.wild_counter,
            holes: Cell::new(self.hole_supply.get()),
        };
        // Scope the annotation.
        let ty_core = match scope_expr(&mut scope, &ty) {
            Ok(c) => c,
            Err(e) => {
                self.wild_counter = scope.wild_counter;
                self.hole_supply.set(scope.holes.get());
                self.urollback(ckpt);
                self.push_failed(name, Core::Sort(Sort::Star), Core::Sort(Sort::Star), format!("in type: {e}"));
                return;
            }
        };
        // Scope the value (lets are non-recursive; `Option<ann>` preserved).
        let val_core = match scope_expr(&mut scope, &val) {
            Ok(c) => c,
            Err(e) => {
                self.wild_counter = scope.wild_counter;
                self.hole_supply.set(scope.holes.get());
                self.urollback(ckpt);
                self.push_failed(name, ty_core, Core::Sort(Sort::Star), format!("in value: {e}"));
                return;
            }
        };
        self.wild_counter = scope.wild_counter;
        self.hole_supply.set(scope.holes.get());

        // The annotation must be a type-in-a-sort, or a sort itself (see
        // `is_type_value`: `#` annotates large types). Evaluated once, then
        // reused as the expected type for the value. A bare `_` annotation
        // instead infers the value's type (like an unannotated `let` — the
        // elaborator synthesizes what the annotation would have said).
        let ctx = Ctx::default();
        let ty_val = match &ty_core {
            Core::Hole { .. } => match self.infer(&val_core, &ctx) {
                Ok(v) => v,
                Err(e) => {
                    self.urollback(ckpt);
                    self.push_failed(name.clone(), ty_core, val_core, format!("in annotation inference: {e}"));
                    return;
                }
            },
            _ => match self.check_ty(&ty_core, &ctx) {
                Ok(v) => v,
                Err(e) => {
                    self.urollback(ckpt);
                    self.push_failed(name.clone(), ty_core, val_core, format!("in annotation evaluation: {e}"));
                    return;
                }
            },
        };
        match self.is_type_value(&ty_val, &ctx) {
            Ok(_) => {}
            Err(e) => {
                self.urollback(ckpt);
                self.push_failed(name.clone(), ty_core, val_core, format!("bad type annotation (not a type): {e}"));
                return;
            }
        }
        // The value must check against the annotation.
        match self.check(&val_core, &ty_val, &ctx) {
            Ok(()) => {
                // Holes: drain postponed equations, then fail on anything
                // still unsolved (an undetermined `_` is an error, never a
                // recorded fact). Only then cycle-check universes and record.
                if let Err(e) = self.drain_postponed() {
                    self.urollback(ckpt);
                    self.push_failed(name.clone(), ty_core, val_core, format!("{e}"));
                    return;
                }
                if let Err(e) = self.unsolved_holes() {
                    self.urollback(ckpt);
                    self.push_failed(name.clone(), ty_core, val_core, format!("{e}"));
                    return;
                }
                // Success: the accumulated universe constraints (this def's
                // and all prior) must stay satisfiable — this is where cyclic
                // level requirements (Hurkens-shaped) are rejected.
                if let Err(e) = self.ucheck() {
                    self.urollback(ckpt);
                    self.push_failed(
                        name.clone(),
                        ty_core,
                        val_core,
                        format!("universe inconsistency: {e}"),
                    );
                    return;
                }
                // Success: record type/value values for later delta, plus the
                // universe scheme for later instantiation (level variables in
                // type+value, in first-seen order; constraints added by this
                // def, which mention exactly those — earlier defs' variables
                // never leak in, since every use freshened on the way in).
                // Values are zonked first: no metavariable (solved or not)
                // may escape into globals (unsolved ones already failed the
                // def above; the assert below is the safety net).
                let empty2: Env = Vec::new();
                // A `_` annotation was already inferred above (re-evaluating
                // the hole core would mint an entry-less metavariable).
                // Re-evaluation here repeats work already done above with the
                // same fuel, so failure is unreachable — but a failure must
                // fail the def loudly, never record a fabricated value.
                let ty_v = match &ty_core {
                    Core::Hole { .. } => ty_val.clone(),
                    _ => match eval(&ty_core, &empty2, &self.gvals) {
                        Ok(v) => v,
                        Err(e) => {
                            self.urollback(ckpt);
                            self.push_failed(name.clone(), ty_core, val_core, format!("internal error (re-evaluating annotation): {e}"));
                            return;
                        }
                    },
                };
                let val_v = match eval(&val_core, &empty2, &self.gvals) {
                    Ok(v) => v,
                    Err(e) => {
                        self.urollback(ckpt);
                        self.push_failed(name.clone(), ty_core, val_core, format!("internal error (re-evaluating value): {e}"));
                        return;
                    }
                };
                let ty_v = match self.zonk_value(&ty_v) {
                    Ok(v) => v,
                    Err(e) => {
                        self.urollback(ckpt);
                        self.push_failed(name.clone(), ty_core, val_core, format!("internal error (zonk type): {e}"));
                        return;
                    }
                };
                let val_v = match self.zonk_value(&val_v) {
                    Ok(v) => v,
                    Err(e) => {
                        self.urollback(ckpt);
                        self.push_failed(name.clone(), ty_core, val_core, format!("internal error (zonk value): {e}"));
                        return;
                    }
                };
                // `Hole` cores inside closures are benign (they re-elaborate
                // to their assigned entry on use); only *unassigned*
                // unknowns leaking here are a soundness bug. (After the
                // sweep above there should be none — this is the safety net.)
                if self.meta_leak(&ty_v) || self.meta_leak(&val_v) {
                    self.urollback(ckpt);
                    self.push_failed(
                        name.clone(),
                        ty_core,
                        val_core,
                        "internal error (unsolved metavariable leaked into recorded globals — please report)".to_string(),
                    );
                    return;
                }
                let mut vars: Vec<u32> = Vec::new();
                level_vars_value(&ty_v, &mut vars);
                level_vars_value(&val_v, &mut vars);
                // Every variable the retained constraints mention must be
                // quantified too: otherwise instantiation re-records the raw
                // id and one use's bounds leak into the next (spurious
                // universe inconsistencies across definitions).
                let retained = self.ucons.borrow()[ckpt.ucons..].to_vec();
                for c in &retained {
                    level_vars_constraint(c, &mut vars);
                }
                let scheme = Scheme { vars, constraints: retained };
                self.gnames.push(name.clone());
                self.gtypes.push(Some(ty_v));
                self.gvals.push(Some(GlobalDef { value: val_v, levels: scheme.vars.clone() }));
                self.gschemes.push(scheme);
                self.failed.push(false);
                self.decls.push(Decl { name, ty: ty_core, val: val_core, ok: true, error: None });
            }
            Err(e) => {
                self.urollback(ckpt);
                self.push_failed(name, ty_core, val_core, format!("{e}"));
            }
        }
    }

    /// Codomain inference (`def f (x:A) ... := b`, no return type): elaborate
    /// the telescope like Pi domains (each checked as a type), scope the
    /// body under it, then INFER the body's type and close the telescope over
    /// that. The recorded type *is* that Pi (evaluated) — usable by delta
    /// everywhere, exactly as if written out. A body that is a term rather
    /// than a type fails here (its inferred type is not a sort), which is
    /// what keeps type-as-term confusion (e.g. `Nat : Nat`) out. Recording
    /// the body's type (never the body) is load-bearing: inference must
    /// produce types, so saturated uses can never claim `T : T`.
    fn check_decl_infer(
        &mut self,
        name: String,
        params: Vec<(String, SExpr)>,
        body: SExpr,
        ckpt: Checkpoint,
    ) {
        let gmap = self.globals_map();
        // Snapshot the failed flags: `Scope` borrows them, and the loop
        // below needs `&mut self` on failure paths. The flags cannot change
        // mid-definition (no def completes while scoping this one), so the
        // snapshot is exact.
        let failed_snapshot = self.failed.clone();
        let mut scope = Scope {
            locals: Vec::new(),
            globals: &gmap,
            failed: &failed_snapshot,
            wild_counter: self.wild_counter,
            holes: Cell::new(self.hole_supply.get()),
        };
        let fail = |this: &mut Self, scope: &Scope, msg: String| {
            this.wild_counter = scope.wild_counter;
            this.hole_supply.set(scope.holes.get());
            this.urollback(ckpt);
            this.push_failed(
                name.clone(),
                Core::Sort(Sort::Star),
                Core::Sort(Sort::Star),
                msg,
            );
        };
        let mut ctx = Ctx::default();
        let mut dom_cores: Vec<Core> = Vec::new();
        let mut names: Vec<String> = Vec::new();
        for (pname, pty) in &params {
            let dom_c = match scope_expr(&mut scope, pty) {
                Ok(c) => c,
                Err(e) => {
                    fail(self, &scope, format!("in telescope binder '{pname}': {e}"));
                    return;
                }
            };
            let dom_v = match self.check_ty(&dom_c, &ctx) {
                Ok(v) => v,
                Err(e) => {
                    fail(self, &scope, format!("in telescope binder '{pname}' evaluation: {e}"));
                    return;
                }
            };
            if let Err(e) = self.is_type_value(&dom_v, &ctx) {
                fail(self, &scope, format!("telescope binder '{pname}' is not a type: {e}"));
                return;
            }
            // Same binder treatment as lambdas (shadowing allowed, `_` fresh).
            let internal = if pname == "_" {
                fresh_wild(&mut scope.wild_counter)
            } else {
                pname.clone()
            };
            scope.locals.push(internal.clone());
            ctx.push(dom_v, Value::Var(ctx.len()));
            dom_cores.push(dom_c);
            names.push(internal);
        }
        let body_c = match scope_expr(&mut scope, &body) {
            Ok(c) => c,
            Err(e) => {
                fail(self, &scope, format!("in codomain body: {e}"));
                return;
            }
        };
        self.wild_counter = scope.wild_counter;
        self.hole_supply.set(scope.holes.get());
        // The body's TYPE is the codomain — never the body itself. Recording
        // the body would file a value as a type, so every saturated use would
        // claim `T : T` for whatever the body denotes (the `bigalias Void :
        // Void` confusion: inference must produce types, and only types).
        // Inferring here also checks the body like any term (lets,
        // ascriptions, arguments — nothing rides along unchecked).
        let body_ty = match self.infer(&body_c, &ctx) {
            Ok(v) => v,
            Err(e) => {
                self.urollback(ckpt);
                self.push_failed(name, Core::Sort(Sort::Star), body_c, format!("in inferred codomain body: {e}"));
                return;
            }
        };
        let mut fuel_body = FUEL_LIMIT;
        match whnf(&body_ty, &self.gvals, &mut fuel_body) {
            Ok(Value::Sort(_)) => {}
            Ok(other) => {
                self.urollback(ckpt);
                self.push_failed(
                    name,
                    Core::Sort(Sort::Star),
                    body_c,
                    format!(
                        "inferred codomain is not a type: body has type {}",
                        pretty_value(&other, ctx.len(), &self.gvals, &self.gnames),
                    ),
                );
                return;
            }
            Err(e) => {
                self.urollback(ckpt);
                self.push_failed(name, Core::Sort(Sort::Star), body_c, format!("inferred codomain whnf failed: {e}"));
                return;
            }
        }
        // Quote the inferred type back under the telescope (same de Bruijn
        // convention as the scoped body: level `l` is `Bound(N - 1 - l)`).
        let mut fuel_q = FUEL_LIMIT;
        let body_ty_c = match crate::core::quote(ctx.len(), &body_ty, &self.gvals, &mut fuel_q, 0) {
            Ok(c) => c,
            Err(e) => {
                self.urollback(ckpt);
                self.push_failed(name, Core::Sort(Sort::Star), body_c, format!("inferred codomain quote failed: {e}"));
                return;
            }
        };
        // Close the telescope over the body's TYPE two ways: the Pi chain
        // core (the recorded *type*, evaluated like an annotation — domains
        // are closed under their prefixes; codomains stay closures until
        // applied), and the Lam chain core over the body itself (the recorded
        // *value*). The value must be lambda-headed, not the type itself:
        // uses apply the global (`is_center T v i`), and only a Lam
        // beta-reduces through `do_apply` — a Pi-headed value would get stuck
        // as `App(Pi, …)`, making every applied use ill-typed. (Ordinary defs
        // get this for free, since their bodies elaborate as terms.)
        let mut ty_core = body_ty_c;
        let mut lam_core = body_c.clone();
        for (dom_c, internal) in dom_cores.into_iter().rev().zip(names.into_iter().rev()) {
            ty_core = Core::Pi { name: display_name(&internal), dom: Box::new(dom_c), cod: Box::new(ty_core) };
            lam_core = Core::Lam { name: display_name(&internal), body: Box::new(lam_core) };
        }
        let empty: Env = Vec::new();
        let ty_v = match eval(&ty_core, &empty, &self.gvals) {
            Ok(v) => v,
            Err(e) => {
                self.urollback(ckpt);
                self.push_failed(name, ty_core, body_c, format!("in codomain evaluation: {e}"));
                return;
            }
        };
        // Formation gate: the closed-over body must be a type (in a sort).
        // This rejects term-bodies and pins universe levels, like checking
        // an annotation — the difference from `def` is only that no value
        // is checked (there is no term; the type is the whole content).
        if let Err(e) = self.is_type_value(&ty_v, &Ctx::default()) {
            self.urollback(ckpt);
            self.push_failed(name, ty_core, body_c, format!("inferred codomain is not a type: {e}"));
            return;
        }
        // Shared tail with the plain flow (drain, sweep, cycle-check, zonk,
        // leak check, record) — with the type as its own value, like any
        // type-former definition (`Bool`, `Nat`, ...).
        match self.drain_postponed() {
            Ok(()) => {}
            Err(e) => {
                self.urollback(ckpt);
                self.push_failed(name, ty_core, body_c, format!("{e}"));
                return;
            }
        }
        if let Err(e) = self.unsolved_holes() {
            self.urollback(ckpt);
            self.push_failed(name, ty_core, body_c, format!("{e}"));
            return;
        }
        if let Err(e) = self.ucheck() {
            self.urollback(ckpt);
            self.push_failed(name, ty_core, body_c, format!("universe inconsistency: {e}"));
            return;
        }
        let ty_v = match self.zonk_value(&ty_v) {
            Ok(v) => v,
            Err(e) => {
                self.urollback(ckpt);
                self.push_failed(name, ty_core, body_c, format!("internal error (zonk type): {e}"));
                return;
            }
        };
        if self.meta_leak(&ty_v) {
            self.urollback(ckpt);
            self.push_failed(
                name,
                ty_core,
                body_c,
                "internal error (unsolved metavariable leaked into recorded globals — please report)".to_string(),
            );
            return;
        }
        let mut vars: Vec<u32> = Vec::new();
        level_vars_value(&ty_v, &mut vars);
        // Quantify constraint-only variables as well (see the plain flow:
        // unquantified ids leak bounds across instantiations).
        let retained = self.ucons.borrow()[ckpt.ucons..].to_vec();
        for c in &retained {
            level_vars_constraint(c, &mut vars);
        }
        let scheme = Scheme { vars, constraints: retained };
        // The recorded value is the lambda-wrapped body (beta-reducible on
        // use); its level variables ride the same scheme (collected from the
        // type above — the value mentions no new ones by construction, since
        // it is the type's own body re-scoped).
        let lam_v = match eval(&lam_core, &empty, &self.gvals) {
            Ok(v) => v,
            Err(e) => {
                self.urollback(ckpt);
                self.push_failed(name, ty_core, body_c, format!("in codomain value evaluation: {e}"));
                return;
            }
        };
        let lam_v = match self.zonk_value(&lam_v) {
            Ok(v) => v,
            Err(e) => {
                self.urollback(ckpt);
                self.push_failed(name, ty_core, body_c, format!("internal error (zonk value): {e}"));
                return;
            }
        };
        if self.meta_leak(&lam_v) {
            self.urollback(ckpt);
            self.push_failed(
                name,
                ty_core,
                body_c,
                "internal error (unsolved metavariable leaked into recorded globals — please report)".to_string(),
            );
            return;
        }
        self.gnames.push(name.clone());
        self.gtypes.push(Some(ty_v));
        self.gvals.push(Some(GlobalDef { value: lam_v, levels: scheme.vars.clone() }));
        self.gschemes.push(scheme);
        self.failed.push(false);
        self.decls.push(Decl { name, ty: ty_core, val: lam_core, ok: true, error: None });
    }

    // -- sorts --------------------------------------------------------------

    /// Sort `s` such that `ty : s` (axioms: `* : Type0`, levels step upward).
    /// Validation runs first: `check_ty` rejects unchecked junk (`let`s with
    /// false bindings, bogus ascriptions) hiding inside canonical type
    /// constructors, which plain evaluation would silently unfold.
    fn infer_sort(&self, ty: &Core, ctx: &Ctx) -> Result<Sort, CheckError> {
        let ty_v = self.check_ty(ty, ctx)?;
        self.infer_sort_value(&ty_v, ctx)
    }

    /// Validate a type core and return its value. `let` bindings are checked
    /// (annotated against the annotation, unannotated inferred) and
    /// ascriptions verified — evaluation alone would accept false ones, since
    /// it never checks what it unfolds. Canonical constructors (`Pi`,
    /// `Sigma`, `Either`, `Quotient`, `Fst`, `Snd`) recurse
    /// structurally (binders extend the context like lambda checking);
    /// everything else evaluates directly (neutrals re-infer through
    /// `is_type_value` at the caller, so their insides are checked there;
    /// non-types are rejected there too).
    fn check_ty(&self, ty: &Core, ctx: &Ctx) -> Result<Value, CheckError> {
        match ty {
            Core::Let { ann, val, body, .. } => {
                let ann_v: Value = match ann {
                    Some(a) => {
                        let av = self.check_ty(a, ctx)?;
                        self.is_type_value(&av, ctx)?;
                        self.check(val, &av, ctx)?;
                        av
                    }
                    None => self.infer(val, ctx)?,
                };
                let val_v = eval(val, &ctx.values, &self.gvals)?;
                let mut ctx2 = ctx.clone();
                ctx2.push(ann_v, val_v);
                self.check_ty(body, &ctx2)
            }
            Core::Ann(e, t) => {
                let t_v = self.check_ty(t, ctx)?;
                self.is_type_value(&t_v, ctx)?;
                self.check(e, &t_v, ctx)?;
                self.check_ty(e, ctx)
            }
            Core::Pi { dom, cod, .. } | Core::Sigma { dom, cod, .. } => {
                let dom_v = self.check_ty(dom, ctx)?;
                let mut ctx2 = ctx.clone();
                let fresh_ix = ctx2.len();
                ctx2.push(dom_v, Value::Var(fresh_ix));
                self.check_ty(cod, &ctx2)?;
                eval(ty, &ctx.values, &self.gvals).map_err(CheckError::from)
            }
            Core::Either(a, b) | Core::Quotient(a, b) => {
                self.check_ty(a, ctx)?;
                self.check_ty(b, ctx)?;
                eval(ty, &ctx.values, &self.gvals).map_err(CheckError::from)
            }
            Core::Fst(p) | Core::Snd(p) => {
                self.check_ty(p, ctx)?;
                eval(ty, &ctx.values, &self.gvals).map_err(CheckError::from)
            }
            _ => eval(ty, &ctx.values, &self.gvals).map_err(CheckError::from),
        }
    }

    fn infer_sort_value(&self, v: &Value, ctx: &Ctx) -> Result<Sort, CheckError> {
        let mut fuel = FUEL_LIMIT;
        let w = whnf(v, &self.gvals, &mut fuel)?;
        match w {
            // Axioms: `* : Type0`; `Type(n) : Type(n+1)`; `Type(?a)` gets a
            // fresh successor with `?a < ?m` (no symbolic successors).
            Value::Sort(Sort::Star) => Ok(Sort::Type(Level::Const(0))),
            Value::Sort(Sort::Type(Level::Const(n))) => Ok(Sort::Type(Level::Const(
                n.checked_add(1).ok_or_else(|| CheckError::new("universe level overflow".to_string()))?,
            ))),
            Value::Sort(Sort::Type(Level::Var(a))) => {
                let m = Level::Var(fresh_level_var());
                self.urecord(Constraint::new(Level::Var(a), Rel::Lt, m));
                Ok(Sort::Type(m))
            }
            // `Void : *` (empty type, small — explosion targets `*`-types).
            Value::Void => Ok(Sort::Star),
            // `Unit : *` (one-element type, small).
            Value::Unit => Ok(Sort::Star),
            Value::Pi { dom, cod, .. } => {
                // Formation: the domain's sort and the codomain's sort feed
                // `pi_sort` (impredicative into `*`, predicative `max`
                // otherwise — see the rule above).
                let sdom = self.infer_sort_value(&dom, ctx)?;
                let mut ctx2 = ctx.clone();
                let fresh_ix = ctx2.len();
                let fresh_val = Value::Var(fresh_ix);
                ctx2.push((*dom).clone(), fresh_val.clone());
                let cod_v = cod.apply(fresh_val, &self.gvals)?;
                let scod = self.infer_sort_value(&cod_v, &ctx2)?;
                Ok(self.pi_sort(&sdom, &scod))
            }
            Value::Sigma { dom, cod, .. } => {
                // PREDICATIVE formation (the cautious choice — see the header
                // notes): Sigma lives at the LARGER of its parts (fresh
                // variable with bounds when variables are involved).
                let i = self.infer_sort_value(&dom, ctx)?;
                let mut ctx2 = ctx.clone();
                let fresh_ix = ctx2.len();
                let fresh_val = Value::Var(fresh_ix);
                ctx2.push((*dom).clone(), fresh_val.clone());
                let cod_v = cod.apply(fresh_val, &self.gvals)?;
                let j = self.infer_sort_value(&cod_v, &ctx2)?;
                Ok(self.predicative_max(&i, &j))
            }
            Value::Either(a, b) => {
                // Predicative, like Sigma: the larger side wins. (An
                // impredicative sum with case analysis projecting the content
                // out is the same paradox lever as impredicative Sigma.)
                let i = self.infer_sort_value(&a, ctx)?;
                let j = self.infer_sort_value(&b, ctx)?;
                Ok(self.predicative_max(&i, &j))
            }
            Value::Quotient(a, r) => {
                // Predicative, like sums: the quotient lives at the max of
                // its carrier's level and its relation's codomain level
                // (`quotient_cod_sort` validates the `A -> A -> Type _`
                // shape along the way — uniform for lambdas and neutrals).
                let i = self.infer_sort_value(&a, ctx)?;
                let j = self.quotient_cod_sort(&r, &a, ctx)?;
                Ok(self.predicative_max(&i, &j))
            }
            Value::Var(_) | Value::Global(_, _) | Value::App(_, _)
            | Value::Match { .. } | Value::Meta { .. } => {
                // Neutral type: quote back to core and infer; its type must
                // be a sort (lets in types work: `eval` unfolded them above).
                // (A stuck `Match` in type position lands here too: quoted
                // back and inferred through `infer_match`. A `Meta` quotes to
                // its hole, whose elaboration resolves the same id.)
                let mut fuel2 = FUEL_LIMIT;
                let c = crate::core::quote(ctx.len(), &w, &self.gvals, &mut fuel2, 0)?;
                let tty = self.infer(&c, ctx)?;
                let mut fuel3 = FUEL_LIMIT;
                match whnf(&tty, &self.gvals, &mut fuel3)? {
                    Value::Sort(s) => Ok(s),
                    other => Err(CheckError::new(format!(
                        "expected a type (in `*` or a `Type` level), got {} : {}",
                        pretty_value(&w, ctx.len(), &self.gvals, &self.gnames),
                        pretty_value(&other, ctx.len(), &self.gvals, &self.gnames),
                    ))),
                }
            }
            Value::Lam { .. } | Value::Absurd | Value::SigRect | Value::EitherRect | Value::UnitRect | Value::W | Value::Sup | Value::WRect | Value::QuotLift | Value::QuotInd | Value::QuotSound => Err(CheckError::new(format!(
                "term {} is a function, not a type",
                pretty_value(v, ctx.len(), &self.gvals, &self.gnames),
            ))),
            // Introductions and projections are terms, never types (`inl`/`inr`/
            // `()`/`quot_mk`/`(a, b)`/`fst`/`snd` values can only appear in
            // type positions via unfolding, which `whnf` handles before this
            // match — reaching here means stuck; use `and` for product types).
            Value::Inl(_) | Value::Inr(_) | Value::Pt | Value::QuotMk(_)
            | Value::Pair(_, _) | Value::Fst(_) | Value::Snd(_) => Err(CheckError::new(format!(
                "term {} is a value, not a type",
                pretty_value(v, ctx.len(), &self.gvals, &self.gnames),
            ))),
        }
    }

    fn is_type_value(&self, v: &Value, ctx: &Ctx) -> Result<Sort, CheckError> {
        // Annotation positions accept types-in-sorts AND sorts themselves:
        // any sort literal annotates the types in it (this grants no type to
        // the sort — values checked against it still go through `infer_sort`,
        // which axioms each sort upward).
        let mut fuel = FUEL_LIMIT;
        if let Ok(Value::Sort(s)) = whnf(v, &self.gvals, &mut fuel) {
            return Ok(s);
        }
        self.infer_sort_value(v, ctx)
    }

    // -- universe levels ----------------------------------------------------

    fn urecord(&self, c: Constraint) {
        self.ucons.borrow_mut().push(c);
    }

    /// Cycle-check the accumulated constraints (called at each successful def
    /// end; the store is monotone, so checking the whole prefix is sound).
    fn ucheck(&self) -> Result<(), CheckError> {
        check_satisfiable(&self.ucons.borrow()).map_err(CheckError::new)
    }

    /// Subsumption on sorts: `actual <= expected` (a type in `actual` is also
    /// usable in `expected`). `*` lifts anywhere for free; concrete levels
    /// compare directly; anything else records a single-direction `<=`
    /// constraint. A `Type` side never fits in `*` (no downward lifting).
    fn require_sort_le(&self, actual: &Sort, expected: &Sort) -> Result<(), CheckError> {
        match (actual, expected) {
            (Sort::Star, _) => Ok(()),
            (Sort::Type(a), Sort::Type(b)) if a == b => Ok(()),
            (Sort::Type(Level::Const(m)), Sort::Type(Level::Const(n))) => {
                if m <= n {
                    Ok(())
                } else {
                    Err(CheckError::new(format!(
                        "{actual} does not fit in {expected} (large type in small universe)"
                    )))
                }
            }
            (Sort::Type(a), Sort::Type(b)) => {
                self.urecord(Constraint::new(*a, Rel::Le, *b));
                Ok(())
            }
            (Sort::Type(_), Sort::Star) => Err(CheckError::new(format!(
                "{actual} does not fit in * (large type in small universe)"
            ))),
        }
    }

    /// Predicative maximum of two sorts (Sigma/Either formation): both
    /// small stays small; `*` is the identity (no constraint); concrete
    /// levels compute directly; anything else mints a fresh variable bounded
    /// below by both sides. (No symbolic `max` nodes anywhere.)
    fn predicative_max(&self, x: &Sort, y: &Sort) -> Sort {
        match (x, y) {
            (Sort::Star, Sort::Star) => Sort::Star,
            (Sort::Star, s) => *s,
            (s, Sort::Star) => *s,
            (Sort::Type(Level::Const(m)), Sort::Type(Level::Const(n))) => {
                Sort::Type(Level::Const(*m.max(n)))
            }
            (Sort::Type(a), Sort::Type(b)) => {
                let w = Level::Var(fresh_level_var());
                self.urecord(Constraint::new(*a, Rel::Le, w));
                self.urecord(Constraint::new(*b, Rel::Le, w));
                Sort::Type(w)
            }
        }
    }

    /// Pi sort: impredicative into `*` (any domain level — ECC's
    /// `(Type_i, Prop) -> Prop`, which keeps Leibniz `path` in `*` for data
    /// at any level), otherwise the predicative maximum.
    fn pi_sort(&self, sdom: &Sort, scod: &Sort) -> Sort {
        if *scod == Sort::Star {
            Sort::Star
        } else {
            self.predicative_max(sdom, scod)
        }
    }

    /// The type `W : (A:Type(?a)) -> (B:(A -> Type(?b))) -> Type(?m)` with
    /// `?a, ?b <= ?m`. The only primitive whose result level must bound its
    /// inputs (formation), so the only hand-built type recording constraints
    /// — hence a method, minting fresh variables per `infer` call.
    fn w_type(&self) -> Value {
        let la = Level::Var(fresh_level_var());
        let lb = Level::Var(fresh_level_var());
        let lm = Level::Var(fresh_level_var());
        self.urecord(Constraint::new(la, Rel::Le, lm));
        self.urecord(Constraint::new(lb, Rel::Le, lm));
        Value::Pi {
            name: "A".to_string(),
            dom: Box::new(Value::Sort(Sort::Type(la))),
            cod: Closure::new(
                Vec::new(),
                Core::Pi {
                    name: "B".to_string(),
                    dom: Box::new(Core::Pi {
                        name: "_".to_string(),
                        dom: Box::new(Core::Bound(0)),
                        cod: Box::new(Core::Sort(Sort::Type(lb))),
                    }),
                    cod: Box::new(Core::Sort(Sort::Type(lm))),
                },
            ),
        }
    }

    /// Validate a quotient relation and return its codomain level: `R` must
    /// check against `A -> A -> Type _` (lambdas via introduction, neutrals
    /// via inference+conversion), and the level is the sort of `R x y` for
    /// fresh `x y : A`. No index shifting anywhere: the nested Pi is built
    /// from values (level-stable) with the inner domain quoted one level
    /// longer (quoting the same value longer shifts indices correctly).
    fn quotient_cod_sort(&self, r_v: &Value, a_v: &Value, ctx: &Ctx) -> Result<Sort, CheckError> {
        // Shape: `R : A -> A -> (some type)`.
        let mut ctx2 = ctx.clone();
        let x1 = Value::Var(ctx2.len());
        ctx2.push(a_v.clone(), x1);
        let mut fq = FUEL_LIMIT;
        let a_c = crate::core::quote(ctx2.len(), a_v, &self.gvals, &mut fq, 0)?;
        let rel_ty = Value::Pi {
            name: "_".to_string(),
            dom: Box::new(a_v.clone()),
            cod: Closure::new(
                ctx.values.clone(),
                Core::Pi {
                    name: "_".to_string(),
                    dom: Box::new(a_c),
                    cod: Box::new(fresh_sort()),
                },
            ),
        };
        let mut fq2 = FUEL_LIMIT;
        // Scoped for the EXTENDED context (quoting the same value longer
        // shifts indices correctly — off-by-push trap), and checked there.
        let r_c = crate::core::quote(ctx2.len(), r_v, &self.gvals, &mut fq2, 0)?;
        self.check(&r_c, &rel_ty, &ctx2).map_err(|e| {
            CheckError::new(format!(
                "quotient relation must be a binary family on the carrier (R : A -> A -> Type _): {e}"
            ))
        })?;
        // Level: sort of `R x y` (beta-reduces now for lambdas, stuck neutral
        // otherwise — either way a type, whose sort is the relation's level).
        let rapp1 = Core::app(r_c, Core::Bound(0));
        let rx1 = eval(&rapp1, &ctx2.values, &self.gvals)?;
        let mut ctx3 = ctx2.clone();
        let x2 = Value::Var(ctx3.len());
        ctx3.push(a_v.clone(), x2);
        let mut fq3 = FUEL_LIMIT;
        let rx1c = crate::core::quote(ctx3.len(), &rx1, &self.gvals, &mut fq3, 0)?;
        let rapp2 = Core::app(rx1c, Core::Bound(0));
        let rxy = eval(&rapp2, &ctx3.values, &self.gvals)?;
        self.infer_sort_value(&rxy, &ctx3)
    }

    // -- inference ----------------------------------------------------------

    fn infer(&self, term: &Core, ctx: &Ctx) -> Result<Value, CheckError> {
        match term {
            Core::Bound(ix) => {
                if *ix >= ctx.len() {
                    return Err(CheckError::new(format!("stuck de Bruijn index {ix}")));
                }
                Ok(ctx.types[ctx.len() - 1 - ix].clone())
            }
            Core::Global(g, inst) => {
                if self.failed.get(*g).copied().unwrap_or(true) {
                    let nm = self.gnames.get(*g).cloned().unwrap_or_else(|| format!("g{g}"));
                    return Err(CheckError::new(format!("reference to failed/unknown definition '{nm}'")));
                }
                let scheme = self.gschemes.get(*g).cloned().unwrap_or_default();
                if scheme.arity() != inst.len() {
                    return Err(CheckError::new(format!(
                        "global g{g} takes {} universe levels, got {} (stale reference — please report)",
                        scheme.arity(),
                        inst.len(),
                    )));
                }
                // Instantiate: substitute the instance for scheme variables in
                // the stored type, and re-add the retained constraints
                // (substituted) — this use varies independently of all others.
                let map: HashMap<u32, Level> = scheme
                    .vars
                    .iter()
                    .copied()
                    .zip(inst.iter().copied())
                    .collect();
                for c in &scheme.constraints {
                    self.urecord(subst_level_constraint(c, &map));
                }
                self.gtypes
                    .get(*g)
                    .and_then(|o| o.clone())
                    .map(|ty| subst_level_value(&ty, &map))
                    .ok_or_else(|| CheckError::new(format!("unknown global g{g}")))
            }
            Core::Sort(Sort::Star) => Ok(Value::Sort(Sort::Type(Level::Const(0)))), // `* : Type0`
            // Every level has a type one up (axioms live in `infer_sort_value`
            // on values; here on syntax the concrete successor is direct).
            Core::Sort(Sort::Type(Level::Const(n))) => Ok(Value::Sort(Sort::Type(Level::Const(
                n.checked_add(1).ok_or_else(|| CheckError::new("universe level overflow".to_string()))?,
            )))),
            Core::Sort(Sort::Type(Level::Var(a))) => {
                // `Type(?a)` as a term: fresh successor with `?a < ?m`.
                let m = Level::Var(fresh_level_var());
                self.urecord(Constraint::new(Level::Var(*a), Rel::Lt, m));
                Ok(Value::Sort(Sort::Type(m)))
            }
            Core::Void => Ok(Value::Sort(Sort::Star)), // `Void : *`
            // Primitive vacuous eliminator (underivable — no case to split).
            Core::Absurd => Ok(absurd_type()),
            // Primitive dependent eliminator (see `sig_rect_type`).
            Core::SigRect => Ok(sig_rect_type()?),
            Core::Unit => Ok(Value::Sort(Sort::Star)), // `Unit : *`
            // `()` infers unambiguously (no parameters, unlike pairs/sums).
            Core::Pt => Ok(Value::Unit),
            // Primitive unit eliminator (see `unit_rect_type`).
            Core::UnitRect => Ok(unit_rect_type()?),
            // `W : (A:*) -> (B:(A -> *)) -> *` (closed hand value).
            Core::W => Ok(self.w_type()),
            // Primitive W introduction / elimination (see below).
            Core::Sup => Ok(sup_type()?),
            Core::WRect => Ok(w_rect_type()?),
            Core::Either { .. } => {
                // `infer_sort` already validated well-formedness; the
                // Either's type is its (predicative) formation sort.
                let s = self.infer_sort(term, ctx)?;
                Ok(Value::Sort(s))
            }
            Core::Quotient { .. } => {
                // Same: the quotient's type is its (predicative) formation
                // sort (`infer_sort` validated carrier, relation shape, max).
                let s = self.infer_sort(term, ctx)?;
                Ok(Value::Sort(s))
            }
            Core::QuotMk(_) => Err(CheckError::new(format!(
                "cannot infer type of {}: `quot_mk` needs a known quotient type — \
                 annotate it (e.g. `(quot_mk a : Q)`)",
                pretty_core(term, &self.gnames),
            ))),
            // Primitive quotient eliminators (see `quot_lift_type` etc.).
            Core::QuotLift => Ok(quot_lift_type()?),
            Core::QuotInd => Ok(quot_ind_type()?),
            // Soundness axiom (stuck-neutral primitive, like `Absurd`).
            Core::QuotSound => Ok(quot_sound_type()?),
            Core::Inl(_) | Core::Inr(_) => Err(CheckError::new(format!(
                "cannot infer type of {}: `inl`/`inr` need a known sum type — \
                 annotate it (e.g. `(inl a : S)` or `let X : S = inl a in ...`)",
                pretty_core(term, &self.gnames),
            ))),
            // Primitive sum eliminator (see `either_rect_type`).
            Core::EitherRect => Ok(either_rect_type()?),
            Core::Pi { .. } => {
                // `infer_sort` already validated well-formedness; the Pi's
                // type is the sort it computed.
                let s = self.infer_sort(term, ctx)?;
                Ok(Value::Sort(s))
            }
            Core::Sigma { .. } => {
                // Same: the Sigma's type is its (predicative) formation sort.
                let s = self.infer_sort(term, ctx)?;
                Ok(Value::Sort(s))
            }
            Core::Pair(_, _) => Err(CheckError::new(format!(
                "cannot infer type of {}: `(a, b)` is a pair value only \
                 (use `and` for product types) — annotate it \
                 (e.g. `((a, b) : S)` or `let X : S = (a, b) in ...`)",
                pretty_core(term, &self.gnames),
            ))),
            Core::Fst(p) => self.infer_fst(p, ctx),
            Core::Snd(p) => self.infer_snd(p, ctx),
            Core::Match { scrut, motive, l_name: _, l_body, r_name: _, r_body, .. } => {
                self.infer_match(scrut, motive, l_body, r_body, ctx)
            }
            Core::Lam { .. } => Err(CheckError::new(format!(
                "cannot infer type of {} (lambda needs an annotation)",
                pretty_core(term, &self.gnames),
            ))),
            Core::Hole { id, span } => {
                // Re-encounter (e.g. quote-then-infer of a type containing an
                // elaborated hole): resolve the same unknown, whose recorded
                // type is the answer. First contact in infer position has no
                // expected type to synthesize from — annotate it. (An entry
                // with unknown type comes from lazy unify contact; inferring
                // through it would fabricate a type, so that errors too.)
                match self.metas.borrow().get(*id as usize).and_then(|o| o.as_ref()).and_then(|e| e.ty.clone()) {
                    Some(ty) => Ok(ty),
                    None => Err(CheckError::new(format!(
                        "cannot infer type of `_` (at {}) — annotate it (the elaborator can only fill holes against a known expected type)",
                        self.hole_loc(*span),
                    ))),
                }
            }
            Core::App(f, a) => {
                // Full `W A B` spine: the result level computes from the
                // actuals (predicative max, concrete when they are), not from
                // the floating `w_type` variable (which only lower-bounds).
                if let Some(ty) = self.infer_w_app(f, a, ctx)? {
                    return Ok(ty);
                }
                let fty = self.infer(f, ctx)?;
                let mut fuel = FUEL_LIMIT;
                let w = whnf(&fty, &self.gvals, &mut fuel)?;
                match w {
                    Value::Pi { dom, cod, .. } => {
                        let checker = self;
                        checker.check(a, &dom, ctx)?;
                        let av = eval(a, &ctx.values, &self.gvals)?;
                        let cod_v = cod.apply(av, &self.gvals)?;
                        // WHNF immediately so dependent codomains like
                        // `motive x` beta-reduce before use.
                        let mut fuel2 = FUEL_LIMIT;
                        Ok(whnf(&cod_v, &self.gvals, &mut fuel2)?)
                    }
                    other => Err(CheckError::new(format!(
                        "head {} has non-function type {} (in application {})",
                        pretty_core(f, &self.gnames),
                        pretty_value(&other, ctx.len(), &self.gvals, &self.gnames),
                        pretty_core(term, &self.gnames),
                    ))),
                }
            }
            Core::Let { name: _, ann, val, body } => {
                let mut ctx2 = ctx.clone();
                // `let x : A = v in b`: check `A`, check `v` against it.
                // `let x = v in b`: infer `v`'s type and use it.
        let ann_v: Value = match ann {
            Some(a) => {
                let av = self.check_ty(a, ctx)?;
                self.is_type_value(&av, ctx)?;
                self.check(val, &av, ctx)?;
                av
            }
            None => self.infer(val, ctx)?,
        };
                let val_v = eval(val, &ctx.values, &self.gvals)?;
                ctx2.push(ann_v, val_v);
                // Body is checked under one more binder; infer it with
                // shifted core? `body` is already under the binder (indices).
                // Evaluate types with ctx2 values. For inference we need a
                // `&Core` that sees the extended context: `body` does (its
                // free `Bound(0)` is our new var). So infer directly.
                self.infer_under(body, &ctx2)
            }
            Core::Ann(e, t) => {
                let t_v = self.check_ty(t, ctx)?;
                self.is_type_value(&t_v, ctx)?;
                self.check(e, &t_v, ctx)?;
                Ok(t_v)
            }
        }
    }

    /// `infer` for a term that lives under an already-extended `ctx`.
    fn infer_under(&self, term: &Core, ctx: &Ctx) -> Result<Value, CheckError> {
        // Same as `infer` but the context is already extended. Since `infer`
        // takes `ctx` explicitly, this is just an alias for clarity.
        self.infer(term, ctx)
    }

    /// Infer the type of a dependent `match`: the motive applied to the
    /// scrutinee. Branches are checked against the motive applied to the
    /// constructor patterns; when the scrutinee is a *variable*, the branch
    /// contexts are additionally refined by substituting the pattern
    /// (first-order and total — see `subst.rs`), so hypotheses mentioning
    /// the scrutinee follow the split. Non-variable scrutinees elaborate
    /// plainly (motive + branches, like the eliminator — sound, just with
    /// no refinement to give).
    fn infer_match(
        &self,
        scrut: &Core,
        motive: &Core,
        l_body: &Core,
        r_body: &Core,
        ctx: &Ctx,
    ) -> Result<Value, CheckError> {
        // Scrutinee type must unfold to a sum (open scrutinees welcome —
        // stuck is fine; only non-sums are rejected).
        let sty = self.infer(scrut, ctx)?;
        let mut fuel = FUEL_LIMIT;
        let (dom_a, dom_b) = match whnf(&sty, &self.gvals, &mut fuel)? {
            Value::Either(a, b) => ((*a).clone(), (*b).clone()),
            other => {
                return Err(CheckError::new(format!(
                    "match scrutinee {} has non-sum type {}",
                    pretty_core(scrut, &self.gnames),
                    pretty_value(&other, ctx.len(), &self.gvals, &self.gnames),
                )));
            }
        };
        // Motive must be a family over the sum at hand, into any level
        // (motives are level-general; formation computes the max).
        let sum_v = Value::Either(Box::new(dom_a.clone()), Box::new(dom_b.clone()));
        let mot_pi = Value::Pi {
            name: "_".to_string(),
            dom: Box::new(sum_v),
            cod: Closure::new(ctx.values.clone(), fresh_sort()),
        };
        self.check(motive, &mot_pi, ctx)?;
        // Scrutinee level, if it is a plain variable (refinement needs a
        // variable to substitute; anything else elaborates plainly).
        let scrut_lvl: Option<usize> = match scrut {
            Core::Bound(ix) => {
                if *ix >= ctx.len() {
                    return Err(CheckError::new(format!("stuck de Bruijn index {ix}")));
                }
                Some(ctx.len() - 1 - ix)
            }
            _ => None,
        };
        // Left branch against `P (inl a)`, right against `P (inr b)`.
        self.check_match_branch(scrut_lvl, true, &dom_a, l_body, motive, ctx)?;
        self.check_match_branch(scrut_lvl, false, &dom_b, r_body, motive, ctx)?;
        // Result: motive applied to the scrutinee (beta-reduces itself when
        // the motive is a lambda; stuck-neutral otherwise — both fine).
        eval(
            &Core::app(motive.clone(), scrut.clone()),
            &ctx.values,
            &self.gvals,
        )
        .map_err(CheckError::from)
    }

    /// Check one match branch in a possibly-refined context: clone the
    /// context, substitute the constructor pattern for the scrutinee level
    /// (if any — see `infer_match`), push the pattern-binder entry, and
    /// check the body against the motive applied to the pattern.
    fn check_match_branch(
        &self,
        scrut_lvl: Option<usize>,
        is_left: bool,
        part_ty: &Value,
        body: &Core,
        motive: &Core,
        ctx: &Ctx,
    ) -> Result<(), CheckError> {
        let mut ext = ctx.clone();
        // Fresh pattern level on top (append-only: existing levels stable).
        let lf = ext.len();
        // Refinement first (needs `lf` known, entries still unextended).
        if let Some(lx) = scrut_lvl {
            for ty in ext.types.iter_mut() {
                *ty = subst_val(ty, lx, lf, is_left);
            }
            for vv in ext.values.iter_mut() {
                *vv = subst_val(vv, lx, lf, is_left);
            }
        }
        // Injection-shaped scrutinee value (what the scrutinee refined to);
        // the pattern *binder* below denotes the payload itself.
        let pat_val = if is_left {
            Value::Inl(Box::new(Value::Var(lf)))
        } else {
            Value::Inr(Box::new(Value::Var(lf)))
        };
        // The binder itself denotes the *payload* (neutral `Var(lf)`); the
        // injection-shaped `pat_val` is what the *scrutinee* refined to — it
        // belongs in substituted entries and the goal below, not here.
        // (Pushing the injection as the binder's value would double-wrap:
        // `f a` would infer through `P (inl (inl a))` instead of `P (inl a)`.)
        ext.push(part_ty.clone(), Value::Var(lf));
        // Goal: motive applied to the pattern. The motive core is scoped for
        // the UNEXTENDED context, so evaluate it there and apply the value
        // to the pattern: evaluating `P (inl a)`-core in the extended env
        // would misread `P`'s indices (off-by-push — every motive variable
        // would point one entry too deep). Closure application carries the
        // captured environment, so it stays correct; neutral motives apply
        // structurally (no indices involved either way).
        let mot_v = eval(motive, &ctx.values, &self.gvals)?;
        let goal = match mot_v {
            Value::Lam { body, .. } => body.apply(pat_val, &self.gvals)?,
            neutral => Value::App(Box::new(neutral), Box::new(pat_val)),
        };
        self.check(body, &goal, &ext)
    }

    /// Type of `fst p`: the Sigma's domain. Two cases:
    /// (i) `p` is syntactically a pair (avoids the ambiguity error);
    /// (ii) `p`'s type unfolds to a Sigma (ordinary term-level).
    /// Deliberately NO case for sort-typed `p`: pairs are values only, so
    /// projecting a type is always an error.
    fn infer_fst(&self, p: &Core, ctx: &Ctx) -> Result<Value, CheckError> {
        if let Core::Pair(a, _) = p {
            // `fst (a, b)` has the type of `a` (pairs bind nothing, so no
            // substitution is needed).
            return self.infer(a, ctx);
        }
        let pty = self.infer(p, ctx)?;
        let mut fuel = FUEL_LIMIT;
        match whnf(&pty, &self.gvals, &mut fuel)? {
            Value::Sigma { dom, .. } => Ok((*dom).clone()),
            other => Err(CheckError::new(format!(
                "fst expects a pair value; {} has type {}",
                pretty_core(p, &self.gnames),
                pretty_value(&other, ctx.len(), &self.gvals, &self.gnames),
            ))),
        }
    }

    /// Type of `snd p`: the Sigma's codomain with `fst p` substituted.
    /// Same two cases (and same deliberate omission) as `infer_fst`.
    fn infer_snd(&self, p: &Core, ctx: &Ctx) -> Result<Value, CheckError> {
        if let Core::Pair(_, b) = p {
            return self.infer(b, ctx);
        }
        let pty = self.infer(p, ctx)?;
        let mut fuel = FUEL_LIMIT;
        match whnf(&pty, &self.gvals, &mut fuel)? {
            Value::Sigma { cod, .. } => {
                let fst_v = eval(
                    &Core::Fst(Box::new(p.clone())),
                    &ctx.values,
                    &self.gvals,
                )?;
                cod.apply(fst_v, &self.gvals).map_err(CheckError::from)
            }
            other => Err(CheckError::new(format!(
                "snd expects a pair value; {} has type {}",
                pretty_core(p, &self.gnames),
                pretty_value(&other, ctx.len(), &self.gvals, &self.gnames),
            ))),
        }
    }

    /// Result type of a complete `W A B` application: `Type(max(sort(A),
    /// sort(B fresh)))` via `predicative_max` (computed when the actuals are
    /// concrete, floating only under genuine ambiguity). Returns `None` for
    /// non-`W` spines (including partial `W A`, which elaborates generically).
    /// `A` was already validated by the inner application; `B` is checked
    /// here against `(A -> Type(?b))` so its actual codomain bounds `?b`.
    fn infer_w_app(&self, f: &Core, b_core: &Core, ctx: &Ctx) -> Result<Option<Value>, CheckError> {
        let fv = eval(f, &ctx.values, &self.gvals)?;
        let mut fuel = FUEL_LIMIT;
        let hw = whnf(&fv, &self.gvals, &mut fuel)?;
        // Exactly one collected argument (`A`); head must be bare `W`
        // (possibly global-aliased — unfolded above).
        let a_val = match hw {
            Value::App(head, a) => {
                let mut hf = FUEL_LIMIT;
                match whnf(&head, &self.gvals, &mut hf)? {
                    Value::W => *a,
                    _ => return Ok(None),
                }
            }
            _ => return Ok(None),
        };
        let sort_a = self.infer_sort_value(&a_val, ctx)?;
        let lb = Level::Var(fresh_level_var());
        let pi_b = Value::Pi {
            name: "_".to_string(),
            dom: Box::new(a_val.clone()),
            cod: Closure::new(ctx.values.clone(), Core::Sort(Sort::Type(lb))),
        };
        self.check(b_core, &pi_b, ctx)?;
        // `B`'s actual codomain level at a fresh point (closure-apply for
        // lambdas, stuck application otherwise — both sort-fine).
        let b_val = eval(b_core, &ctx.values, &self.gvals)?;
        let mut ctx2 = ctx.clone();
        let fresh_ix = ctx2.len();
        let fresh = Value::Var(fresh_ix);
        ctx2.push(a_val, fresh.clone());
        let b_app = match b_val {
            Value::Lam { body, .. } => body.apply(fresh, &self.gvals)?,
            neutral => Value::App(Box::new(neutral), Box::new(fresh)),
        };
        let sort_b = self.infer_sort_value(&b_app, &ctx2)?;
        Ok(Some(Value::Sort(self.predicative_max(&sort_a, &sort_b))))
    }

    // -- holes / metavariables -----------------------------------------------
    // Surface `_` in term position elaborates to a hole the checker must
    // fill (see `Core::Hole` / `Value::Meta`). Holes solve in two ways:
    // determined shapes checked directly (Pi eta-expansion, the `()` inhabitant
    // of `Unit`), and Miller-pattern unification against rigid terms. Anything
    // else stays deferred and becomes a typed-hole error at the end of the
    // definition (unsolved holes fail the def — never recorded facts).
    //
    // Soundness notes (all load-bearing):
    // - One assignment per id, ever: solving substitutes a value valid in
    //   every occurrence context (Miller-pattern spine, occurs-checked,
    //   levels below `origin_len`, which contexts only grow past).
    // - Unknowns never alias: flex-flex pairs postpone, never assign.
    // - Nothing escapes: `check_decl` drains postponements, reports unsolved
    //   holes, zonks, and asserts meta-freedom before recording globals.

    /// Per-def checkpoint covering every monotone store (universes, metas,
    /// postponements): a failed comparison leaves no trace anywhere. Hole
    /// ids are dense from zero (one never-reset supply), so the metas
    /// checkpoint is a length and rollback truncates — abandoned ids simply
    /// leave `None` gaps and are never reused.
    fn ucheckpoint(&self) -> Checkpoint {
        Checkpoint {
            ucons: self.ucons.borrow().len(),
            metas: self.metas.borrow().len(),
            postponed: self.postponed.borrow().len(),
        }
    }

    fn urollback(&self, ckpt: Checkpoint) {
        self.ucons.borrow_mut().truncate(ckpt.ucons);
        self.metas.borrow_mut().truncate(ckpt.metas);
        self.postponed.borrow_mut().truncate(ckpt.postponed);
    }

    /// Fresh hole id (surface and elaboration-generated holes share one
    /// never-reset supply, so ids are globally unique).
    fn fresh_hole(&self) -> u32 {
        let id = self.hole_supply.get();
        self.hole_supply.set(id + 1);
        id
    }

    /// Resolve surface hole `id` to its metavariable, creating the entry on
    /// first contact. Re-encounters shrink `origin_len` (sound solution
    /// scope) and unify differing recorded types (one unknown, one type).
    fn ensure_meta(&self, id: u32, span: Span, ty: Option<Value>, origin_len: usize, ctx: &Ctx) -> Result<(), CheckError> {
        {
            let mut metas = self.metas.borrow_mut();
            while metas.len() <= id as usize {
                metas.push(None);
            }
            match &mut metas[id as usize] {
                Some(e) => {
                    e.origin_len = e.origin_len.min(origin_len);
                    match (&e.ty, &ty) {
                        (Some(_), Some(_)) => {
                            // Merge below (needs `&self` without the borrow).
                        }
                        (None, Some(new)) => {
                            e.ty = Some(new.clone());
                            return Ok(());
                        }
                        _ => return Ok(()),
                    }
                }
                slot => {
                    *slot = Some(MetaEntry { span, ty, origin_len, assigned: None });
                    return Ok(());
                }
            }
        }
        // Re-encounter with a second known type: the two must agree (one
        // unknown term, one type — differing demands are a real error).
        let (old, new) = {
            let metas = self.metas.borrow();
            let e = metas[id as usize].as_ref().expect("just ensured");
            (e.ty.clone().expect("merge needs both types"), ty.expect("merge needs both types"))
        };
        match self.unify_inner(&old, &new, ctx, ctx.len())? {
            UOut::Mismatch => Err(CheckError::new("hole `_` used at inconsistent types".to_string())),
            _ => Ok(()),
        }
    }

    fn unify(&self, a: &Value, b: &Value, ctx: &Ctx, val: &Core) -> Result<(), CheckError> {
        match self.unify_inner(a, b, ctx, ctx.len())? {
            UOut::Mismatch => {
                let za = self.zonk_value(a)?;
                let zb = self.zonk_value(b)?;
                Err(CheckError::new(format!(
                    "{} : {} :! {}",
                    pretty_core(val, &self.gnames),
                    pretty_value(&za, ctx.len(), &self.gvals, &self.gnames),
                    pretty_value(&zb, ctx.len(), &self.gvals, &self.gnames),
                )))
            }
            _ => Ok(()),
        }
    }

    /// One unification step between elaborated values. Both sides are zonked
    /// (assignments followed) and weak-head normalized first. Flex-rigid
    /// pairs over a Miller-pattern spine assign; flex-flex pairs and
    /// non-pattern flex-rigid pairs postpone (revisited after progress and
    /// drained at def end); rigid pairs whose heads match decompose
    /// structurally, mirroring `conv` but recursing into `unify_inner` so
    /// nested unknowns still solve. Rigid head mismatch is a real mismatch
    /// (no assignment can change rigid heads). Sorts and atoms delegate to
    /// `conv`, which never sees a meta here (pre-scanned below).
    fn unify_inner(&self, a: &Value, b: &Value, ctx: &Ctx, level: usize) -> Result<UOut, CheckError> {
        let za = self.zonk_value(a)?;
        let zb = self.zonk_value(b)?;
        let mut fuel = FUEL_LIMIT;
        let wa = whnf(&za, &self.gvals, &mut fuel)?;
        let wb = whnf(&zb, &self.gvals, &mut fuel)?;
        // Flex cases (at least one side a stuck unknown after zonk+whnf).
        match (&wa, &wb) {
            (Value::Meta { id, span, spine }, other) if !matches!(other, Value::Meta { .. }) => {
                return self.solve_meta(*id, *span, spine, other, ctx);
            }
            (other, Value::Meta { id, span, spine }) if !matches!(other, Value::Meta { .. }) => {
                return self.solve_meta(*id, *span, spine, other, ctx);
            }
            (Value::Meta { id: i1, .. }, Value::Meta { id: i2, .. }) => {
                // Same unknown on both sides: equal regardless of spine
                // (one assignment, valid in every occurrence context by the
                // level bound — see `assign_meta`). Distinct unknowns never
                // alias: postpone (each solves independently or errors).
                if i1 == i2 {
                    return Ok(UOut::Eq);
                }
                self.postpone(za, zb);
                return Ok(UOut::Defer);
            }
            _ => {}
        }
        // Rigid pairs: bail to postponement if unknowns hide inside (their
        // assignment may decide the outcome later); otherwise `conv` decides.
        if contains_meta(&wa) || contains_meta(&wb) {
            return self.unify_rigid(&wa, &wb, ctx, level);
        }
        let mut fuel2 = FUEL_LIMIT;
        let mut ucs = self.ucons.borrow_mut();
        match conv(level, &wa, &wb, &self.gvals, &mut fuel2, 0, &mut ucs) {
            Ok(true) => Ok(UOut::Eq),
            Ok(false) => Ok(UOut::Mismatch),
            Err(e) => Err(CheckError::from(e)),
        }
    }

    /// Rigid-vs-rigid unification with unknowns nested inside: decompose the
    /// common constructors (recursing into `unify_inner`, so nested unknowns
    /// still solve) and postpone anything subtle (eta, match, mixed heads
    /// that `conv` already rejects... — no: mismatched rigid heads are a
    /// real mismatch, since no assignment changes rigid heads).
    fn unify_rigid(&self, a: &Value, b: &Value, ctx: &Ctx, level: usize) -> Result<UOut, CheckError> {
        match (a, b) {
            (Value::Pi { dom: d1, cod: c1, .. }, Value::Pi { dom: d2, cod: c2, .. }) => {
                self.seq_unify(&[
                    (d1.as_ref(), d2.as_ref()),
                ], ctx, level)?;
                let fresh = Value::Var(level);
                let v1 = c1.apply(fresh.clone(), &self.gvals)?;
                let v2 = c2.apply(fresh, &self.gvals)?;
                self.seq_unify(&[(&v1, &v2)], ctx, level + 1)
            }
            (Value::Sigma { dom: d1, cod: c1, .. }, Value::Sigma { dom: d2, cod: c2, .. }) => {
                self.seq_unify(&[
                    (d1.as_ref(), d2.as_ref()),
                ], ctx, level)?;
                let fresh = Value::Var(level);
                let v1 = c1.apply(fresh.clone(), &self.gvals)?;
                let v2 = c2.apply(fresh, &self.gvals)?;
                self.seq_unify(&[(&v1, &v2)], ctx, level + 1)
            }
            (Value::App(f1, a1), Value::App(f2, a2))
            | (Value::Pair(f1, a1), Value::Pair(f2, a2))
            | (Value::Either(f1, a1), Value::Either(f2, a2))
            | (Value::Quotient(f1, a1), Value::Quotient(f2, a2)) => {
                self.seq_unify(&[(f1.as_ref(), f2.as_ref()), (a1.as_ref(), a2.as_ref())], ctx, level)
            }
            (Value::Inl(a1), Value::Inl(a2))
            | (Value::Inr(a1), Value::Inr(a2))
            | (Value::Fst(a1), Value::Fst(a2))
            | (Value::Snd(a1), Value::Snd(a2))
            | (Value::QuotMk(a1), Value::QuotMk(a2)) => {
                self.seq_unify(&[(a1.as_ref(), a2.as_ref())], ctx, level)
            }
            // Sorts, variables, globals: meta-free here by construction
            // (the pre-scan routed anything meta-bearing above), so `conv`
            // decides directly — same constraints as always.
            (Value::Sort(_), Value::Sort(_))
            | (Value::Var(_), Value::Var(_))
            | (Value::Global(_, _), Value::Global(_, _)) => {
                let mut fuel = FUEL_LIMIT;
                let mut ucs = self.ucons.borrow_mut();
                match conv(level, a, b, &self.gvals, &mut fuel, 0, &mut ucs) {
                    Ok(true) => Ok(UOut::Eq),
                    Ok(false) => Ok(UOut::Mismatch),
                    Err(e) => Err(CheckError::from(e)),
                }
            }
            // Unit eta, mirroring `conv` exactly (same approximation class:
            // `()` converts with neutrals, which may be Unit-typed — metas
            // among them; anything already decided stays decided).
            (Value::Pt, other) | (other, Value::Pt) => match other {
                Value::Var(_)
                | Value::Global(_, _)
                | Value::App(_, _)
                | Value::Match { .. }
                | Value::Fst(_)
                | Value::Snd(_)
                | Value::Meta { .. } => Ok(UOut::Eq),
                _ => {
                    self.postpone(a.clone(), b.clone());
                    Ok(UOut::Defer)
                }
            },
            // Anything else (eta shapes, matches, mixed rigid heads): postpone.
            // A later assignment can still decide these — even head mismatch,
            // since assigning a head-position meta redexes (e.g. `?m x` with
            // `?m := \_. *`). If nothing ever assigns, the unsolved-hole
            // sweep fails the def.
            _ => {
                self.postpone(a.clone(), b.clone());
                Ok(UOut::Defer)
            }
        }
    }

    /// Unify a sequence of pairs left to right: `Mismatch` or fuel errors
    /// abort immediately; `Defer` is sticky (the whole sequence defers —
    /// later pairs still run, so one pass makes maximal progress).
    fn seq_unify(&self, pairs: &[(&Value, &Value)], ctx: &Ctx, level: usize) -> Result<UOut, CheckError> {
        let mut out = UOut::Eq;
        for (x, y) in pairs {
            match self.unify_inner(x, y, ctx, level)? {
                UOut::Mismatch => return Ok(UOut::Mismatch),
                UOut::Defer => out = UOut::Defer,
                UOut::Eq => {}
            }
        }
        Ok(out)
    }

    /// Record a deferred equation for the drain (duplicates tolerated: the
    /// drain stops on no-progress, so reposts only cost fuel, bounded below).
    fn postpone(&self, a: Value, b: Value) {
        self.postponed.borrow_mut().push((a, b));
    }

    /// Attempt `?id[spine] := rhs` (Miller pattern fragment). Assigns on
    /// success (`Eq`); anything shape-uncertain postpones (`Defer`); only
    /// permanent failures (occurs violation, out-of-scope levels, solution
    /// ill-typed against the hole's recorded type) mismatch.
    /// The spine must be distinct bound variables; the right-hand side must
    /// be free of `?id` (occurs-checked through assigned metas) and mention
    /// only levels below the meta's origin (contexts grow append-only, so
    /// those levels mean the same in every occurrence — the assignment is
    /// valid wherever the hole occurs). Finally the solution must CHECK
    /// against the recorded type: assigning without that proves false
    /// universe judgments (`g _ *` with `?m : Type0` assigned `Type0`,
    /// i.e. `Type0 : Type0`).
    fn solve_meta(&self, id: u32, span: Span, spine: &[Value], rhs: &Value, ctx: &Ctx) -> Result<UOut, CheckError> {
        // Lazily register unknowns first met inside unification (e.g. a hole
        // evaluated into an annotation before elaboration contacted its
        // core): no known type yet, origin is the current context.
        self.ensure_meta(id, span, None, ctx.len(), ctx)?;
        // The spine must be distinct bound variables (pattern fragment);
        // anything else (projections, applications, duplicate or closed
        // entries) postpones — a later assignment inside the spine may still
        // turn it into a pattern.
        let mut seen = Vec::new();
        for e in spine {
            match e {
                Value::Var(l) if !seen.contains(l) => seen.push(*l),
                _ => {
                    let (a, b) = (self.zonk_value(&Value::Meta {
                        id,
                        span,
                        spine: spine.to_vec(),
                    })?, self.zonk_value(rhs)?);
                    self.postpone(a, b);
                    return Ok(UOut::Defer);
                }
            }
        }
        let zrhs = self.zonk_value(rhs)?;
        // Occurs check (through assignments — zonked above, so any `?id`
        // inside is a genuine cycle, never a shadow of another unknown).
        if occurs_meta(id, &zrhs) {
            return Ok(UOut::Mismatch);
        }
        // Scope check: every free level of the solution must predate the
        // meta's oldest occurrence.
        let origin = self.meta_origin(id);
        let mut levels = Vec::new();
        free_levels_value(&zrhs, &mut levels);
        if levels.iter().any(|l| *l >= origin) {
            return Ok(UOut::Mismatch);
        }
        // Type check: the solution must check against the hole's recorded
        // type (if it has one — lazily-registered unknowns met only inside
        // unification may not). Quoting needs a context covering every free
        // level; when this one does not (the drain re-unifies with an empty
        // context), the assignment cannot be validated here — postpone the
        // equation instead of assigning blindly (the drain retries; an
        // unassigned hole still fails the def at the unsolved sweep).
        if let Some(ty) = self.metas.borrow().get(id as usize).and_then(|o| o.as_ref()).and_then(|e| e.ty.clone()) {
            let zty = self.zonk_value(&ty)?;
            if occurs_meta(id, &zty) {
                return Ok(UOut::Mismatch);
            }
            let mut tlevels = Vec::new();
            free_levels_value(&zty, &mut tlevels);
            if levels.iter().chain(tlevels.iter()).any(|l| *l >= ctx.len()) {
                let a = self.zonk_value(&Value::Meta { id, span, spine: spine.to_vec() })?;
                self.postpone(a, zrhs);
                return Ok(UOut::Defer);
            }
            let mut fuel_q = FUEL_LIMIT;
            match crate::core::quote(ctx.len(), &zrhs, &self.gvals, &mut fuel_q, 0) {
                Ok(core) => {
                    if self.check(&core, &zty, ctx).is_err() {
                        return Ok(UOut::Mismatch);
                    }
                }
                Err(_) => return Ok(UOut::Mismatch),
            }
        }
        self.assign_meta(id, zrhs);
        Ok(UOut::Eq)
    }

    /// Record an assignment (the id is unassigned: zonking routes assigned
    /// ids to their solutions before anyone solves, so reassignment cannot
    /// happen — and the occurs check keeps every chain acyclic, which is
    /// what makes `zonk_value` terminate).
    fn assign_meta(&self, id: u32, v: Value) {
        if let Some(e) = self.metas.borrow_mut().get_mut(id as usize).and_then(|o| o.as_mut()) {
            debug_assert!(e.assigned.is_none(), "reassignment of hole {id}");
            e.assigned = Some(v);
        }
    }

    /// Follow assignments (depth-capped like `quote`/`conv`). Closure
    /// *terms* keep their `Hole` cores — evaluation resolves those to fresh
    /// `Meta` values on use, which zonk then follows; substituting solutions
    /// into cores would need quoting at unknown levels.
    fn zonk_value(&self, v: &Value) -> Result<Value, EvalError> {
        self.zonk_value_in(v, 0)
    }

    fn zonk_value_in(&self, v: &Value, depth: u32) -> Result<Value, EvalError> {
        if depth > DEPTH_LIMIT {
            return Err(EvalError { msg: "zonk depth limit exceeded".to_string() });
        }
        match v {
            Value::Meta { id, span, spine } => {
                let solved = self.metas.borrow().get(*id as usize).and_then(|o| o.as_ref()).and_then(|e| e.assigned.clone());
                match solved {
                    Some(s) => self.zonk_value_in(&s, depth + 1),
                    None => {
                        let mut s2 = Vec::with_capacity(spine.len());
                        for e in spine {
                            s2.push(self.zonk_value_in(e, depth + 1)?);
                        }
                        Ok(Value::Meta { id: *id, span: *span, spine: s2 })
                    }
                }
            }
            Value::Pi { name, dom, cod } => Ok(Value::Pi {
                name: name.clone(),
                dom: Box::new(self.zonk_value_in(dom, depth + 1)?),
                cod: self.zonk_closure(cod, depth + 1)?,
            }),
            Value::Sigma { name, dom, cod } => Ok(Value::Sigma {
                name: name.clone(),
                dom: Box::new(self.zonk_value_in(dom, depth + 1)?),
                cod: self.zonk_closure(cod, depth + 1)?,
            }),
            Value::Lam { name, body } => Ok(Value::Lam {
                name: name.clone(),
                body: self.zonk_closure(body, depth + 1)?,
            }),
            Value::App(f, a) => Ok(Value::App(
                Box::new(self.zonk_value_in(f, depth + 1)?),
                Box::new(self.zonk_value_in(a, depth + 1)?),
            )),
            Value::Pair(a, b) => Ok(Value::Pair(
                Box::new(self.zonk_value_in(a, depth + 1)?),
                Box::new(self.zonk_value_in(b, depth + 1)?),
            )),
            Value::Either(a, b) => Ok(Value::Either(
                Box::new(self.zonk_value_in(a, depth + 1)?),
                Box::new(self.zonk_value_in(b, depth + 1)?),
            )),
            Value::Inl(a) => Ok(Value::Inl(Box::new(self.zonk_value_in(a, depth + 1)?))),
            Value::Inr(b) => Ok(Value::Inr(Box::new(self.zonk_value_in(b, depth + 1)?))),
            Value::Fst(p) => Ok(Value::Fst(Box::new(self.zonk_value_in(p, depth + 1)?))),
            Value::Snd(p) => Ok(Value::Snd(Box::new(self.zonk_value_in(p, depth + 1)?))),
            Value::Quotient(a, r) => Ok(Value::Quotient(
                Box::new(self.zonk_value_in(a, depth + 1)?),
                Box::new(self.zonk_value_in(r, depth + 1)?),
            )),
            Value::QuotMk(a) => Ok(Value::QuotMk(Box::new(self.zonk_value_in(a, depth + 1)?))),
            Value::Match { scrut, mot, l_name, l_body, r_name, r_body } => Ok(Value::Match {
                scrut: Box::new(self.zonk_value_in(scrut, depth + 1)?),
                mot: Box::new(self.zonk_value_in(mot, depth + 1)?),
                l_name: l_name.clone(),
                l_body: self.zonk_closure(l_body, depth + 1)?,
                r_name: r_name.clone(),
                r_body: self.zonk_closure(r_body, depth + 1)?,
            }),
            _ => Ok(v.clone()),
        }
    }

    fn zonk_closure(&self, c: &Closure, depth: u32) -> Result<Closure, EvalError> {
        Ok(Closure {
            env: c.env.iter().map(|e| self.zonk_value_in(e, depth)).collect::<Result<Vec<_>, _>>()?,
            term: c.term.clone(),
        })
    }

    /// Safety net: does an *unassigned* unknown occur in a value about to be
    /// recorded? Assigned metas and their `Hole` cores are benign (uses
    /// resolve through the store); anything unassigned here means the sweep
    /// missed it — a soundness bug, never user error.
    fn meta_leak(&self, v: &Value) -> bool {
        match v {
            Value::Meta { id, spine, .. } => {
                match self.metas.borrow().get(*id as usize).and_then(|o| o.as_ref()) {
                    // Assigned: uses resolve through the store; the spine may
                    // still mention unknowns — check it.
                    Some(e) if e.assigned.is_some() => spine.iter().any(|e| self.meta_leak(e)),
                    // Unassigned or unknown: the sweep should have failed the
                    // def already — reaching record is the bug.
                    _ => true,
                }
            }
            Value::Var(_)
            | Value::Global(_, _)
            | Value::QuotLift
            | Value::QuotInd
            | Value::QuotSound
            | Value::Sort(_)
            | Value::Void
            | Value::Absurd
            | Value::SigRect
            | Value::EitherRect
            | Value::Unit
            | Value::Pt
            | Value::UnitRect
            | Value::W
            | Value::Sup
            | Value::WRect => false,
            Value::App(f, a)
            | Value::Pair(f, a)
            | Value::Either(f, a)
            | Value::Quotient(f, a) => self.meta_leak(f) || self.meta_leak(a),
            Value::Pi { dom, cod, .. } | Value::Sigma { dom, cod, .. } => {
                self.meta_leak(dom) || self.meta_leak_closure(cod)
            }
            Value::Lam { body, .. } => self.meta_leak_closure(body),
            Value::Inl(a) | Value::Inr(a) | Value::Fst(a) | Value::Snd(a) | Value::QuotMk(a) => {
                self.meta_leak(a)
            }
            Value::Match { scrut, mot, l_body, r_body, .. } => {
                self.meta_leak(scrut)
                    || self.meta_leak(mot)
                    || self.meta_leak_closure(l_body)
                    || self.meta_leak_closure(r_body)
            }
        }
    }

    fn meta_leak_closure(&self, c: &Closure) -> bool {
        c.env.iter().any(|e| self.meta_leak(e)) || self.meta_leak_core(&c.term)
    }

    fn meta_leak_core(&self, t: &Core) -> bool {
        match t {
            // Assigned holes re-elaborate on use — benign.
            Core::Hole { id, .. } => self
                .metas
                .borrow()
                .get(*id as usize)
                .and_then(|o| o.as_ref())
                .is_none_or(|e| e.assigned.is_none()),
            Core::Bound(_)
            | Core::Global(_, _)
            | Core::QuotLift
            | Core::QuotInd
            | Core::QuotSound
            | Core::Sort(_)
            | Core::Void
            | Core::Absurd
            | Core::SigRect
            | Core::EitherRect
            | Core::Unit
            | Core::Pt
            | Core::UnitRect
            | Core::W
            | Core::Sup
            | Core::WRect => false,
            Core::Pi { dom, cod, .. } | Core::Sigma { dom, cod, .. } => {
                self.meta_leak_core(dom) || self.meta_leak_core(cod)
            }
            Core::Pair(a, b)
            | Core::Either(a, b)
            | Core::App(a, b)
            | Core::Quotient(a, b)
            | Core::Ann(a, b) => self.meta_leak_core(a) || self.meta_leak_core(b),
            Core::Inl(a)
            | Core::Inr(a)
            | Core::Fst(a)
            | Core::Snd(a)
            | Core::QuotMk(a)
            | Core::Lam { body: a, .. } => self.meta_leak_core(a),
            Core::Match { scrut, motive, l_body, r_body, .. } => {
                self.meta_leak_core(scrut)
                    || self.meta_leak_core(motive)
                    || self.meta_leak_core(l_body)
                    || self.meta_leak_core(r_body)
            }
            Core::Let { ann, val, body, .. } => {
                ann.as_ref().is_some_and(|a| self.meta_leak_core(a))
                    || self.meta_leak_core(val)
                    || self.meta_leak_core(body)
            }
        }
    }

    /// Fresh level above everything a value mentions (for decomposition
    /// variables and quoting in messages).
    fn above(&self, a: &Value, b: &Value) -> usize {
        let mut ls = Vec::new();
        free_levels_value(a, &mut ls);
        free_levels_value(b, &mut ls);
        ls.into_iter().max().map(|l| l + 1).unwrap_or(0)
    }

    /// Re-run postponed equations until no assignment lands (each pass that
    /// assigns makes progress; passes are bounded by the number of holes,
    /// since no id is ever assigned twice). A surviving `Mismatch` is a
    /// real type error, reported zonked. Leftovers with unassigned metas are
    /// NOT errors here — the unsolved-hole sweep reports those (with spans).
    fn drain_postponed(&self) -> Result<(), CheckError> {
        loop {
            let before = self.assigned_count();
            let mut kept = Vec::new();
            let mut failed: Option<CheckError> = None;
            // Snapshot the queue (solving borrows the store; draining it
            // inline would double-borrow).
            let queue = std::mem::take(&mut *self.postponed.borrow_mut());
            // A throwaway empty context: postponed pairs carry absolute
            // levels in their spines, so no context is needed (freshness
            // comes from `above`, not `ctx.len()`).
            let ctx = Ctx::default();
            for (a, b) in queue {
                let level = self.above(&a, &b);
                match self.unify_inner(&a, &b, &ctx, level) {
                    Ok(UOut::Eq) => {}
                    Ok(UOut::Defer) => kept.push((a, b)),
                    Ok(UOut::Mismatch) => {
                        let za = self.zonk_value(&a)?;
                        let zb = self.zonk_value(&b)?;
                        let lv = self.above(&za, &zb);
                        failed = Some(CheckError::new(format!(
                            "deferred equation failed: {} :! {}",
                            pretty_value(&za, lv, &self.gvals, &self.gnames),
                            pretty_value(&zb, lv, &self.gvals, &self.gnames),
                        )));
                        kept.push((a, b));
                        break;
                    }
                    Err(e) => {
                        failed = Some(e);
                        break;
                    }
                }
            }
            *self.postponed.borrow_mut() = kept;
            if let Some(e) = failed {
                return Err(e);
            }
            if self.assigned_count() == before {
                return Ok(());
            }
        }
    }

    /// Report every unassigned hole (id order) with its location and
    /// expected type. Called after draining: anything listed here is
    /// genuinely undetermined, and the definition fails.
    fn unsolved_holes(&self) -> Result<(), CheckError> {
        let metas = self.metas.borrow();
        let mut ids: Vec<u32> = metas
            .iter()
            .enumerate()
            .filter_map(|(i, e)| match e {
                Some(m) if m.assigned.is_none() => Some(i as u32),
                _ => None,
            })
            .collect();
        ids.sort_unstable();
        if ids.is_empty() {
            return Ok(());
        }
        let mut parts = Vec::new();
        for id in ids {
            let e = metas[id as usize].as_ref().expect("listed");
            let ty_s = match &e.ty {
                Some(t) => {
                    let zt = self.zonk_value(t).unwrap_or_else(|_| t.clone());
                    let mut ls = Vec::new();
                    free_levels_value(&zt, &mut ls);
                    let lv = ls.into_iter().max().map(|l| l + 1).unwrap_or(0);
                    pretty_value(&zt, lv, &self.gvals, &self.gnames)
                }
                None => "(type unknown)".to_string(),
            };
            parts.push(format!("hole `_` at {}: expected {}", self.hole_loc(e.span), ty_s));
        }
        Err(CheckError::new(format!("unsolved hole(s): {}", parts.join("; "))))
    }

    fn assigned_count(&self) -> usize {
        self.metas.borrow().iter().filter(|e| e.as_ref().is_some_and(|m| m.assigned.is_some())).count()
    }

    /// Elaborate a `_` hole against a known expected type: fill it when the
    /// type determines the term (functions eta-expand, `()` inhabits `Unit`),
    /// otherwise record an unsolved metavariable and succeed — the
    /// end-of-def drain reports it if nothing ever solves it. Re-encounters
    /// of an already-assigned hole verify against the solution instead.
    fn check_hole(&self, id: u32, span: Span, expected: &Value, ctx: &Ctx) -> Result<(), CheckError> {
        // Assigned already (e.g. solved earlier, re-met through a
        // quote-then-infer roundtrip): the solution must fit here too.
        if let Some(solved) = self.metas.borrow().get(id as usize).and_then(|o| o.as_ref()).and_then(|e| e.assigned.clone()) {
            let z = self.zonk_value(&solved)?;
            return self.unify(&z, expected, ctx, &Core::Hole { id, span });
        }
        let mut fuel = FUEL_LIMIT;
        let exp = whnf(expected, &self.gvals, &mut fuel)?;
        match &exp {
            Value::Pi { dom, cod, .. } => {
                // Determined by eta: the solution is a lambda; its body is a
                // fresh hole checked against the codomain (which solves,
                // defers, or errors exactly like any other hole).
                let mut ctx2 = ctx.clone();
                let fresh = Value::Var(ctx2.len());
                ctx2.push((**dom).clone(), fresh.clone());
                let cod_v = cod.apply(fresh, &self.gvals)?;
                let inner = self.fresh_hole();
                let inner_core = Core::Hole { id: inner, span };
                self.ensure_meta(inner, span, Some(cod_v.clone()), ctx2.len(), &ctx2)?;
                self.check(&inner_core, &cod_v, &ctx2)?;
                let lam = Value::Lam {
                    name: "_".to_string(),
                    body: Closure::new(ctx.values.clone(), inner_core),
                };
                self.ensure_meta(id, span, Some(expected.clone()), ctx.len(), ctx)?;
                self.assign_meta(id, lam);
                Ok(())
            }
            Value::Unit => {
                // Determined: `()` is the canonical inhabitant (definitional
                // uniqueness does the rest — neutrals convert with it).
                self.ensure_meta(id, span, Some(expected.clone()), ctx.len(), ctx)?;
                self.assign_meta(id, Value::Pt);
                Ok(())
            }
            _ => {
                // Nothing determines the term: defer. If no equation ever
                // solves it, the drain reports the hole with this type.
                self.ensure_meta(id, span, Some(expected.clone()), ctx.len(), ctx)?;
                Ok(())
            }
        }
    }

    /// Location string for a hole span (`line:col`, or byte offsets when no
    /// source was stashed — e.g. hand-built test programs).
    fn hole_loc(&self, span: Span) -> String {
        let src = self.source.borrow();
        if src.is_empty() {
            return format!("byte {}..{}", span.start, span.end);
        }
        let (l, c) = line_col(&src, span.start);
        format!("line {l}, col {c}")
    }

    /// Oldest occurrence context length for a hole id.
    fn meta_origin(&self, id: u32) -> usize {
        self.metas
            .borrow()
            .get(id as usize)
            .and_then(|o| o.as_ref())
            .map(|e| e.origin_len)
            .unwrap_or(0)
    }

    // -- checking -----------------------------------------------------------

    fn check(&self, val: &Core, expected: &Value, ctx: &Ctx) -> Result<(), CheckError> {
        // Ascriptions verify like inference does: the annotation must be a
        // type, the value must check against it, and it must agree with the
        // ambient expectation. (Stripping the annotation unchecked accepts
        // false claims like `(() : Void)`.)
        if let Core::Ann(e, t) = val {
            let t_v = self.check_ty(t, ctx)?;
            self.is_type_value(&t_v, ctx)?;
            self.check(e, &t_v, ctx)?;
            return self.expect_conv(&t_v, expected, ctx, val);
        }
        // Holes elaborate against the expected type (synthesis or deferral).
        if let Core::Hole { id, span } = val {
            return self.check_hole(*id, *span, expected, ctx);
        }
        // Lets in value position: check items, then tail (never just unfold).
        if let Core::Let { ann, val: v, body, .. } = val {
            return self.check_let(ann, v, body, Some(expected), ctx);
        }
        // Lambdas against Pi (introduce a fresh var).
        if let Core::Lam { name: _, body } = val {
            let mut fuel = FUEL_LIMIT;
            let w = whnf(expected, &self.gvals, &mut fuel)?;
            match w {
                Value::Pi { dom, cod, .. } => {
                    let mut ctx2 = ctx.clone();
                    let fresh_ix = ctx2.len();
                    let fresh = Value::Var(fresh_ix);
                    ctx2.push((*dom).clone(), fresh.clone());
                    let cod_v = cod.apply(fresh, &self.gvals)?;
                    // `body` is under one binder; check it in ctx2.
                    return self.check(body, &cod_v, &ctx2);
                }
                other => {
                    return Err(CheckError::new(format!(
                        "lambda {} does not fit non-function type {}",
                        pretty_core(val, &self.gnames),
                        pretty_value(&other, ctx.len(), &self.gvals, &self.gnames),
                    )));
                }
            }
        }
        // Pairs against Sigma only (values only — use `and` for types).
        if let Core::Pair(a, b) = val {
            return self.check_pair(a, b, expected, ctx);
        }
        // Injections against sums (payload against the matching side).
        if let Core::Inl(a) = val {
            return self.check_inject(a, true, expected, ctx);
        }
        if let Core::Inr(b) = val {
            return self.check_inject(b, false, expected, ctx);
        }
        // Quotient introduction against a known quotient (payload against
        // the carrier; the relation is irrelevant here, like the other side).
        if let Core::QuotMk(a) = val {
            return self.check_quot_mk(a, expected, ctx);
        }
        // Neutral values (app/var/global/projections/eliminators/`()`/match):
        // infer + convert. This runs even when the application would reduce
        // to an intro form, so argument checking is never skipped
        // (soundness-critical). (`()` infers unambiguously, so it joins the
        // neutrals; ambiguous intros like pairs/sums keep their dispatch.)
        match val {
            Core::App(_, _) | Core::Bound(_) | Core::Global(_, _)
            | Core::Fst(_) | Core::Snd(_) | Core::EitherRect | Core::Pt
            | Core::Match { .. } => {
                let inferred = self.infer(val, ctx)?;
                // Formation positions (`expected` is a sort) care about the
                // denotation, not the inferred type — but the cheap decision
                // runs first and the fallback only on failure, so formation
                // checking never pays twice. When the fallback runs, any
                // constraints the failed comparison recorded are rolled back
                // (a failed comparison must leave no trace); assignments it
                // made stay (they are verified solutions, like everywhere).
                let ucons_snapshot = self.ucons.borrow().len();
                match self.expect_conv(&inferred, expected, ctx, val) {
                    Ok(()) => return Ok(()),
                    Err(e) => {
                        // Formation fallback: an applied family denotes a
                        // type even when its inferred type is a sort
                        // (`bigalias Void : Type(?f)` denotes `Void : *`), so
                        // validate well-formedness instead of converting
                        // (conversion of a type against a sort always fails).
                        // Non-sort expectations keep infer+convert (a type is
                        // not a term of a non-sort type: `Nat : Nat` stays
                        // rejected). Holes stay with unification: inferred
                        // metas, or hole cores inside `val` (whose recorded
                        // types — not solutions — drive re-inference), skip
                        // the fallback so solving behavior is unchanged.
                        let mut fuel_inf = FUEL_LIMIT;
                        let inferred_is_sort =
                            matches!(whnf(&inferred, &self.gvals, &mut fuel_inf)?, Value::Sort(_));
                        let mut fuel_exp = FUEL_LIMIT;
                        match whnf(expected, &self.gvals, &mut fuel_exp)? {
                            Value::Sort(s)
                                if !contains_meta(&inferred)
                                    && (!inferred_is_sort || !self.meta_leak_core(val)) =>
                            {
                                self.ucons.borrow_mut().truncate(ucons_snapshot);
                                let actual = self.infer_sort(val, ctx)?;
                                return self.require_sort_le(&actual, &s).map_err(|_| {
                                    CheckError::new(format!(
                                        "{} : {}, but expected a type in {} (large type in small universe)",
                                        pretty_core(val, &self.gnames),
                                        actual,
                                        s,
                                    ))
                                });
                            }
                            _ => {}
                        }
                        return Err(e);
                    }
                }
            }
            _ => {}
        }
        let mut fuel = FUEL_LIMIT;
        let exp = whnf(expected, &self.gvals, &mut fuel)?;
        match &exp {
            Value::Sort(s) => {
                // Expected a sort: `val` must be a well-formed type, and fit
                // by cumulativity (`*` fits anywhere; levels go up, recorded
                // when variables are involved). In particular `*` itself fits
                // in `Type0`, never in `*`.
                let actual = self.infer_sort(val, ctx)?;
                self.require_sort_le(&actual, s).map_err(|_| {
                    CheckError::new(format!(
                        "{} : {}, but expected a type in {} (large type in small universe)",
                        pretty_core(val, &self.gnames),
                        actual,
                        s,
                    ))
                })
            }
            _ => {
                // Default: infer + convert.
                let inferred = self.infer(val, ctx).map_err(|e| {
                    CheckError::new(format!(
                        "{} :! {} ({e})",
                        pretty_core(val, &self.gnames),
                        pretty_value(&exp, ctx.len(), &self.gvals, &self.gnames),
                    ))
                })?;
                self.expect_conv(&inferred, &exp, ctx, val)
            }
        }
    }

    fn expect_conv(&self, inferred: &Value, expected: &Value, ctx: &Ctx, val: &Core) -> Result<(), CheckError> {
        // See through assigned holes first: the fast paths below match on
        // shape (sorts, Pis), and an assigned-but-unzonked metavariable
        // would otherwise skip them and land in unification — where
        // conversion (equality, correctly) rejects what subsumption accepts
        // (`id _ Unit : Type0` must behave like the explicit `id * Unit`).
        // Zoning is assignment-following only (never solves), so hole
        // behavior is unchanged; unassigned holes still go to `unify`.
        let zi = self.zonk_value(inferred).unwrap_or_else(|_| inferred.clone());
        let ze = self.zonk_value(expected).unwrap_or_else(|_| expected.clone());
        let (inferred, expected) = (&zi, &ze);
        // Cumulativity (single direction: inferred-actual lifts into
        // expected): `*` fits anywhere for free; concrete levels compare
        // directly; variables record `<=`. (`Type` never fits in `*`.)
        if let (Value::Sort(a), Value::Sort(b)) = (whnfed(inferred, self), whnfed(expected, self)) {
            if self.require_sort_le(&a, &b).is_ok() {
                return Ok(());
            }
        }
        // Subsumption for functions (contravariant domains, covariant
        // codomains): a small-motive eliminator step checks against a
        // level-general required type, while a small proof never passes as a
        // large one (contravariance demands `Type0 <= *`, which fails).
        // Anything undecided here (metas, non-Pi shapes) falls through to
        // unification below, so hole behavior is unchanged.
        match self.subsumes(inferred, expected, ctx) {
            Ok(true) => return Ok(()),
            Ok(false) => {}
            Err(e) => return Err(e),
        }
        // Unification (holes-aware): solves, defers, or mismatches. Plain
        // `conv` runs only inside, on meta-free pairs.
        self.unify(inferred, expected, ctx, val)
    }

    /// Subsumption `inferred <= expected` (does the inferred type fit where
    /// the expected is required?). Sorts subsume by `require_sort_le`; Pi
    /// types subsume contravariantly in the domain and covariantly in the
    /// codomain; anything else (including any metavariable — holes always go
    /// through unification) is undecided (`false`: fall through to `unify`).
    /// Never fails closed on its own: `false` just means "ask unification".
    fn subsumes(&self, inferred: &Value, expected: &Value, ctx: &Ctx) -> Result<bool, CheckError> {
        let mut fuel = FUEL_LIMIT;
        let wi = whnf(inferred, &self.gvals, &mut fuel)?;
        let mut fuel2 = FUEL_LIMIT;
        let we = whnf(expected, &self.gvals, &mut fuel2)?;
        match (wi, we) {
            (Value::Sort(a), Value::Sort(b)) => Ok(self.require_sort_le(&a, &b).is_ok()),
            (
                Value::Pi { dom: d1, cod: c1, .. },
                Value::Pi { dom: d2, cod: c2, .. },
            ) => {
                // Contravariant domain: the required domain must fit the
                // inferred one (flipped subsumption).
                if !self.subsumes(&d2, &d1, ctx)? {
                    return Ok(false);
                }
                // Covariant codomain under a fresh point.
                let mut ctx2 = ctx.clone();
                let fresh_ix = ctx2.len();
                let fresh = Value::Var(fresh_ix);
                ctx2.push((*d1).clone(), fresh.clone());
                let v1 = c1.apply(fresh.clone(), &self.gvals)?;
                let v2 = c2.apply(fresh, &self.gvals)?;
                self.subsumes(&v1, &v2, &ctx2)
            }
            (wi, we) => {
                // Atomic shapes subsume by equality (same verdict conversion
                // gives — unknown-free only; anything with a hole stays with
                // unification so solving behavior is unchanged).
                if contains_meta(&wi) || contains_meta(&we) {
                    return Ok(false);
                }
                let mut fuel3 = FUEL_LIMIT;
                let mut ucs = self.ucons.borrow_mut();
                match conv(ctx.len(), &wi, &we, &self.gvals, &mut fuel3, 0, &mut ucs) {
                    Ok(b) => Ok(b),
                    Err(e) => Err(CheckError::from(e)),
                }
            }
        }
    }

    /// Check a pair `(a, b)` against an expected Sigma type (components
    /// against dom/cod, second sees first via the binder). Anything else
    /// falls back to inference, which rejects `(a, b)` as ambiguous
    /// (values only — use `and` for product types).
    fn check_pair(
        &self,
        a: &Core,
        b: &Core,
        expected: &Value,
        ctx: &Ctx,
    ) -> Result<(), CheckError> {
        let mut fuel = FUEL_LIMIT;
        let exp = whnf(expected, &self.gvals, &mut fuel)?;
        match &exp {
            Value::Sigma { dom, cod, .. } => {
                let (dom, cod) = (dom.clone(), cod.clone());
                self.check(a, &dom, ctx)?;
                let av = eval(a, &ctx.values, &self.gvals)?;
                let tail = cod.apply(av, &self.gvals)?;
                self.check(b, &tail, ctx)
            }
            _ => {
                // Anything else: pairs only elaborate against Sigma. Surface
                // the ambiguity error from inference (it always errors).
                let pair = Core::Pair(Box::new(a.clone()), Box::new(b.clone()));
                match self.infer(&pair, ctx) {
                    Err(e) => Err(e),
                    Ok(_) => Err(CheckError::new(format!(
                        "({}, {}) :! {} (pair fits Sigma only)",
                        pretty_core(a, &self.gnames),
                        pretty_core(b, &self.gnames),
                        pretty_value(&exp, ctx.len(), &self.gvals, &self.gnames),
                    ))),
                }
            }
        }
    }

    /// Check an injection `inl a` / `inr b` against an expected type: the
    /// payload against the matching side of a whnf-unfolded `Either`.
    /// Anything else falls back to inference, which rejects bare
    /// injections as ambiguous.
    fn check_inject(
        &self,
        payload: &Core,
        is_left: bool,
        expected: &Value,
        ctx: &Ctx,
    ) -> Result<(), CheckError> {
        let mut fuel = FUEL_LIMIT;
        let exp = whnf(expected, &self.gvals, &mut fuel)?;
        match &exp {
            Value::Either(l, r) => {
                let side = if is_left { l } else { r };
                // `side: &Box<Value>` coerces to `&Value` for checking.
                self.check(payload, side, ctx)
            }
            _ => {
                let inferred = self
                    .infer(
                        &if is_left {
                            Core::Inl(Box::new(payload.clone()))
                        } else {
                            Core::Inr(Box::new(payload.clone()))
                        },
                        ctx,
                    )
                    .map_err(|e| {
                        CheckError::new(format!(
                            "{} :! {} ({e})",
                            pretty_core(payload, &self.gnames),
                            pretty_value(&exp, ctx.len(), &self.gvals, &self.gnames),
                        ))
                    })?;
                self.expect_conv(&inferred, &exp, ctx, payload)
            }
        }
    }

    /// Check `quot_mk a` against an expected type: it must unfold to a
    /// quotient, and the payload checks against the carrier.
    fn check_quot_mk(
        &self,
        payload: &Core,
        expected: &Value,
        ctx: &Ctx,
    ) -> Result<(), CheckError> {
        let mut fuel = FUEL_LIMIT;
        let exp = whnf(expected, &self.gvals, &mut fuel)?;
        match &exp {
            Value::Quotient(dom, _) => {
                // `dom: &Box<Value>` coerces to `&Value` for checking.
                self.check(payload, dom, ctx)
            }
            _ => {
                let inferred = self
                    .infer(
                        &Core::QuotMk(Box::new(payload.clone())),
                        ctx,
                    )
                    .map_err(|e| {
                        CheckError::new(format!(
                            "{} :! {} ({e})",
                            pretty_core(payload, &self.gnames),
                            pretty_value(&exp, ctx.len(), &self.gvals, &self.gnames),
                        ))
                    })?;
                self.expect_conv(&inferred, &exp, ctx, payload)
            }
        }
    }

    fn check_let(
        &self,
        ann: &Option<Box<Core>>,
        val: &Core,
        body: &Core,
        expected: Option<&Value>,
        ctx: &Ctx,
    ) -> Result<(), CheckError> {
        let ann_v: Value = match ann {
            Some(a) => {
                let av = self.check_ty(a, ctx)?;
                self.is_type_value(&av, ctx)?;
                self.check(val, &av, ctx)?;
                av
            }
            None => self.infer(val, ctx)?,
        };
        let val_v = eval(val, &ctx.values, &self.gvals)?;
        let mut ctx2 = ctx.clone();
        ctx2.push(ann_v, val_v);
        match expected {
            Some(exp) => self.check(body, exp, &ctx2),
            None => {
                self.infer(body, &ctx2)?;
                Ok(())
            }
        }
    }

    #[allow(dead_code)]
    fn ctx_len_unused(&self) {
        let _ = Ctx::default().len();
        let _ = Ctx::default().pop();
    }
}

fn whnfed(v: &Value, c: &Checker) -> Value {
    let mut fuel = FUEL_LIMIT;
    whnf(v, &c.gvals, &mut fuel).unwrap_or_else(|_| v.clone())
}

/// Fresh ambiguous sort core (`Type(?a)`, typical ambiguity). Every call mints
/// an independent variable — shares nothing.
fn fresh_sort() -> Core {
    Core::Sort(Sort::Type(Level::Var(fresh_level_var())))
}

/// The type of the primitive eliminator, `(A:Type(?a)) -> Void -> A`, as a
/// closed value (empty captured environment; `Bound(1)` is the outer `A`).
/// `A` ranges over any level (vacuous elimination smuggles nothing); each
/// `infer` call mints a fresh variable, so primitives are level-polymorphic
/// with no constraints of their own.
fn absurd_type() -> Value {
    Value::Pi {
        name: "A".to_string(),
        dom: Box::new(Value::Sort(Sort::Type(Level::Var(fresh_level_var())))),
        cod: Closure::new(
            Vec::new(),
            Core::Pi {
                name: "_".to_string(),
                dom: Box::new(Core::Void),
                cod: Box::new(Core::Bound(1)),
            },
        ),
    }
}

/// The type of the primitive dependent eliminator:
/// `(A:Type(?a)) -> (B:(A -> Type(?b))) -> (P:(SigmaAB -> Type(?p)))
///  -> ((a:A) -> (b:B a) -> P (a, b)) -> (p:SigmaAB) -> P p`,
/// as a closed core term evaluated once in the empty environment.
/// (Hand-built *values* are impossible here — unlike `absurd_type`, whose
/// domains are closed, these domains mention outer binders, so only closures
/// over a core term can name them. The core below is closed, so evaluating
/// it touches just the top domain.)
/// Binder layout outer→inner with de Bruijn index at each use site:
/// - `B`'s type `A -> *` under `[A]`: `A` is `Bound(0)`.
/// - `P`'s domain `SigmaAB` under `[A,B]`: `A`/`B` are `Bound(1)`.
/// - `f`'s type under `[A,B,P]`: `A` is `Bound(2)`.
/// - `p`'s type under `[A,B,P,f]`: `A`/`B` are `Bound(3)`.
/// - result `P p` under `[A,B,P,f,p]`: `P` is `Bound(2)`.
/// A cross-check test below asserts conversion with the elaborated surface
/// spelling, so any index slip fails loudly rather than silently.
fn sig_rect_type() -> Result<Value, EvalError> {
    // Sort positions below share nothing: each `star()` call mints an
    // independent ambiguous level (so e.g. `A`, `B`, `P` vary freely).
    let star = fresh_sort;
    let b = Core::Bound;
    let app = |f: Core, a: Core| Core::App(Box::new(f), Box::new(a));
    let pair = |a: Core, b: Core| Core::Pair(Box::new(a), Box::new(b));
    let pi = |name: &str, dom: Core, cod: Core| Core::Pi {
        name: name.to_string(),
        dom: Box::new(dom),
        cod: Box::new(cod),
    };
    let sigma = |name: &str, dom: Core, cod: Core| Core::Sigma {
        name: name.to_string(),
        dom: Box::new(dom),
        cod: Box::new(cod),
    };
    // `SigmaAB = (x:A) and B x` under `[A,B]`.
    let sigma_ab = sigma("x", b(1), app(b(1), b(0)));
    let core = pi(
        "A",
        star(),
        pi(
            "B",
            pi("_", b(0), star()),
            pi(
                "P",
                pi("_", sigma_ab, star()),
                pi(
                    "f",
                    // `(a:A) -> (b:B a) -> P (a, b)`: `P` takes the PAIR
                    // (single application), not curried args.
                    pi("a", b(2), pi("b", app(b(2), b(0)), app(b(2), pair(b(1), b(0))))),
                    pi(
                        "p",
                        sigma("x", b(3), app(b(3), b(0))),
                        app(b(2), b(0)),
                    ),
                ),
            ),
        ),
    );
    let empty: Env = Vec::new();
    eval(&core, &empty, &GlobalVals::new())
}

/// The type of the primitive sum eliminator:
/// `(A:Type(?a)) -> (B:Type(?b)) -> (P:((A or B) -> Type(?p)))
///  -> ((a:A) -> P (inl a)) -> ((b:B) -> P (inr b)) -> (e:A or B) -> P e`,
/// as a closed core term evaluated once in the empty environment (same
/// technique as `sig_rect_type`: open domains force the core+closures route).
/// Binder layout outer→inner with de Bruijn index at each use site:
/// - `P`'s domain `A or B` under `[A,B]`: `A`/`B` are `Bound(1)`/`Bound(0)`.
/// - `f`'s codomain `P (inl a)` under `[A,B,P,a]`: `P` is `Bound(1)`.
/// - `g`'s codomain `P (inr b)` under `[A,B,P,f,b]`: `P` is `Bound(2)`.
/// - `e`'s type `A or B` under `[A,B,P,f,g]`: `A`/`B` are `Bound(4)`/`Bound(3)`.
/// - result `P e` under `[A,B,P,f,g,e]`: `P` is `Bound(3)`.
/// A cross-check test below asserts conversion with the elaborated surface
/// spelling, so any index slip fails loudly rather than silently.
fn either_rect_type() -> Result<Value, EvalError> {
    // Sort positions below share nothing: each `star()` call mints an
    // independent ambiguous level (so e.g. `A`, `B`, `P` vary freely).
    let star = fresh_sort;
    let b = Core::Bound;
    let app = |f: Core, a: Core| Core::App(Box::new(f), Box::new(a));
    let pi = |name: &str, dom: Core, cod: Core| Core::Pi {
        name: name.to_string(),
        dom: Box::new(dom),
        cod: Box::new(cod),
    };
    let either = |a: Core, c: Core| Core::Either(Box::new(a), Box::new(c));
    let inl = |a: Core| Core::Inl(Box::new(a));
    let inr = |c: Core| Core::Inr(Box::new(c));
    // `A or B` under `[A,B]`.
    let either_ab = either(b(1), b(0));
    let core = pi(
        "A",
        star(),
        pi(
            "B",
            star(),
            pi(
                "P",
                pi("_", either_ab, star()),
                pi(
                    "f",
                    // `(a:A) -> P (inl a)` under `[A,B,P]`.
                    pi("a", b(2), app(b(1), inl(b(0)))),
                    pi(
                        "g",
                        // `(b:B) -> P (inr b)`: b-type `B` under `[A,B,P,f]`
                        // (len 4, `B` level 1 → `Bound(2)`); body under
                        // `[A,B,P,f,b]` (len 5, `P` level 2 → `Bound(2)`).
                        pi("b", b(2), app(b(2), inr(b(0)))),
                        pi(
                            "e",
                            either(b(4), b(3)),
                            app(b(3), b(0)),
                        ),
                    ),
                ),
            ),
        ),
    );
    let empty: Env = Vec::new();
    eval(&core, &empty, &GlobalVals::new())
}

/// The type of primitive W introduction:
/// `(A:Type(?a)) -> (B:(A->Type(?b))) -> (a:A) -> (f:(B a) -> W A B) -> W A B`,
/// as a closed core term evaluated once in the empty environment (same
/// technique as `sig_rect_type`: open domains force the core+closures route).
/// Binder layout with de Bruijn index at each use site:
/// - `B`'s type `A -> *` under `[A]`: `A` is `Bound(0)`.
/// - `a`'s type `A` under `[A,B]`: `Bound(1)`.
/// - `f`'s type `(B a) -> W A B` under `[A,B,a]`: `B a` is
///   `App(Bound(1), Bound(0))`, `W A B` is `App(App(W, Bound(2)), Bound(1))`.
/// - result `W A B` under `[A,B,a,f]`: `App(App(W, Bound(3)), Bound(2))`.
/// A cross-check test below asserts conversion with the elaborated surface
/// spelling, so any index slip fails loudly rather than silently.
fn sup_type() -> Result<Value, EvalError> {
    // Sort positions below share nothing: each `star()` call mints an
    // independent ambiguous level (so e.g. `A`, `B`, `P` vary freely).
    let star = fresh_sort;
    let b = Core::Bound;
    let app = |f: Core, a: Core| Core::App(Box::new(f), Box::new(a));
    let pi = |name: &str, dom: Core, cod: Core| Core::Pi {
        name: name.to_string(),
        dom: Box::new(dom),
        cod: Box::new(cod),
    };
    let core = pi(
        "A",
        star(),
        pi(
            "B",
            pi("_", b(0), star()),
            pi(
                "a",
                b(1),
                pi(
                    "f",
                    pi("_", app(b(1), b(0)), app(app(Core::W, b(3)), b(2))),
                    app(app(Core::W, b(3)), b(2)),
                ),
            ),
        ),
    );
    let empty: Env = Vec::new();
    eval(&core, &empty, &GlobalVals::new())
}

/// The type of the primitive quotient eliminator:
/// `(A:Type?a) -> (R:(A->A->Type?r)) -> (B:Type?b) -> (f:(A->B))
///  -> (h:(a:A)->(b:A)->(R a b)->LEIB(B,f a,f b)) -> (q:Quot A R) -> B`,
/// where `LEIB(T,x,y) := (Q2:(T->*)) -> Q2 x -> Q2 y` (Leibniz, inlined —
/// `path.sig` defines this shape, so these proofs check against `path`).
/// Positions vary freely (unconstrained fresh levels each `infer` call).
/// Binder layout outer→inner with de Bruijn index at each use site:
/// - `R`'s type under `[A]`: `A` is `Bound(0)`; inner dom under `[A,x]`: `Bound(1)`.
/// - `f`'s type under `[A,R,B]`: `A` is `Bound(2)`; codomain one deeper:
///   `B` is `Bound(1)`.
/// - `h`'s `a`-type under `[A,R,B,f]`: `Bound(3)`; `b`-type under `+[a]`: `Bound(4)`;
///   `R a b` under `+[a,b]`: `R`/`a`/`b` are `Bound(4)`/`Bound(1)`/`Bound(0)`.
/// - `LEIB` is the codomain, so one deeper (base len 7): `T=B` is `Bound(4)`;
///   under `+[Q2]`: `Q2` is `Bound(0)`, `f a` is `App(Bound(4), Bound(3))`;
///   under `+[_]`: `Q2` is `Bound(1)`, `f b` is `App(Bound(5), Bound(3))`.
/// - `q`'s type under `[A,R,B,f,h]`: `Quotient(Bound(4), Bound(3))`.
/// - result `B` under `+[q]`: `Bound(3)`.
/// A cross-check test below asserts conversion with the elaborated surface
/// spelling, so any index slip fails loudly rather than silently.
fn quot_lift_type() -> Result<Value, EvalError> {
    let b = Core::Bound;
    let app = |f: Core, a: Core| Core::App(Box::new(f), Box::new(a));
    let pi = |name: &str, dom: Core, cod: Core| Core::Pi {
        name: name.to_string(),
        dom: Box::new(dom),
        cod: Box::new(cod),
    };
    let star = Core::Sort(Sort::Star);
    // LEIB(B, f a, f b), scoped one deeper than `h`'s domain (codomains live
    // under one more binder): base len 7 `[A,R,B,f,a,b,h]`, `+[Q2]` len 8,
    // `+[_]` len 9. `T=B` is `Bound(4)`; under `+[Q2]`: `Q2` is `Bound(0)`,
    // `f a` is `App(Bound(4), Bound(3))`; under `+[_]`: `Q2` is `Bound(1)`,
    // `f b` is `App(Bound(5), Bound(3))`.
    let leib = pi(
        "Q2",
        pi("_", b(4), star.clone()),
        pi(
            "_",
            app(b(0), app(b(4), b(3))),
            app(b(1), app(b(5), b(3))),
        ),
    );
    let core = pi(
        "A",
        fresh_sort(),
        pi(
            "R",
            pi("_", b(0), pi("_", b(1), fresh_sort())),
            pi(
                "B",
                fresh_sort(),
                pi(
                    "f",
                    // Codomain one deeper: `B` is `Bound(1)` here.
                    pi("_", b(2), b(1)),
                    pi(
                        "h",
                        pi(
                            "a",
                            b(3),
                            pi(
                                "b",
                                b(4),
                                pi("_", app(app(b(4), b(1)), b(0)), leib),
                            ),
                        ),
                        pi(
                            "q",
                            Core::Quotient(Box::new(b(4)), Box::new(b(3))),
                            b(3),
                        ),
                    ),
                ),
            ),
        ),
    );
    let empty: Env = Vec::new();
    eval(&core, &empty, &GlobalVals::new())
}

/// The type of the soundness axiom:
/// `(A:Type?a) -> (R:(A->A->Type?r)) -> (a:A) -> (b:A) -> (h:R a b)
///  -> LEIB(Quot A R, quot_mk a, quot_mk b)`,
/// with `LEIB` inlined as above (so proofs check against `path`). Stuck
/// primitive (no iota — like `Absurd`).
/// Layout under `[A,R,a,b,h]` (len 5): `Q` is `Quotient(Bound(4), Bound(3))`;
/// `quot_mk a`/`quot_mk b` are `QuotMk(Bound(2))`/`QuotMk(Bound(1))`; under
/// `+[Q2]`: `Q2` is `Bound(0)`, `mk a` shifts to `QuotMk(Bound(3))`; under
/// `+[_]`: `Q2` is `Bound(1)`, `mk b` shifts to `QuotMk(Bound(3))`.
fn quot_sound_type() -> Result<Value, EvalError> {
    let b = Core::Bound;
    let app = |f: Core, a: Core| Core::App(Box::new(f), Box::new(a));
    let pi = |name: &str, dom: Core, cod: Core| Core::Pi {
        name: name.to_string(),
        dom: Box::new(dom),
        cod: Box::new(cod),
    };
    let star = Core::Sort(Sort::Star);
    let quot = Core::Quotient(Box::new(b(4)), Box::new(b(3)));
    let leib = pi(
        "Q2",
        pi("_", quot, star.clone()),
        pi(
            "_",
            app(b(0), Core::QuotMk(Box::new(b(3)))),
            app(b(1), Core::QuotMk(Box::new(b(3)))),
        ),
    );
    let core = pi(
        "A",
        fresh_sort(),
        pi(
            "R",
            pi("_", b(0), pi("_", b(1), fresh_sort())),
            pi(
                "a",
                b(1),
                pi(
                    "b",
                    b(2),
                    pi("_", app(app(b(2), b(1)), b(0)), leib),
                ),
            ),
        ),
    );
    let empty: Env = Vec::new();
    eval(&core, &empty, &GlobalVals::new())
}

/// The type of the primitive dependent quotient eliminator:
/// `(A:Type?a) -> (R:(A->A->Type?r)) -> (P:((Quot A R) -> *))
///  -> (f:(a:A) -> P (quot_mk a))
///  -> (coh:(a:A)->(b:A)->(h:R a b)->LEIB(P (quot_mk b), transported, f b))
///  -> (q:Quot A R) -> P q`,
/// where `transported := quot_sound A R a b h P (f a)` (Leibniz transport —
/// an application chain, no `path` reference).
/// NOTE the motive is `*`-valued, unlike every other eliminator: Leibniz
/// transport applies the proof to `P` itself, which requires `P : Q -> *`
/// (exactly why `path_subst` pins its motive) — so the builder pins `*`
/// here rather than minting a variable. Large-motive coherence is
/// inexpressible — the principled boundary (cf. Lean's `Quot.ind`,
/// which targets `Prop` for the same reason).
/// Layout: `P`'s type under `[A,R]` (domain position): `Pi(_, Quotient(Bound(1), Bound(0)), *)`;
/// `f`'s codomain under `[A,R,P,a]` (one deeper): `App(Bound(1), QuotMk(Bound(0)))`;
/// `coh`'s `a`/`b`-types under `[A,R,P,f]`/`+[a]`: `Bound(3)`/`Bound(4)`;
/// `R a b` under `+[a,b]`: `App(App(Bound(4), Bound(1)), Bound(0))`;
/// `LEIB` under `+[a,b,h]` (len 7, levels A0 R1 P2 f3 a4 b5 h6):
/// `T := App(Bound(4), QuotMk(Bound(0)))`; `e_ab` (sound-spine) and
/// `transported` shift under `+[Q2]` (len 8): `A`/`R`/`a`/`b`/`h` are
/// `Bound(7/6/3/2/1)`, `P`/`f` are `Bound(5)`/`Bound(4)`; under `+[_]`
/// (len 9): `Q2` is `Bound(1)`, `f b` is `App(Bound(5), Bound(3))`.
/// `q`'s type under `[A,R,P,f,coh]`: `Quotient(Bound(4), Bound(3))`;
/// result `P q` under `+[q]`: `App(Bound(3), Bound(0))`.
fn quot_ind_type() -> Result<Value, EvalError> {
    let b = Core::Bound;
    let app = |f: Core, a: Core| Core::App(Box::new(f), Box::new(a));
    let pi = |name: &str, dom: Core, cod: Core| Core::Pi {
        name: name.to_string(),
        dom: Box::new(dom),
        cod: Box::new(cod),
    };
    let star = Core::Sort(Sort::Star);
    // `e_ab := quot_sound A R a b h`, under `+[Q2]` (len 8).
    let e_ab = app(
        app(
            app(app(app(Core::QuotSound, b(7)), b(6)), b(3)),
            b(2),
        ),
        b(1),
    );
    // `transported := e_ab P (f a)`, under `+[Q2]` (len 8).
    let transported = app(app(e_ab, b(5)), app(b(4), b(3)));
    // `T := P (quot_mk b)`, under `+[a,b,h]` (len 7): `P` is `Bound(4)`,
    // `b` is `Bound(1)`.
    let t_fam = app(b(4), Core::QuotMk(Box::new(b(1))));
    let leib = pi(
        "Q2",
        pi("_", t_fam, star.clone()),
        pi(
            "_",
            app(b(0), transported),
            app(b(1), app(b(5), b(3))),
        ),
    );
    let core = pi(
        "A",
        fresh_sort(),
        pi(
            "R",
            pi("_", b(0), pi("_", b(1), fresh_sort())),
            pi(
                "P",
                pi("_", Core::Quotient(Box::new(b(1)), Box::new(b(0))), star.clone()),
                pi(
                    "f",
                    // Codomain one deeper: `P` is `Bound(1)` here.
                    pi("a", b(2), app(b(1), Core::QuotMk(Box::new(b(0))))),
                    pi(
                        "coh",
                        pi(
                            "a",
                            b(3),
                            pi(
                                "b",
                                b(4),
                                pi("_", app(app(b(4), b(1)), b(0)), leib),
                            ),
                        ),
                        pi(
                            "q",
                            Core::Quotient(Box::new(b(4)), Box::new(b(3))),
                            app(b(3), b(0)),
                        ),
                    ),
                ),
            ),
        ),
    );
    let empty: Env = Vec::new();
    eval(&core, &empty, &GlobalVals::new())
}

/// The type of the primitive W eliminator:
/// `(A:Type(?a)) -> (B:(A->Type(?b))) -> (P:(W A B -> Type(?p)))
///  -> (s:(a:A) -> (f:(B a) -> W A B) -> ((b:B a) -> P (f b))
///  -> P (sup A B a f)) -> (w:W A B) -> P w`,
/// as a closed core term evaluated once in the empty environment.
/// Binder layout with de Bruijn index at each use site:
/// - `P`'s domain `(W A B -> *)` under `[A,B]`: `W A B` is
///   `App(App(W, Bound(1)), Bound(0))`.
/// - `s`'s `a`-domain `A` under `[A,B,P]`: `Bound(2)`.
/// - `s`'s `f`-domain `(B a) -> W A B` under `[A,B,P,a]`: `B a` is
///   `App(Bound(2), Bound(0))`, `W A B` is `App(App(W, Bound(3)), Bound(2))`.
/// - `s`'s `ih`-domain `B a` under `[A,B,P,a,f]`: `App(Bound(3), Bound(1))`;
///   its codomain `P (f b)` under `+[b]`: `App(Bound(3), App(Bound(1),
///   Bound(0)))`.
/// - `s`'s result `P (sup A B a f)` under `[A,B,P,a,f]`: `P` is `Bound(3)`,
///   `sup`-spine `App(App(App(App(Sup, Bound(4)), Bound(3)), Bound(1)),
///   Bound(0))`.
/// - `w`'s type `W A B` under `[A,B,P,s]`: `App(App(W, Bound(3)), Bound(2))`.
/// - result `P w` under `[A,B,P,s,w]`: `App(Bound(3), Bound(0))`.
/// A cross-check test below asserts conversion with the elaborated surface
/// spelling, so any index slip fails loudly rather than silently.
fn w_rect_type() -> Result<Value, EvalError> {
    // Sort positions below share nothing: each `star()` call mints an
    // independent ambiguous level (so e.g. `A`, `B`, `P` vary freely).
    let star = fresh_sort;
    let b = Core::Bound;
    let app = |f: Core, a: Core| Core::App(Box::new(f), Box::new(a));
    let pi = |name: &str, dom: Core, cod: Core| Core::Pi {
        name: name.to_string(),
        dom: Box::new(dom),
        cod: Box::new(cod),
    };
    let core = pi(
        "A",
        star(),
        pi(
            "B",
            pi("_", b(0), star()),
            pi(
                "P",
                pi(
                    "_",
                    app(app(Core::W, b(1)), b(0)),
                    star(),
                ),
                pi(
                    "s",
                    pi(
                        "a",
                        b(2),
                        pi(
                            "f",
                            pi(
                                "_",
                                app(b(2), b(0)),
                                app(app(Core::W, b(4)), b(3)),
                            ),
                            pi(
                                "ih",
                                pi(
                                    "b",
                                    app(b(3), b(1)),
                                    app(b(3), app(b(1), b(0))),
                                ),
                                app(
                                    b(3),
                                    app(app(app(app(Core::Sup, b(5)), b(4)), b(2)), b(1)),
                                ),
                            ),
                        ),
                    ),
                    pi(
                        "w",
                        app(app(Core::W, b(3)), b(2)),
                        app(b(2), b(0)),
                    ),
                ),
            ),
        ),
    );
    let empty: Env = Vec::new();
    eval(&core, &empty, &GlobalVals::new())
}

/// The type of the primitive unit eliminator:
/// `(P:(Unit -> Type(?p))) -> (b:P ()) -> (u:Unit) -> P u`,
/// as a closed core term evaluated once in the empty environment (same
/// technique as `sig_rect_type`: open domains force the core+closures route).
/// Binder layout with de Bruijn index at each use site (`Pt` is the unit
/// value core):
/// - `P`'s domain `Unit -> *` is closed.
/// - `b`'s type `P ()` under `[P]`: `P` is `Bound(0)`.
/// - result `P u` under `[P,b,u]`: `P` is `Bound(2)`, `u` is `Bound(0)`.
/// A cross-check test below asserts conversion with the elaborated surface
/// spelling, so any index slip fails loudly rather than silently.
fn unit_rect_type() -> Result<Value, EvalError> {
    // Sort positions below share nothing: each `star()` call mints an
    // independent ambiguous level (so e.g. `A`, `B`, `P` vary freely).
    let star = fresh_sort;
    let b = Core::Bound;
    let app = |f: Core, a: Core| Core::App(Box::new(f), Box::new(a));
    let pi = |name: &str, dom: Core, cod: Core| Core::Pi {
        name: name.to_string(),
        dom: Box::new(dom),
        cod: Box::new(cod),
    };
    let pt = Core::Pt;
    let core = pi(
        "P",
        pi("_", Core::Unit, star()),
        pi(
            "b",
            app(b(0), pt.clone()),
            pi("u", Core::Unit, app(b(2), b(0))),
        ),
    );
    let empty: Env = Vec::new();
    eval(&core, &empty, &GlobalVals::new())
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Parse + scope + check a program. Never panics on user input; per-def
/// failures are recorded in the returned [`Checker`].
pub fn check_program(src: &str) -> Result<Checker, String> {
    let decls = crate::parser::parse_program(src)
        .map_err(|e| format!("{e} at {} ({})", e.span.start, snippet(src, e.span)))?;
    let mut checker = Checker::new();
    checker.source.replace(src.to_string());
    checker.check_program(decls);
    Ok(checker)
}

fn snippet(src: &str, span: Span) -> String {
    use crate::lexer::line_col;
    let (l, c) = line_col(src, span.start);
    let line = src.lines().nth(l.saturating_sub(1)).unwrap_or("");
    format!("line {l}, col {c}: {line:.80}")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ok(src: &str) -> Checker {
        let c = check_program(src).expect("parse failed");
        assert!(!c.has_errors(), "expected OK, got:\n{}", c.report());
        c
    }

    fn fails(src: &str) -> Checker {
        let c = check_program(src).expect("parse failed");
        assert!(c.has_errors(), "expected failure, got OK:\n{}", c.report());
        c
    }

    #[test]
    fn identity_checks() {
        ok("def id : (T : *) -> T -> T = \\T x. x;");
    }

    #[test]
    fn const_checks() {
        ok("def const : (A : *) -> (B : *) -> A -> B -> A = \\A B x y. x;");
    }

    #[test]
    fn sorts_stratified() {
        // Axioms: `* : Type0`, `Type0 : Type1` ...
        ok("def a : Type0 = *;");
        ok("def b : Type0 = * -> *;");
        ok("def c : Type1 = Type0;");
        // ... but no level contains itself (Girard-analog, checked directly)
        // ...
        fails("def bad : Type0 = Type0;");
        // ... and `*` lives in `Type0`, not in `*` (no `* : *`).
        fails("def bad : * = *;");
        // Typical ambiguity: bare `Type` elaborates and generalizes.
        ok("def t : Type = Type;");
        ok("def up : Type1 = Type0 -> Type0;");
    }

    #[test]
    fn impredicative_pi() {
        // Large domain, `*`-codomain: accepted (impredicative into `*` at any
        // domain level). Here `P` ranges over type constructors, yet the
        // result stays small.
        ok("def polyid : (P : * -> *) -> (u : *) -> P u -> P u = \\P u x. x;");
        // But `T -> *` (small domain, `*`-as-codomain-term) lives in `Type0`,
        // not `*` (predicative above `*` — the codomain *term* `*` is itself
        // large).
        fails("def f : * = (T : *) -> T -> *;");
        ok("def f : Type0 = (T : *) -> T -> *;");
        // Quantifying over a sort is well-formed (every level has a successor)
        // and lands one level up.
        ok("def f : Type1 = (A : Type0) -> A -> A;");
        fails("def f : Type0 = (A : Type0) -> A -> A;");
    }

    #[test]
    fn hurkens_v_stays_large() {
        // Hurkens' V needs `A -> *` at small level to close in `*`; here that
        // arrow lives in `Type0`, so V lands in `Type0` — the paradox's
        // self-membership switch (`V : *`) is rejected. (If this `fails` ever
        // flips to `ok`, the design is inconsistent — see the header gate.)
        fails("def v : * = (A:*) -> ((A -> *) -> (A -> *)) -> A -> *;");
        ok("def v : Type0 = (A:*) -> ((A -> *) -> (A -> *)) -> A -> *;");
    }

    #[test]
    fn universe_polymorphic_reuse() {
        // One `id` serves two pinned levels: each reference mints a fresh
        // instance, so the `? = 0` and `? = 5` requirements never meet.
        // (With shared/floating levels this cycles and fails.)
        ok("def id : (A:Type) -> A -> A = \\A x. x;");
        ok("def id : (A:Type) -> A -> A = \\A x. x; \
            def f : (X:Type0) -> X -> X = id; \
            def g : (X:Type5) -> X -> X = id;");
    }

    #[test]
    fn user_case_analysis_reused_at_two_levels() {
        // A user-written eliminator over ambiguous levels, used on `*`-data
        // with a `*`-motive AND on `Type0`-data with a `Type1`-motive.
        ok("def mycase : (A:Type) -> (B:Type) -> (P:((A or B) -> Type)) -> (f:(a:A) -> P (inl a)) -> (g:(b:B) -> P (inr b)) -> (e:A or B) -> P e = \\A B P f g e. match e return P { inl a => f a | inr b => g b }; \
            def u1 : Unit = mycase Unit Unit (\\_. Unit) (\\_. ()) (\\_. ()) (inl () : Unit or Unit); \
            def u2 : Type1 = mycase Type0 Type0 (\\_. Type1) (\\_. Type0) (\\_. Type0) (inl Unit : Type0 or Type0);");
    }

    #[test]
    fn leibniz_path_suite() {
        // Definitional Leibniz equality, living in `*`, eliminating
        // definitionally (motive domains are `(T -> *)`-typed = `#`-domains
        // with `*`-codomains, so `(#,*)` keeps every step small).
        ok("def path : (T:*) -> (a:T) -> (b:T) -> * = \\T a b. (P:(T -> *)) -> (P a) -> (P b);");
        ok("def path : (T:*) -> (a:T) -> (b:T) -> * = \\T a b. (P:(T -> *)) -> (P a) -> (P b); \
            def path_subst : (T:*) -> (a:T) -> (b:T) -> (p:path T a b) -> (M:(T -> *)) -> (v:M a) -> M b = \\T a b p M v. p M v;");
        ok("def path : (T:*) -> (a:T) -> (b:T) -> * = \\T a b. (P:(T -> *)) -> (P a) -> (P b); \
            def id_path : (T:*) -> (v:T) -> path T v v = \\T v P h. h;");
        ok("def path : (T:*) -> (a:T) -> (b:T) -> * = \\T a b. (P:(T -> *)) -> (P a) -> (P b); \
            def id_path : (T:*) -> (v:T) -> path T v v = \\T v P h. h; \
            def path_symm : (T:*) -> (a:T) -> (b:T) -> (p:path T a b) -> path T b a = \\T a b p. p (\\i. path T i a) (id_path T a);");
    }

    #[test]
    fn bad_application_rejected() {
        // `f` takes one arg; the second application hits non-function `Type0`.
        fails("def f : * -> Type0 = \\x. x; def b : Type0 = f * *;");
    }

    #[test]
    fn argument_is_checked_despite_reduction() {
        // `k` ignores its 2nd arg; a bad 2nd arg (`Type0` never fits in `Unit`)
        // must still fail even though the application would reduce past it.
        fails("def k : (T : *) -> T -> Type0 = \\T x. *; def b : Type0 = k Unit Type0;");
    }

    #[test]
    fn annotated_let_checks() {
        // `* : Type0`, so a let-bound `*` needs a `Type0` annotation (or inference).
        ok("def a : Type0 = let X : Type0 = * in X;");
        ok("def a : Type0 = let X = * in X;");
    }

    #[test]
    fn eta_holds() {
        // `\\x. f x` checks against the same Pi as `f`.
        ok("def e : ((T : *) -> T -> T) -> (T : *) -> T -> T = \\f. \\T x. f T x;");
    }

    #[test]
    fn forward_ref_rejected() {
        fails("def a : Type0 = b; def b : Type0 = *;");
    }

    #[test]
    fn self_ref_rejected() {
        fails("def a : Type0 = a;");
    }

    #[test]
    fn unbound_rejected() {
        fails("def a : Type0 = nope;");
    }

    #[test]
    fn duplicate_rejected() {
        fails("def a : Type0 = *; def a : Type0 = *;");
    }

    #[test]
    fn dependent_codomain_substitutes() {
        // `\\T x. x` against `(T : *) -> (x : T) -> T`: 2nd binder type is `T`.
        ok("def id : (T : *) -> (x : T) -> T = \\T x. x;");
        fails("def id : (T : *) -> (x : T) -> Unit = \\T x. x;");
    }

    #[test]
    fn void_is_empty_but_wellformed() {
        // `Void : *`, and `absurd` eliminates into any small type.
        ok("def v : * = Void;");
        ok("def exfalso : (A:*) -> Void -> A = \\A v. absurd A v;");
        ok("def absurdVoid : (v:Void) -> Void = \\v. absurd Void v;");
    }

    #[test]
    fn void_has_no_intro() {
        // No lambda fits `Void`, sorts aren't its inhabitants ...
        fails("def bad : Void = \\x. x;");
        fails("def bad : Void = *;");
        // ... and `absurd`'s arguments are still checked (soundness-critical:
        // `*` fits nowhere near `Void`, even in scrutinee position).
        fails("def b : * = absurd * *;");
        fails("def b : (A:*) -> A = \\A. absurd A *;");
    }

    #[test]
    fn shadowing_ok() {
        ok("def a : Type0 = let x : Type0 = * in let x : Type0 = x in x;");
        ok("def a : Type0 = let x = * in let x = x in x;");
    }

    #[test]
    fn sigma_formation_predicative() {
        // Small parts: small Sigma. (`Void` is the only closed small type.)
        ok("def s : * = (x : Void) and Void;");
        ok("def s : * = Void and Void;");
        // `(a, b)` is values only — never a type spelling.
        fails("def s : * = (Void, Void);");
        // Any `Type0` part forces `Type0` — impredicative-Sigma would claim `*`.
        fails("def bad : * = Void and *;");
        ok("def good : Type0 = Void and *;");
        fails("def bad : * = (u:*) -> ((A : * -> *) and A u);");
        ok("def good : Type0 = (u:*) -> ((A : * -> *) and A u);");
    }

    #[test]
    fn pair_intro_projections() {
        ok("def p : (v:Void) -> ((x:Void) and Void) = \\v. (absurd Void v, absurd Void v);");
        ok("def f : (p:(x:Void) and Void) -> Void = \\p. fst p;");
        ok("def s : (A:*) -> (B:A -> *) -> (p:(x:A) and B x) -> B (fst p) = \\A B p. snd p;");
        // Iota computes: `fst`/`snd` of a literal reduce in conversion.
        ok("def t : (v:Void) -> Void = \\v. fst ((absurd Void v), (absurd Void v));");
        // `fst f x` is `(fst f) x`, not `fst (f x)` (needs no annotation
        // since every part is neutral — lambdas as parts would, see below).
        ok("def t : (f:Void -> Void) -> (v:Void) -> Void = \\f v. fst (f, (absurd Void v)) (absurd Void v);");
    }

    #[test]
    fn diverging_term_is_checked_error_not_crash() {
        // Totality: fuel/depth-bounded evaluation turns divergence into a
        // clean per-def error — even in annotation position (this used to
        // overflow the host stack).
        fails("def bad : (\\x. x x) (\\x. x x) = *;");
    }

    #[test]
    fn w_types_match_surface_spellings() {
        // The hand-built W types must convert with the elaborated surface
        // spellings (catches de Bruijn index slips loudly — this caught three
        // across the other eliminators). The spellings use ambiguous `Type`
        // (fresh variables), matching the primitives' level-generality:
        // conversion is equality, so `*`-pinned spellings would (correctly)
        // fail against the general hand types — `*`-usability is covered by
        // the `ok(...)` tests below instead.
        fn cross(src: &str, prim: &Core) {
            let sexpr = crate::parser::parse_expr(src).expect("parse W type");
            let checker = Checker::new();
            let gmap = std::collections::HashMap::new();
            let failed: Vec<bool> = Vec::new();
            let mut scope = Scope { locals: Vec::new(), globals: &gmap, failed: &failed, wild_counter: 0, holes: Cell::new(0) };
            let core = scope_expr(&mut scope, &sexpr).expect("scope W type");
            let ctx = Ctx::default();
            checker.infer_sort(&core, &ctx).expect("W type well-formed");
            let empty: Env = Vec::new();
            let surface_val = eval(&core, &empty, &checker.gvals).expect("eval W type");
            let prim_val = checker.infer(prim, &ctx).expect("infer W primitive");
            let mut fuel = FUEL_LIMIT;
            let eq = conv(0, &surface_val, &prim_val, &checker.gvals, &mut fuel, 0, &mut Vec::new())
                .expect("conv W type");
            if !eq {
                let ps = crate::core::pretty_value(&surface_val, 0, &checker.gvals, &[]);
                let qs = crate::core::pretty_value(&prim_val, 0, &checker.gvals, &[]);
                panic!("hand-built W type differs from surface spelling: {src}\n surface: {ps}\n prim:    {qs}");
            }
        }
        cross("(A:Type) -> (B:(A -> Type)) -> Type", &Core::W);
        cross(
            "(A:Type) -> (B:(A -> Type)) -> (a:A) -> (f:(B a) -> W A B) -> W A B",
            &Core::Sup,
        );
        cross(
            "(A:Type) -> (B:(A -> Type)) -> (P:((W A B) -> Type)) -> (s:(a:A) -> (f:(B a) -> W A B) -> ((b:B a) -> P (f b)) -> P (sup A B a f)) -> (w:W A B) -> P w",
            &Core::WRect,
        );
    }

    #[test]
    fn w_formation_intro_elim() {
        // Formation over small families.
        ok("def t : * = W Void (\\_. Void);");
        // Introduction: label plus child-function.
        ok("def t : (v:Void) -> W Void (\\_. Void) = \\v. sup Void (\\_. Void) v (\\x. absurd (W Void (\\_. Void)) x);");
        // Full eliminator checks with all explicit args.
        ok("def r : (A:*) -> (B:(A -> *)) -> (P:((w:W A B) -> *)) -> (s:(a:A) -> (f:(B a) -> W A B) -> ((b:B a) -> P (f b)) -> P (sup A B a f)) -> (w:W A B) -> P w = \\A B P s w. w_rect A B P s w;");
    }

    #[test]
    fn w_rect_iota_concrete() {
        // Closed computation through the IH machinery: quoting, IH-lambda
        // building, and nested application all run (result would stay stuck
        // if any stage failed to fire).
        ok("def t : (v:Void) -> Void = \\v. w_rect Void (\\_. Void) (\\_. Void) (\\a f ih. absurd Void a) (sup Void (\\_. Void) v (\\x. absurd (W Void (\\_. Void)) x));");
    }

    #[test]
    fn w_rect_iota_pinned_neutral() {
        // With neutral `P`/`s`, only iota closes this gap: the goal mentions
        // the reduced `s v f0 ih0` while the body infers the stuck chain.
        // Fails without `w_rect_env_redex`. (`f0` is a binder — an inline
        // `((\x. ...) b)` redex would hit the unrelated pre-existing limit
        // that head-lambda applications never infer; binders stay neutral.)
        ok("def t : (v:Void) -> (P:((w:W Void (\\_. Void)) -> *)) -> (s:(a:Void) -> (f:(Void -> W Void (\\_. Void))) -> ((b:Void) -> P (f b)) -> P (sup Void (\\_. Void) a f)) -> (f0:(Void -> W Void (\\_. Void))) -> (H:P (sup Void (\\_. Void) v f0) -> *) -> H (s v f0 (\\b. w_rect Void (\\_. Void) P s (f0 b))) -> H (w_rect Void (\\_. Void) P s (sup Void (\\_. Void) v f0)) = \\v P s f0 H h. h;");
    }

    #[test]
    fn w_rejects_nonsense() {
        // Scrutinee must be a W-tree (`v : Void` is not one).
        fails("def bad : (v:Void) -> Void = \\v. w_rect Void (\\_. Void) (\\_. Void) (\\a f ih. absurd Void a) v;");
        // ...and motives are `*`-valued.
        fails("def bad : (v:Void) -> Void = \\v. w_rect Void (\\_. Void) (\\_. *) (\\a f ih. absurd Void a) (sup Void (\\_. Void) v (\\x. absurd (W Void (\\_. Void)) x));");
        // `W` needs small families (`*` itself never fits).
        fails("def bad : * = W * (\\_. *);");
    }

    #[test]
    fn wnat_recursion_derives_bare_transport_stalls() {
        // Non-dependent `nat_rec` goes through (split family + refined step),
        // and full `nat_ind` with explicit transports checks in `nat.sig`;
        // but a BARE `z` cannot cross the `inl`-branch (the child functions
        // differ — transport, now derived, is genuinely required). So this
        // shape must keep failing.
        ok("def Bf : (Unit or Unit) -> * = \\b. match b return (\\_. *) { inl _ => Void | inr _ => Unit }; \
            def nat_rec : (P:*) -> P -> (P -> P) -> W (Unit or Unit) Bf -> P = \\P z st w. w_rect (Unit or Unit) Bf (\\_. P) (\\a f ih. match a return (\\_. P) { inl _ => z | inr u => st (ih ()) }) w;");
        fails("def Bf : (Unit or Unit) -> * = \\b. match b return (\\_. *) { inl _ => Void | inr _ => Unit }; \
            def WNat : * = W (Unit or Unit) Bf; \
            def wzero : WNat = sup (Unit or Unit) Bf (inl () : Unit or Unit) (\\x. absurd WNat x); \
            def inlCase : (P:(WNat -> *)) -> (z:P wzero) -> (f:(Void -> WNat)) -> P (sup (Unit or Unit) Bf (inl () : Unit or Unit) f) = \\P z f. z;");
    }

    #[test]
    fn nat_ind_stuck_at_sound() {
        // `nat_ind` into a non-collapsing type (`Bool`) does NOT reduce
        // through `quot_sound` (stuck axiom, no iota): computation stops
        // exactly at fully-applied `quot_sound` terms. (Unit-typed instances
        // still convert — by Unit-eta, not by reduction.)
        let base = include_str!("../examples/nat.sig");
        let stuck_src = format!(
            "{base}\ndef indBool : WNat -> Bool = nat_ind (\\_. Bool) (inl () : Bool) (\\_ _. (inr () : Bool));\ndef stuck : path Bool (indBool wtwo) (inr () : Bool) = id_path Bool (inr () : Bool);"
        );
        let checker = check_program(&stuck_src).expect("must parse");
        assert!(
            checker.has_errors(),
            "induction into Bool must get stuck at `quot_sound`"
        );
        // Control: the same computation into `Unit` converts (Unit-eta
        // collapses the stuck chain with `()` — no reduction needed).
        let ok_src = format!(
            "{base}\ndef indUnit : WNat -> Unit = nat_ind (\\_. Unit) () (\\_ _. ());\ndef indCompTest : path Unit (indUnit wtwo) () = id_path Unit ();"
        );
        let checker = check_program(&ok_src).expect("must parse");
        assert!(
            !checker.has_errors(),
            "induction into Unit must convert by Unit-eta:\n{}",
            checker.report()
        );
    }

    #[test]
    fn hole_occurs_rejected() {
        // `?0[] := ?0[] ()` would build an infinite term: occurs violation
        // is a mismatch, never an assignment (and never a hang).
        let c = Checker::new();
        let ctx = Ctx::default();
        c.ensure_meta(0, Span::empty(0), None, 0, &ctx).unwrap();
        let m = Value::Meta { id: 0, span: Span::empty(0), spine: vec![] };
        let rhs = Value::App(Box::new(m.clone()), Box::new(Value::Pt));
        assert_eq!(c.unify_inner(&m, &rhs, &ctx, 0).unwrap(), UOut::Mismatch);
    }

    #[test]
    fn hole_level_bound_rejected() {
        // Solutions may only mention levels older than the hole's oldest
        // occurrence (`?0` from the empty context cannot see level 5).
        let c = Checker::new();
        let ctx = Ctx::default();
        c.ensure_meta(1, Span::empty(0), None, 0, &ctx).unwrap();
        let m = Value::Meta { id: 1, span: Span::empty(0), spine: vec![] };
        assert_eq!(c.unify_inner(&m, &Value::Var(5), &ctx, 0).unwrap(), UOut::Mismatch);
    }

    #[test]
    fn hole_postpone_makes_progress() {
        // Flex-flex postpones; solving one side elsewhere unblocks the
        // queued pair on drain (no progress → drain simply stops).
        let c = Checker::new();
        let ctx = Ctx::default();
        c.ensure_meta(0, Span::empty(0), None, 0, &ctx).unwrap();
        c.ensure_meta(1, Span::empty(0), None, 0, &ctx).unwrap();
        let m0 = Value::Meta { id: 0, span: Span::empty(0), spine: vec![] };
        let m1 = Value::Meta { id: 1, span: Span::empty(0), spine: vec![] };
        assert_eq!(c.unify_inner(&m0, &m1, &ctx, 0).unwrap(), UOut::Defer);
        assert_eq!(c.postponed.borrow().len(), 1);
        assert_eq!(c.unify_inner(&m1, &Value::Pt, &ctx, 0).unwrap(), UOut::Eq);
        c.drain_postponed().unwrap();
        assert!(c.postponed.borrow().is_empty());
    }

    #[test]
    fn hole_same_id_equal() {
        // One unknown is itself, whatever the occurrence spines (a single
        // assignment, valid in every occurrence context, decides all uses).
        let c = Checker::new();
        let ctx = Ctx::default();
        c.ensure_meta(0, Span::empty(0), None, 0, &ctx).unwrap();
        let l = Value::Meta { id: 0, span: Span::empty(0), spine: vec![Value::Var(0)] };
        let r = Value::Meta { id: 0, span: Span::empty(0), spine: vec![Value::Var(1)] };
        assert_eq!(c.unify_inner(&l, &r, &ctx, 1).unwrap(), UOut::Eq);
        assert!(c.postponed.borrow().is_empty());
    }

    #[test]
    fn hole_nonpattern_postpones_then_errors() {
        // A non-variable spine cannot invert (Miller pattern required), so
        // the equation waits — and the end-of-def sweep reports the hole
        // instead of accepting silently.
        let c = Checker::new();
        let ctx = Ctx::default();
        c.ensure_meta(0, Span::empty(0), None, 0, &ctx).unwrap();
        let m = Value::Meta { id: 0, span: Span::empty(0), spine: vec![Value::Pt] };
        assert_eq!(c.unify_inner(&m, &Value::Unit, &ctx, 0).unwrap(), UOut::Defer);
        c.drain_postponed().unwrap();
        let err = c.unsolved_holes().expect_err("must report the hole");
        assert!(format!("{err}").contains("unsolved hole"), "got: {err}");
    }

    #[test]
    fn hole_zonk_follows_chains() {
        // Assignments compose transitively through the store.
        let c = Checker::new();
        let ctx = Ctx::default();
        c.ensure_meta(0, Span::empty(0), None, 0, &ctx).unwrap();
        c.ensure_meta(1, Span::empty(0), None, 0, &ctx).unwrap();
        let m0 = Value::Meta { id: 0, span: Span::empty(0), spine: vec![] };
        let m1 = Value::Meta { id: 1, span: Span::empty(0), spine: vec![] };
        c.assign_meta(0, m1.clone());
        assert_eq!(format!("{:?}", c.zonk_value(&m0).unwrap()), format!("{m1:?}"));
        c.assign_meta(1, Value::Pt);
        assert_eq!(c.zonk_value(&m0).unwrap(), Value::Pt);
    }

    #[test]
    fn hole_unit_and_eta_synth() {
        // Determined shapes fill directly: `()` for `Unit`, eta-expansion
        // for functions (the body hole defers like any other hole).
        ok("def u : Unit = _;");
        ok("def e : (x:Unit) -> Unit = \\x. _;");
        ok("def t : _ = ();");
    }

    #[test]
    fn hole_miller_through_app() {
        // The type hole in `id_path _ zero` is solved by the later argument
        // (`zero : ?T` forces `?T := Nat`) — synthesis through application.
        let base = include_str!("../examples/nat.sig");
        let src = format!("{base}\ndef e2 : path Nat zero zero = id_path _ zero;");
        let checker = check_program(&src).expect("must parse");
        assert!(!checker.has_errors(), "type hole must solve:\n{}", checker.report());
    }

    #[test]
    fn hole_ambiguous_errors() {
        // Nothing determines these: each fails with a located typed-hole
        // error (never a guess, never silence).
        let c = fails("def p : (A:*) -> A -> A = \\A x. _;");
        assert!(c.report().contains("unsolved hole"), "got:\n{}", c.report());
        let c2 = fails("def t : Unit = _ ();");
        assert!(c2.report().contains("cannot infer"), "got:\n{}", c2.report());
    }

    #[test]
    fn telescope_sugar_matches_plain() {
        // `def f (x:A) : B = b` elaborates exactly like the Pi/Lam form
        // (same Core after scoping): both accept, and both apply alike.
        let sugared = check_program(
            "def const (A : *) (x : A) : A = x; def t : Unit = const Unit ();",
        )
        .expect("must parse");
        assert!(!sugared.has_errors(), "sugar must check:\n{}", sugared.report());
        let plain = check_program(
            "def const : (A : *) -> (x : A) -> A = \\A x. x; def t : Unit = const Unit ();",
        )
        .expect("must parse");
        assert!(!plain.has_errors(), "plain must check:\n{}", plain.report());
    }

    #[test]
    fn codomain_inference_aliases() {
        // App-headed family bodies elaborate (their types inferred) and
        // unfold transparently at use sites — including in type position,
        // where the plain form cannot even be written.
        let src = "def path : (T:*) -> (a:T) -> (b:T) -> * = \\T a b. (P:(T -> *)) -> (P a) -> (P b);\
            def is_center (T : *) (v : T) (i : T) = path T i v;\
            def t : (T:*) -> (v:T) -> (i:T) -> * = \\T v i. is_center T v i;";
        let checker = check_program(src).expect("must parse");
        assert!(!checker.has_errors(), "aliases must check:\n{}", checker.report());
        // A term body is not a type (the inference gate, not just scoping).
        let bad = check_program("def bad (A : *) = ();").expect("must parse");
        assert!(bad.has_errors(), "term body must fail");
        assert!(bad.report().contains("not a type"), "got:\n{}", bad.report());
    }

    #[test]
    fn formation_fallback_alias() {
        // Applied aliases denoting types check in formation position
        // (neutral infer gives a type, not a sort — formation validates
        // instead of converting), while large ones still respect
        // cumulativity and aliases-as-terms still fail.
        let src = "def path : (T:*) -> (a:T) -> (b:T) -> * = \\T a b. (P:(T -> *)) -> (P a) -> (P b);\
            def is_center (T : *) (v : T) (i : T) = path T i v;\
            def t : * = is_center Unit () ();";
        let checker = check_program(src).expect("must parse");
        assert!(!checker.has_errors(), "alias in formation must check:\n{}", checker.report());
        let bad = check_program("def path : (T:*) -> (a:T) -> (b:T) -> * = \\T a b. (P:(T -> *)) -> (P a) -> (P b);\
            def is_center (T : *) (v : T) (i : T) = path T i v;\
            def bad : Unit = is_center Unit () ();");
        let checker = bad.expect("must parse");
        assert!(checker.has_errors(), "alias as term must fail");
    }

    #[test]
    fn alias_saturated_term_rejected_partial_usable() {
        // A saturated family application denotes a type and is rejected as a
        // term (inference produces the codomain type, so conversion refuses
        // it); partial applications stay usable (genuine closures);
        // formation positions are unaffected.
        // (Partial applications get the recorded codomain — coarse `*`, not
        // the body — so ascribing a more precise Pi to one fails, exactly as
        // for any family: `Type` is not `nat -> Prop`.)
        let base = "def path : (T:*) -> (a:T) -> (b:T) -> * = \\T a b. (P:(T -> *)) -> (P a) -> (P b);\
            def is_center (T : *) (v : T) (i : T) = path T i v;";
        let bad = check_program(&format!("{base} def bad : path Unit () () = is_center Unit () ();"))
            .expect("must parse");
        assert!(bad.has_errors(), "saturated alias as term must fail");
        let precise = check_program(&format!("{base} def pap : ((i:Unit) -> path Unit i i) = is_center Unit ();"))
            .expect("must parse");
        assert!(precise.has_errors(), "over-precise ascription of a partial alias must fail");
        let ok = check_program(&format!("{base}\
            def pap : ((i:Unit) -> *) = is_center Unit ();\
            def t : * = is_center Unit () ();"))
        .expect("must parse");
        assert!(!ok.has_errors(), "partial alias and formation use must check:\n{}", ok.report());
    }

    #[test]
    fn scheme_constraints_generalized() {
        // Universe constraints mentioning only internal level variables must
        // still be freshened per use: `use2` passes with and without `use1`
        // (order-independent — previously the second failed spuriously).
        let mk = |tail: &str| {
            check_program(&format!(
                "def foo (A : Type) (B : Type) : Type = (A and B);{tail}"
            ))
            .expect("must parse")
        };
        let both = mk("def use1 : Type0 = foo Unit Unit; def use2 : Type1 = foo Type0 Type0;");
        assert!(!both.has_errors(), "combined uses must check:\n{}", both.report());
        let late = mk("def use2 : Type1 = foo Type0 Type0;");
        assert!(!late.has_errors(), "lone use must check:\n{}", late.report());
    }

    #[test]
    fn sorts_not_terms() {
        // Stratification holds: sorts cannot inhabit each other as terms, so
        // the Leibniz-over-sorts route to `* == Type0` cannot even be stated
        // (the second argument fails: `Type0 : Type1`, not `Type0`).
        let src = "def path1 : (a:Type0) -> (b:Type0) -> * = \\a b. (P:(Type0 -> *)) -> P a -> P b;\
            def r1 : (a:Type0) -> path1 a a = \\a P h. h;\
            def p : path1 * Type0 = r1 *;";
        let checker = check_program(src).expect("must parse");
        assert!(checker.has_errors(), "sort equation must fail");
        assert!(checker.report().contains("large type"), "got:\n{}", checker.report());
    }

    #[test]
    fn fail_alias_rejects() {
        // Soundness gate: saturated families denote types and must never
        // check as terms — `bigalias Void` proving `Void` would make the
        // logic inconsistent. (Inference produces types, so conversion
        // rejects them: `Type(?n) :! Void`.)
        let src = include_str!("../examples/fail_alias.sig");
        let checker = check_program(src).expect("fail_alias.sig must parse");
        assert!(checker.has_errors(), "fail_alias.sig must fail");
    }

    #[test]
    fn audit_gates_reject() {
        // Soundness gates from the type-checker audit: each file's base defs
        // check while the attacks fail (smuggled families via `let`/pair
        // projection, unchecked ascriptions, unchecked `let`s in types,
        // unchecked hole solutions against universe levels, small-to-large
        // proof ascriptions).
        for (name, src) in [
            ("fail_alias_let", include_str!("../examples/fail_alias_let.sig")),
            ("fail_alias_fst", include_str!("../examples/fail_alias_fst.sig")),
            ("fail_ann", include_str!("../examples/fail_ann.sig")),
            ("fail_letann", include_str!("../examples/fail_letann.sig")),
            ("fail_hole_universe", include_str!("../examples/fail_hole_universe.sig")),
            ("fail_leib_lift", include_str!("../examples/fail_leib_lift.sig")),
        ] {
            let checker = check_program(src).unwrap_or_else(|e| panic!("{name}.sig must parse: {e}"));
            assert!(checker.has_errors(), "{name}.sig must fail");
        }
    }

    #[test]
    fn formation_validates_nested_types() {
        // `let`s with false bindings are rejected wherever they hide inside
        // types (domains, sum sides, carrier positions) — evaluation alone
        // would silently unfold them. True bindings still elaborate.
        fails("def bad : ((let X : Void = () in Unit) -> Unit) = \\x. x;");
        fails("def bad : (Unit or (let X : Void = () in Unit)) = inl ();");
        fails("def bad : (let X : Void = () in Unit) -> Unit = \\x. x;");
        fails("def bad : Quot (let X : Void = () in Unit) (\\_ _. Unit) = quot_mk ();");
        ok("def good : ((let X : Unit = () in Unit) -> Unit) = \\x. x;");
        ok("def good : (Unit or (let X : Unit = () in Unit)) = inl ();");
    }

    #[test]
    fn duplicate_def_keeps_first() {
        // A duplicate definition fails without poisoning later references to
        // the original (fail-closed: the error stays on the duplicate).
        let src = "def a : Type0 = *; def a : Type0 = *; def c : Type0 = a;";
        let checker = check_program(src).expect("must parse");
        assert!(checker.has_errors(), "the duplicate must fail");
        let report = checker.report();
        assert!(report.contains("def c (ok)"), "later refs must resolve to the original:\n{report}");
    }

    #[test]
    fn wmap_sig_checks_end_to_end() {
        // Weak maps, fibers, and quotient splicing ported from Lean (all
        // args explicit): definitions plus the computational proofs
        // (transports, both quotient maps, canonical roundtrip equation).
        // The full coherence proofs need `quot_ind` + `exists_rep` work
        // documented in the file — this test pins the ported prefix.
        let src = include_str!("../examples/wmap.sig");
        let checker = check_program(src).expect("wmap.sig must parse");
        assert!(
            !checker.has_errors(),
            "wmap.sig must check:\n{}",
            checker.report()
        );
    }

    #[test]
    fn holes_sig_checks_end_to_end() {
        // Elaborated holes: determined shapes fill (Unit, eta), the rest
        // solves through unification or errors — one file so the behavior
        // cannot drift from the core.
        let src = include_str!("../examples/holes.sig");
        let checker = check_program(src).expect("holes.sig must parse");
        assert!(
            !checker.has_errors(),
            "holes.sig must check:\n{}",
            checker.report()
        );
    }

    #[test]
    fn fail_hole_rejects() {
        // Undetermined holes fail the def (located typed-hole errors), and
        // infer-position holes ask for annotations.
        let src = include_str!("../examples/fail_hole.sig");
        let checker = check_program(src).expect("fail_hole.sig must parse");
        assert!(
            checker.has_errors(),
            "fail_hole.sig must fail"
        );
        let report = checker.report();
        assert!(report.contains("unsolved hole"), "got:\n{report}");
        assert!(report.contains("cannot infer"), "got:\n{report}");
    }

    #[test]
    fn nat_sig_checks_end_to_end() {
        // The full Nat development (W-derived formation plus Church numerals
        // with computation) lives in one file so it cannot drift from the
        // core: `include_str!` (compile-time, no cwd fragility).
        let src = include_str!("../examples/nat.sig");
        let checker = check_program(src).expect("nat.sig must parse");
        assert!(
            !checker.has_errors(),
            "nat.sig must check:\n{}",
            checker.report()
        );
    }

    #[test]
    fn funext_sig_checks_end_to_end() {
        // Derived funext (quotient classes + transport + iota-under-eta) plus
        // its first use (the `inl`-case transport of WNat induction): one file
        // so it cannot drift from the core.
        let src = include_str!("../examples/funext.sig");
        let checker = check_program(src).expect("funext.sig must parse");
        assert!(
            !checker.has_errors(),
            "funext.sig must check:\n{}",
            checker.report()
        );
    }

    #[test]
    fn unit_eta_holds() {
        // Definitional uniqueness of `()`: any `u : Unit` is convertible with
        // `()` (conversion-level Unit-eta, no axiom).
        ok("def ueta : (u:Unit) -> (P:(Unit -> *)) -> P u -> P () = \\u P x. x;");
        // The `inr`-case of WNat induction goes through on Unit-eta alone
        // (`f` vs `\\_. f ()` and `u` vs `()` both convert now).
        ok("def Bf : (Unit or Unit) -> * = \\b. match b return (\\_. *) { inl _ => Void | inr _ => Unit }; \
            def WNat : * = W (Unit or Unit) Bf; \
            def wzero : WNat = sup (Unit or Unit) Bf (inl () : Unit or Unit) (\\x. absurd WNat x); \
            def wsucc : WNat -> WNat = \\n. sup (Unit or Unit) Bf (inr () : Unit or Unit) (\\_. n); \
            def inrCase : (P:(WNat -> *)) -> (st:(n:WNat) -> P n -> P (wsucc n)) -> (f:(Unit -> WNat)) -> (ih:(u:Unit) -> P (f u)) -> P (sup (Unit or Unit) Bf (inr () : Unit or Unit) f) = \\P st f ih. st (f ()) (ih ());");
    }

    #[test]
    fn sigma_eta_holds() {
        // Definitional `p ≡ (fst p, snd p)` (conversion-level Sigma-eta,
        // no axiom): transport along it checks by `\\x. x`.
        ok("def peta : (A:*) -> (B:A -> *) -> (p:(x:A) and B x) -> (P:(((x:A) and B x) -> *)) -> P p -> P (fst p, snd p) = \\A B p P x. x;");
        // Eta does not over-identify: distinct neutrals stay unequal.
        fails("def bad : (A:*) -> (p:(x:A) and A) -> (q:(x:A) and A) -> (P:(((x:A) and A) -> *)) -> P p -> P q = \\A p q P x. x;");
    }

    #[test]
    fn unit_rect_type_matches_surface_spelling() {
        // The hand-built `unit_rect_type` must convert with the elaborated
        // surface spelling (catches de Bruijn index slips loudly).
        // Ambiguous `Type` (not `*`): the hand type is level-general, and
        // conversion is equality — a `*`-pinned spelling would (correctly)
        // fail against it.
        let src = "(P:(Unit -> Type)) -> (b:P ()) -> (u:Unit) -> P u";
        let sexpr = crate::parser::parse_expr(src).expect("parse unit_rect type");
        let checker = Checker::new();
        let gmap = std::collections::HashMap::new();
        let failed: Vec<bool> = Vec::new();
        let mut scope = Scope { locals: Vec::new(), globals: &gmap, failed: &failed, wild_counter: 0, holes: Cell::new(0) };
        let core = scope_expr(&mut scope, &sexpr).expect("scope unit_rect type");
        let ctx = Ctx::default();
        checker.infer_sort(&core, &ctx).expect("unit_rect type well-formed");
        let empty: Env = Vec::new();
        let surface_val = eval(&core, &empty, &checker.gvals).expect("eval unit_rect type");
        let prim_val = checker.infer(&Core::UnitRect, &ctx).expect("infer unit_rect");
        let mut fuel = FUEL_LIMIT;
        assert!(
            conv(0, &surface_val, &prim_val, &checker.gvals, &mut fuel, 0, &mut Vec::new())
                .expect("conv unit_rect type"),
            "hand-built unit_rect type differs from surface spelling"
        );
    }

    #[test]
    fn unit_intro_elim() {
        // `Unit : *` with sole value `()`, eliminated by `unit_rect`.
        ok("def u : Unit = ();");
        ok("def t : * = Unit;");
        ok("def r : (P:(Unit -> *)) -> (b:P ()) -> (u:Unit) -> P u = \\P b u. unit_rect P b u;");
        // Closed inhabitants of sums at last: `inl ()`, `inr ()`.
        ok("def t1 : Unit or Unit = inl ();");
        ok("def t2 : Unit or Unit = inr ();");
        ok("def f : (Unit or Unit) -> Unit = \\e. either_rect Unit Unit (\\_. Unit) (\\_. ()) (\\_. ()) e;");
    }

    #[test]
    fn unit_rect_iota_pinned() {
        // With neutral `P`, only iota closes this gap: the goal mentions the
        // reduced `b` while the body infers the stuck chain.
        ok("def t : (P:(Unit -> *)) -> (b:P ()) -> (H:P () -> *) -> H b -> H (unit_rect P b ()) = \\P b H h. h;");
    }

    #[test]
    fn unit_rejects_nonsense() {
        // `()` fits `Unit` only (not `Void`, not sorts-as-terms).
        fails("def bad : Void = ();");
        fails("def bad : Unit = Void;");
        // Motives are `*`-valued.
        fails("def bad : (u:Unit) -> * = \\u. unit_rect (\\_. *) * ();");
        // `Unit` the type is not a term of itself... (`Unit : *`, not `Unit`).
        fails("def bad : Unit = Unit;");
    }

    #[test]
    fn either_rect_type_matches_surface_spelling() {
        // The hand-built `either_rect_type` must convert with the elaborated
        // surface spelling (catches de Bruijn index slips loudly). NOTE the
        // double parens around the motive domain: `(P:(A or B -> *))` would
        // misparse (`or`-operands don't extend over `->`). Ambiguous `Type`
        // (not `*`): the hand type is level-general, and conversion is
        // equality.
        let src = "(A:Type) -> (B:Type) -> (P:((A or B) -> Type)) -> (f:(a:A) -> P (inl a)) -> (g:(b:B) -> P (inr b)) -> (e:A or B) -> P e";
        let sexpr = crate::parser::parse_expr(src).expect("parse either_rect type");
        let checker = Checker::new();
        let gmap = std::collections::HashMap::new();
        let failed: Vec<bool> = Vec::new();
        let mut scope = Scope { locals: Vec::new(), globals: &gmap, failed: &failed, wild_counter: 0, holes: Cell::new(0) };
        let core = scope_expr(&mut scope, &sexpr).expect("scope either_rect type");
        let ctx = Ctx::default();
        checker.infer_sort(&core, &ctx).expect("either_rect type well-formed");
        let empty: Env = Vec::new();
        let surface_val = eval(&core, &empty, &checker.gvals).expect("eval either_rect type");
        let prim_val = checker.infer(&Core::EitherRect, &ctx).expect("infer either_rect");
        let mut fuel = FUEL_LIMIT;
        assert!(
            conv(0, &surface_val, &prim_val, &checker.gvals, &mut fuel, 0, &mut Vec::new())
                .expect("conv either_rect type"),
            "hand-built either_rect type differs from surface spelling"
        );
    }

    #[test]
    fn either_formation_predicative() {
        // Small sides: small sum.
        ok("def s : * = Void or Void;");
        // Any `Type0` side forces `Type0` — an impredicative sum would claim `*`.
        fails("def bad : * = Void or *;");
        ok("def good : Type0 = Void or *;");
        fails("def bad : * = (* -> *) or Void;");
        ok("def good : Type0 = (* -> *) or Void;");
    }

    #[test]
    fn injections_check_against_sums() {
        ok("def t : (v:Void) -> (Void or Void) = \\v. inl (absurd Void v);");
        ok("def t : (v:Void) -> (Void or Void) = \\v. inr (absurd Void v);");
        // Full case analysis.
        ok("def c : (A:*) -> (B:*) -> (P:((A or B) -> *)) -> (f:(a:A) -> P (inl a)) -> (g:(b:B) -> P (inr b)) -> (e:A or B) -> P e = \\A B P f g e. either_rect A B P f g e;");
    }

    #[test]
    fn either_rect_iota_pinned() {
        // With neutral `P`/`f`/`g`, only iota closes this gap: the goal
        // mentions the reduced `f x` while the body infers the stuck chain.
        // Fails without the `elim_redex` branch, passes with it. (`g` stays
        // abstract: no closed body inhabits `P (inr b)` for abstract `P`.)
        ok("def t : (v:Void) -> (P:((Void or Void) -> *)) -> (f:(a:Void) -> P (inl a)) -> (g:(b:Void) -> P (inr b)) -> (H:P (inl (absurd Void v)) -> *) -> H (f (absurd Void v)) -> H (either_rect Void Void P f g (inl (absurd Void v))) = \\v P f g H h. h;");
    }

    #[test]
    fn either_rejects_nonsense() {
        // Scrutinee must be a sum (neutral of non-sum type rejected).
        fails("def bad : (A:*) -> A = \\A. either_rect A A (\\_. A) (\\a. a) (\\b. b) A;");
        // Motives are `*`-valued.
        fails("def bad : (v:Void) -> Void = \\v. either_rect Void Void (\\_. *) (\\a. absurd Void a) (\\b. b) (inl (absurd Void v));");
        // Bare `inl`/`inr` don't infer (which side? annotate).
        fails("def b : (v:Void) -> * = \\v. (let X = inl (absurd Void v) in X);");
    }

    #[test]
    fn match_basic_case() {
        // Non-dependent case analysis with a variable scrutinee.
        ok("def c : (A:*) -> (B:*) -> (C:*) -> (f:A -> C) -> (g:B -> C) -> (e:A or B) -> C = \\A B C f g e. match e return (\\_. C) { inl a => f a | inr b => g b };");
        // Closed scrutinees compute (iota through the checker, not just eval;
        // injections need ascriptions — bare `inl` never infers).
        ok("def t1 : Unit = match (inl () : Unit or Unit) return (\\_. Unit) { inl a => a | inr b => b };");
        ok("def t2 : Unit = match (inr () : Unit or Unit) return (\\_. Unit) { inl a => a | inr b => b };");
        // Non-variable (neutral, non-sum-stuck) scrutinees elaborate plainly.
        ok("def t : (f:Unit -> Unit or Unit) -> Unit = \\f. match (f ()) return (\\_. Unit) { inl a => () | inr b => () };");
        // Pattern binders carry payloads (swap uses both sides).
        ok("def s : (E:*) -> (e:E or E) -> E or E = \\E e. match e return (\\_. E or E) { inl a => inr a | inr b => inl b };");
    }

    #[test]
    fn match_refines_variable_scrutinee() {
        // THE refinement test: `h : B e` is usable where `B (inl a)` and
        // `B (inr b)` are expected — the branch contexts substituted the
        // patterns for `e`. Fails with plain elaboration (`B e` vs
        // `B (inl a)` never converts for abstract `B`), passes with it.
        ok("def t : (E:*) -> (B:((E or E) -> *)) -> (e:E or E) -> (h:B e) -> B e = \\E B e h. match e return (\\x. B x) { inl a => h | inr b => h };");
    }

    #[test]
    fn match_iota_pinned() {
        // With neutral `P`, only iota closes this gap: the goal mentions the
        // reduced `f ()` while the body infers the stuck chain. Fails without
        // the eval-level `Match` iota branch, passes with it. (Also exercises
        // the neutral-motive goal arm: `P` is a variable here.)
        ok("def t : (P:((Unit or Unit) -> *)) -> (f:(a:Unit) -> P (inl a)) -> (g:(b:Unit) -> P (inr b)) -> (H:P (inl ()) -> *) -> H (f ()) -> H (match (inl () : Unit or Unit) return P { inl a => f a | inr b => g b }) = \\P f g H h. h;");
    }

    #[test]
    fn match_neutral_headed_annotation() {
        // A stuck match as an annotation fails cleanly — exactly like a
        // stuck eliminator head (`elim_ann` probe): neutral-headed types
        // must infer to a literal sort, and `infer_match` yields `P e`.
        // (Reaches the `Value::Match` arm of `infer_sort_value`: quoted,
        // inferred, then rejected with the match and its type shown.)
        fails("def bad : (P:((Void or Void) -> *)) -> (e:Void or Void) -> match e return P { inl a => absurd (P (inl a)) a | inr b => absurd (P (inr b)) b } = \\P e. absurd (P e) e;");
    }

    #[test]
    fn match_rejects_nonsense() {
        // Scrutinee must be a sum (sorts are not sums).
        fails("def bad : * = match * return (\\_. *) { inl a => * | inr b => * };");
        // Motive must be a family over the sum (a bare type is not one).
        fails("def bad : (e:Void or Void) -> Void = \\e. match e return Void { inl a => absurd Void a | inr b => b };");
        // Branch bodies must fit the motive at the patterns (`a : Void`
        // is not a `Unit`).
        fails("def bad : (e:Void or Void) -> Unit = \\e. match e return (\\_. Unit) { inl a => a | inr b => () };");
    }

    #[test]
    fn quot_lift_type_matches_surface_spelling() {
        // The hand-built `quot_lift_type` must convert with the elaborated
        // surface spelling (catches de Bruijn index slips loudly).
        let src = "(A:Type) -> (R:(A -> A -> Type)) -> (B:Type) -> (f:(A -> B)) -> (h:(a:A) -> (b:A) -> (R a b) -> (Q2:(B -> *)) -> Q2 (f a) -> Q2 (f b)) -> (q:Quot A R) -> B";
        let sexpr = crate::parser::parse_expr(src).expect("parse quot_lift type");
        let checker = Checker::new();
        let gmap = std::collections::HashMap::new();
        let failed: Vec<bool> = Vec::new();
        let mut scope = Scope { locals: Vec::new(), globals: &gmap, failed: &failed, wild_counter: 0, holes: Cell::new(0) };
        let core = scope_expr(&mut scope, &sexpr).expect("scope quot_lift type");
        let ctx = Ctx::default();
        checker.infer_sort(&core, &ctx).expect("quot_lift type well-formed");
        let empty: Env = Vec::new();
        let surface_val = eval(&core, &empty, &checker.gvals).expect("eval quot_lift type");
        let prim_val = checker.infer(&Core::QuotLift, &ctx).expect("infer quot_lift");
        let mut fuel = FUEL_LIMIT;
        assert!(
            conv(0, &surface_val, &prim_val, &checker.gvals, &mut fuel, 0, &mut Vec::new())
                .expect("conv quot_lift type"),
            "hand-built quot_lift type differs from surface spelling"
        );
    }

    #[test]
    fn quot_sound_type_matches_surface_spelling() {
        // Same cross-check for the soundness axiom (inlined Leibniz shape).
        let src = "(A:Type) -> (R:(A -> A -> Type)) -> (a:A) -> (b:A) -> (R a b) -> (Q2:((Quot A R) -> *)) -> Q2 (quot_mk a) -> Q2 (quot_mk b)";
        let sexpr = crate::parser::parse_expr(src).expect("parse quot_sound type");
        let checker = Checker::new();
        let gmap = std::collections::HashMap::new();
        let failed: Vec<bool> = Vec::new();
        let mut scope = Scope { locals: Vec::new(), globals: &gmap, failed: &failed, wild_counter: 0, holes: Cell::new(0) };
        let core = scope_expr(&mut scope, &sexpr).expect("scope quot_sound type");
        let ctx = Ctx::default();
        checker.infer_sort(&core, &ctx).expect("quot_sound type well-formed");
        let empty: Env = Vec::new();
        let surface_val = eval(&core, &empty, &checker.gvals).expect("eval quot_sound type");
        let prim_val = checker.infer(&Core::QuotSound, &ctx).expect("infer quot_sound");
        let mut fuel = FUEL_LIMIT;
        assert!(
            conv(0, &surface_val, &prim_val, &checker.gvals, &mut fuel, 0, &mut Vec::new())
                .expect("conv quot_sound type"),
            "hand-built quot_sound type differs from surface spelling"
        );
    }

    #[test]
    fn quotient_formation_predicative() {
        // Carrier + relation codomain levels max out (here all small).
        ok("def q : * = Quot (Unit or Unit) (\\_ _. Unit or Unit);");
        // A `Type0` part forces `Type0` (here the relation's codomain).
        ok("def q : Type0 = Quot * (\\_ _. *);");
        fails("def bad : * = Quot * (\\_ _. *);");
        // Non-relations rejected: `R` must be a binary family on `A`.
        fails("def bad : * = Quot Void Void;");
        fails("def bad : * = Quot Void (\\x. x);");
    }

    #[test]
    fn quot_mk_intro() {
        // `quot_mk` checks against a known quotient, infers nothing bare.
        ok("def c : Quot (Unit or Unit) (\\_ _. Unit or Unit) = quot_mk (inl () : Unit or Unit);");
        // Payload must fit the carrier.
        fails("def bad : Quot (Unit or Unit) (\\_ _. Unit or Unit) = quot_mk ();");
        // Bare `quot_mk` doesn't infer (which quotient? annotate).
        fails("def b : (u:Unit) -> * = \\u. (let X = quot_mk u in X);");
    }

    #[test]
    fn quot_lift_iota_pinned() {
        // With neutral `B`/`f`, only iota closes this gap: the goal mentions
        // the reduced `f (inl ())` while the body infers the stuck chain.
        // Fails without the `elim_redex` branch, passes with it.
        ok("def t : (B:*) -> (f:(Unit or Unit) -> B) -> (h:(a:(Unit or Unit)) -> (b:(Unit or Unit)) -> Unit -> (Q2:(B -> *)) -> Q2 (f a) -> Q2 (f b)) -> (H:(B -> *)) -> H (f (inl ())) -> H (quot_lift (Unit or Unit) (\\_ _. Unit) B f h (quot_mk (inl () : Unit or Unit) : Quot (Unit or Unit) (\\_ _. Unit))) = \\B f h H x. x;");
    }

    #[test]
    fn quot_sound_feeds_path() {
        // `quot_sound` proofs check against `path` (delta+beta interop with
        // the inlined Leibniz shape — no `path` primitive needed).
        ok("def path : (T:*) -> (a:T) -> (b:T) -> * = \\T a b. (P:(T -> *)) -> (P a) -> (P b); \
            def rel : (a:(Unit or Unit)) -> (b:(Unit or Unit)) -> Unit -> path (Quot (Unit or Unit) (\\_ _. Unit)) (quot_mk a) (quot_mk b) = \\a b h. quot_sound (Unit or Unit) (\\_ _. Unit) a b h;");
    }

    #[test]
    fn quot_rejects_nonsense() {
        // Relation must be binary on the carrier (a bare type is not one).
        fails("def bad : * = Quot Void Void;");
        // Respectfulness is checked: an `h` proving the wrong statement fails
        // (`h : Unit` is not a Leibniz proof between `f`-values).
        fails("def bad : (e:Quot (Unit or Unit) (\\_ _. Unit)) -> Unit = \\e. quot_lift (Unit or Unit) (\\_ _. Unit) Unit (\\_. ()) (\\a b h. h) e;");
        // `quot_mk` against a non-quotient.
        fails("def bad : Unit = quot_mk ();");
    }

    #[test]
    fn quot_ind_type_matches_surface_spelling() {
        // Same cross-check for dependent elimination (transport-coherence
        // stated with `quot_sound` applied — surface-expressible since the
        // motive is `*`-valued).
        let src = "(A:Type) -> (R:(A -> A -> Type)) -> (P:((Quot A R) -> *)) -> (f:(a:A) -> P (quot_mk a)) -> (coh:(a:A) -> (b:A) -> (h:R a b) -> (Q2:(P (quot_mk b) -> *)) -> Q2 (quot_sound A R a b h P (f a)) -> Q2 (f b)) -> (q:Quot A R) -> P q";
        let sexpr = crate::parser::parse_expr(src).expect("parse quot_ind type");
        let checker = Checker::new();
        let gmap = std::collections::HashMap::new();
        let failed: Vec<bool> = Vec::new();
        let mut scope = Scope { locals: Vec::new(), globals: &gmap, failed: &failed, wild_counter: 0, holes: Cell::new(0) };
        let core = scope_expr(&mut scope, &sexpr).expect("scope quot_ind type");
        let ctx = Ctx::default();
        checker.infer_sort(&core, &ctx).expect("quot_ind type well-formed");
        let empty: Env = Vec::new();
        let surface_val = eval(&core, &empty, &checker.gvals).expect("eval quot_ind type");
        let prim_val = checker.infer(&Core::QuotInd, &ctx).expect("infer quot_ind");
        let mut fuel = FUEL_LIMIT;
        assert!(
            conv(0, &surface_val, &prim_val, &checker.gvals, &mut fuel, 0, &mut Vec::new())
                .expect("conv quot_ind type"),
            "hand-built quot_ind type differs from surface spelling"
        );
    }

    #[test]
    fn quot_ind_iota_pinned() {
        // With neutral `P`/`f`, only iota closes this gap: the goal mentions
        // the reduced `f`-application while the body infers the stuck chain.
        // Fails without the `elim_redex` branch, passes with it.
        ok("def t : (P:((Quot (Unit or Unit) (\\_ _. Unit)) -> *)) -> (f:(a:(Unit or Unit)) -> P (quot_mk a)) -> (coh:(a:(Unit or Unit)) -> (b:(Unit or Unit)) -> (hh:Unit) -> (Q2:(P (quot_mk b) -> *)) -> Q2 (quot_sound (Unit or Unit) (\\_ _. Unit) a b hh P (f a)) -> Q2 (f b)) -> (H:P (quot_mk (inl () : Unit or Unit)) -> *) -> H (f (inl () : Unit or Unit)) -> H (quot_ind (Unit or Unit) (\\_ _. Unit) P f coh (quot_mk (inl () : Unit or Unit) : Quot (Unit or Unit) (\\_ _. Unit))) = \\P f coh H x. x;");
    }

    #[test]
    fn sig_rect_type_matches_surface_spelling() {
        // The hand-built `sig_rect_type` must convert with the elaborated
        // surface spelling (catches de Bruijn index slips loudly).
        // NOTE the triple parens around P's domain: `(P:((x:A) and B x -> *))`
        // would misparse — the named-`and` rule swallows the `->` into the
        // Sigma's codomain. `(((x:A) and B x) -> *)` groups first.
        // Ambiguous `Type` throughout (not `*`): the hand type is
        // level-general, and conversion is equality.
        let src = "(A:Type) -> (B:(A -> Type)) -> (P:(((x:A) and B x) -> Type)) -> (f:(a:A) -> (b:B a) -> P (a, b)) -> (p:(x:A) and B x) -> P p";
        let sexpr = crate::parser::parse_expr(src).expect("parse sig_rect type");
        let checker = Checker::new();
        let gmap = std::collections::HashMap::new();
        let failed: Vec<bool> = Vec::new();
        let mut scope = Scope { locals: Vec::new(), globals: &gmap, failed: &failed, wild_counter: 0, holes: Cell::new(0) };
        let core = scope_expr(&mut scope, &sexpr).expect("scope sig_rect type");
        let ctx = Ctx::default();
        checker.infer_sort(&core, &ctx).expect("sig_rect type well-formed");
        let empty: Env = Vec::new();
        let surface_val = eval(&core, &empty, &checker.gvals).expect("eval sig_rect type");
        let prim_val = checker.infer(&Core::SigRect, &ctx).expect("infer sig_rect");
        let mut fuel = FUEL_LIMIT;
        assert!(
            conv(0, &surface_val, &prim_val, &checker.gvals, &mut fuel, 0, &mut Vec::new())
                .expect("conv sig_rect type"),
            "hand-built sig_rect type differs from surface spelling"
        );
    }

    #[test]
    fn eliminator_subsumes_projections() {
        // `fst`/`snd` are definable from `sig_rect` (the eliminator is the
        // stronger primitive). `snd2`'s motive forces `fst`-iota during
        // checking: its `f`-case goal `B (fst (a, b))` reduces to `B a`.
        ok("def fst2 : (A:*) -> (B:A -> *) -> (p:(x:A) and B x) -> A = \\A B p. sig_rect A B (\\_. A) (\\a b. a) p;");
        ok("def snd2 : (A:*) -> (B:A -> *) -> (p:(x:A) and B x) -> B (fst p) = \\A B p. sig_rect A B (\\p. B (fst p)) (\\a b. b) p;");
    }

    #[test]
    fn sig_rect_iota_pinned() {
        // With neutral `P`/`f`, only iota closes this gap: the goal mentions
        // the reduced `f a b` while the body infers the stuck chain. Fails
        // without the `do_apply` iota branch, passes with it.
        ok("def t : (v:Void) -> (P:((x:Void) and Void) -> *) -> (f:(a:Void) -> (b:Void) -> P (a, b)) -> (H:P ((absurd Void v), (absurd Void v)) -> *) -> H (f (absurd Void v) (absurd Void v)) -> H (sig_rect Void (\\_. Void) P f ((absurd Void v), (absurd Void v))) = \\v P f H h. h;");
    }

    #[test]
    fn sig_rect_rejects_nonsense() {
        // Scrutinee must be a pair (neutral of non-Sigma type rejected).
        fails("def bad : Void = \\v. sig_rect Void (\\_. Void) (\\_. Void) (\\a b. a) v;");
        // Branch must fit the motive at the pattern (`a : Void` is not a
        // type in `*`, though the `Type0`-motive itself is now legal).
        fails("def bad : (v:Void) -> Void = \\v. sig_rect Void (\\_. Void) (\\_. *) (\\a b. a) ((absurd Void v), (absurd Void v));");
    }

    #[test]
    fn sigma_rejects_nonsense() {
        // `fst` of a non-pair (neutral whose type is not Sigma).
        fails("def bad : (A:*) -> A = \\A. fst A;");
        fails("def bad : * = fst *;");
        // Bare `(a, b)` never forms a type (values only — use `and`).
        fails("def bad : * = (Void, Void);");
        // Bare `(a, b)` in inference position is ambiguous (needs Sigma).
        fails("def b : * = (let X = (Void, Void) in X);");
        // Lambdas as components need annotations (bidirectional limit).
        fails("def t : (v:Void) -> Void = \\v. fst ((\\w. w), (absurd Void v)) (absurd Void v);");
        ok("def t : (v:Void) -> Void = \\v. fst (((\\w. w) : Void -> Void), (absurd Void v)) (absurd Void v);");
    }
}

