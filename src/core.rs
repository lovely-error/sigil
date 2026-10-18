//! De Bruijn core terms, runtime values, closures, evaluation and quoting.
//!
//! Indexing conventions (the usual NbE split):
//! - [`Core`] uses de Bruijn *indices* (`Bound(0)` = nearest binder).
//! - [`Value`] uses de Bruijn *levels* (`Var(0)` = outermost).
//! - [`Env`] is a stack of values indexed by level.
//!
//! Globals (`Global(i)`) refer to top-level `def`s by source order. They are
//! neutral until unfolded by `whnf` (only backwards references exist, so
//! unfolding terminates modulo object-level divergence, which is cut off by
//! [`FUEL_LIMIT`]).
//!
//! Sorts: `*` (impredicative bottom) and `Type(l)` levels (`Type(0)` concrete
//! as `Type0`, ambiguous surface `Type` elaborating to a fresh level variable).
//! `* : Type(0)`; `Type(n) : Type(n + 1)`; cumulativity goes up. See
//! `levels.rs` for constraints and `check.rs` for the Pi rule.

use std::collections::HashMap;
use std::fmt;
use crate::levels::{Constraint, Level, Rel};

use crate::lexer::Span;
use crate::subst::contains_meta;

/// Evaluation fuel: bounds beta/delta steps so diverging terms (e.g.
/// `(\x. x x) (\x. x x)`) become errors instead of hangs. Calibrated at
/// 100k (not 20k): conversion walks unfolded proof terms with a shared
/// budget, and `nat_ind`/`funext`-scale chains (nested transports through
/// delta-unfolded globals) legitimately need tens of thousands of steps —
/// verified by `nat_ind_stuck_at_sound`, which exhausts 20k but settles
/// well under 100k. Raised to 400k after `examples/afsnat.sig`: AFS-style
/// subtype certificates (`limSucc`-shaped Σ-pairs unfolding inside
/// Leibniz-path types against abstract variables) peak just under 150k
/// steps for one conversion, and chained derivations multiply that.
/// Diverging terms still error, only slightly later (steps are
/// microseconds; the depth cap, not fuel, guards the stack).
pub const FUEL_LIMIT: u32 = 400_000;
/// Nesting-depth cap for evaluation (threaded functionally: each nested call
/// gets `depth - 1`, so no decrement discipline can leak). Bounds Rust-stack
/// use no matter what the step budget allows: depth and work are capped
/// independently, and deep-but-shallow-nesting computation is unaffected.
/// Calibrated for small host stacks (Windows main thread is ~1MB in debug
/// builds with fat frames): whatever nesting survives a diverging probe
/// cleanly also bounds legitimate code, which nests far shallower.
pub const EVAL_DEPTH_LIMIT: u32 = 256;
/// Structural recursion cap for conversion/quote.
pub const DEPTH_LIMIT: u32 = 200;

// ---------------------------------------------------------------------------
// Sorts
// ---------------------------------------------------------------------------

/// The sorts. `Star` (`*`) is the impredicative bottom; `Type(l)` is level
/// `l` of a predicative-in-the-large hierarchy (`Type0`, `Type1`, ... and
/// inference variables from bare surface `Type`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Sort {
    Star,
    Type(Level),
}

impl fmt::Display for Sort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Sort::Star => write!(f, "*"),
            Sort::Type(Level::Const(0)) => write!(f, "Type0"),
            Sort::Type(Level::Const(n)) => write!(f, "Type{n}"),
            Sort::Type(Level::Var(a)) => write!(f, "Type(?{a})"),
        }
    }
}

// ---------------------------------------------------------------------------
// Core terms (de Bruijn indices)
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Core {
    Bound(usize),
    /// Global use with an explicit universe instance: `inst` assigns the
    /// global's scheme variables (in scheme order — see `check.rs`).
    Global(usize, Vec<Level>),
    Sort(Sort),
    /// Empty type (no constructors). `Void : *`.
    Void,
    /// Vacuous eliminator, `absurd : (A:*) -> Void -> A`. Primitive constant:
    /// underivable by design (no case to split on). Applications stay stuck
    /// (no iota rule needed — no canonical scrutinee can exist).
    Absurd,
    Pi { name: String, dom: Box<Core>, cod: Box<Core> },
    /// Dependent pair type `(x : A) and B` (cod under binder). Non-dependent
    /// `A and B` uses `"_"`. Formation is PREDICATIVE (see `check.rs`).
    Sigma { name: String, dom: Box<Core>, cod: Box<Core> },
    /// Pair value `(a, b)` (checked against Sigma types only; unlike
    /// `and`, it never forms a type — see `check.rs`).
    Pair(Box<Core>, Box<Core>),
    /// Projections (term formers, so their types come from the scrutinee).
    Fst(Box<Core>),
    Snd(Box<Core>),
    /// Dependent eliminator `sig_rect : (A:*) -> (B:A->*) -> (P:SigmaAB->*)
    /// -> ((a:A) -> (b:B a) -> P (a,b)) -> (p:SigmaAB) -> P p` (primitive
    /// constant, like `Absurd`: all args explicit, iota in `do_apply`).
    SigRect,
    /// Non-dependent sum type `A or B` (predicative formation, like Sigma).
    Either(Box<Core>, Box<Core>),
    /// Left / right injection (check-only against a known sum, like pairs).
    Inl(Box<Core>),
    Inr(Box<Core>),
    /// Sum eliminator `either_rect : (A:*) -> (B:*) -> (P:(A or B -> *))
    /// -> ((a:A) -> P (inl a)) -> ((b:B) -> P (inr b)) -> (e:A or B) -> P e`.
    EitherRect,
    /// Quotient type former `Quot A R` (predicative formation, like sums:
    /// lives at the max of its parts' levels).
    Quotient(Box<Core>, Box<Core>),
    /// Quotient introduction `quot_mk a` (check-only against a known
    /// quotient, like injections).
    QuotMk(Box<Core>),
    /// Quotient eliminator (primitive constant; iota in `do_apply`).
    QuotLift,
    /// Dependent quotient eliminator (primitive constant; iota in `do_apply`).
    QuotInd,
    /// Soundness axiom (stuck-neutral primitive constant, like `Absurd`:
    /// `quot_sound A R a b h : path-enc (Quot A R) (mk a) (mk b)` — no iota).
    QuotSound,
    /// Dependent case analysis `match e return P { inl x => b1 | inr y => b2 }`.
    /// Branch bodies are core terms under one pattern binder each (names kept
    /// for pretty-printing; de Bruijn handles scope).
    Match {
        scrut: Box<Core>,
        motive: Box<Core>,
        l_name: String,
        l_body: Box<Core>,
        r_name: String,
        r_body: Box<Core>,
    },
    /// One-element type (`Unit : *`).
    Unit,
    /// Its sole value `()`.
    Pt,
    /// Unit eliminator `unit_rect : (P:(Unit -> *)) -> P () -> (u:Unit) -> P u`.
    UnitRect,
    /// Well-founded trees `W : (A:*) -> (B:(A -> *)) -> *` (primitive).
    W,
    /// Introduction `sup` (all args explicit; iota lives with `w_rect`).
    Sup,
    /// W eliminator (primitive constant; iota needs an environment — see
    /// `w_rect_env_redex` — so it fires in `eval`, not `do_apply`).
    WRect,
    Lam { name: String, body: Box<Core> },
    App(Box<Core>, Box<Core>),
    Let { name: String, ann: Option<Box<Core>>, val: Box<Core>, body: Box<Core> },
    /// `(e : T)`. Preserved for pretty-printing; evaluation ignores the type.
    Ann(Box<Core>, Box<Core>),
    /// A surface `_` hole. Scoped once (the `id` is globally unique, minted
    /// from the checker's hole supply); evaluation snapshots the environment
    /// into a [`Value::Meta`], and elaboration resolves the id to at most one
    /// metavariable per definition (see `check.rs`).
    Hole { id: u32, span: Span },
}

impl Core {
    pub fn app(f: Core, a: Core) -> Self {
        Core::App(Box::new(f), Box::new(a))
    }
}

// ---------------------------------------------------------------------------
// Values (de Bruijn levels) + closures
// ---------------------------------------------------------------------------

/// Environment: value for each level (index == level).
pub type Env = Vec<Value>;

#[derive(Debug, Clone)]
pub struct Closure {
    pub env: Env,
    pub term: Box<Core>,
}

impl Closure {
    pub fn new(env: Env, term: Core) -> Self {
        Self { env, term: Box::new(term) }
    }
    /// Beta-step with fuel: every closure application consumes one unit, so
    /// diverging terms (e.g. `(\x. x x) (\x. x x)`) exhaust fuel instead of
    /// overflowing the host stack. Nested calls share the budget; each
    /// top-level [`eval`]/[`Closure::apply`] call starts a fresh one, so one
    /// diverging subterm cannot starve unrelated checking.
    pub fn apply(&self, arg: Value, globals: &GlobalVals) -> Result<Value, EvalError> {
        let mut fuel = FUEL_LIMIT;
        self.apply_in(arg, globals, &mut fuel, EVAL_DEPTH_LIMIT)
    }
    fn apply_in(&self, arg: Value, globals: &GlobalVals, fuel: &mut u32, depth: u32) -> Result<Value, EvalError> {
        if *fuel == 0 {
            return Err(EvalError { msg: "evaluation fuel exhausted (possibly diverging term)".to_string() });
        }
        if depth == 0 {
            return Err(EvalError { msg: "maximum evaluation depth exceeded (diverging term or excessively deep nesting)".to_string() });
        }
        *fuel -= 1;
        let mut env = self.env.clone();
        env.push(arg);
        eval_in(&self.term, &env, globals, fuel, depth - 1)
    }
}

#[derive(Debug, Clone)]
pub enum Value {
    Var(usize),
    /// Stuck global use (unfolds in `whnf` by instantiating the stored
    /// scheme value with `inst`).
    Global(usize, Vec<Level>),
    Sort(Sort),
    Void,
    /// Stuck eliminator constant (never unfolds; applications of it are
    /// neutral — there is no canonical `Void` value to reduce against).
    Absurd,
    Pi { name: String, dom: Box<Value>, cod: Closure },
    Sigma { name: String, dom: Box<Value>, cod: Closure },
    Pair(Box<Value>, Box<Value>),
    /// Stuck projections (iota fires in `eval`/`whnf` when the scrutinee is
    /// a `Pair`; otherwise neutral).
    Fst(Box<Value>),
    Snd(Box<Value>),
    /// Stuck eliminator constant (iota fires in `do_apply` on a complete
    /// `sig_rect A B P f (a, b)` redex; otherwise neutral, like `Absurd`).
    SigRect,
    /// Sum type (predicative; both sides ordinary values).
    Either(Box<Value>, Box<Value>),
    /// Canonical injections (no reduction: introduction forms).
    Inl(Box<Value>),
    Inr(Box<Value>),
    /// Stuck sum-eliminator constant (iota on complete
    /// `either_rect A B P f g (inl a | inr b)` redexes; else neutral).
    EitherRect,
    /// Quotient type (predicative; parts ordinary values).
    Quotient(Box<Value>, Box<Value>),
    /// Canonical quotient introduction (no reduction: introduction form).
    QuotMk(Box<Value>),
    /// Stuck quotient-eliminator constant (iota on complete
    /// `quot_lift A R B f h (quot_mk a)` redexes; else neutral).
    QuotLift,
    /// Stuck dependent quotient-eliminator constant (iota on complete
    /// `quot_ind A R P f coh (quot_mk a)` redexes; else neutral).
    QuotInd,
    /// Stuck soundness-axiom constant (never unfolds; applications neutral —
    /// there is no canonical `R`-proof shape to reduce against, like `Absurd`).
    QuotSound,
    /// Stuck dependent match (iota fires in `eval`/`whnf` when the scrutinee
    /// is canonical; branch bodies stay closures so no environment is ever
    /// missing — unlike W's quoted IH).
    Match {
        scrut: Box<Value>,
        mot: Box<Value>,
        l_name: String,
        l_body: Closure,
        r_name: String,
        r_body: Closure,
    },
    /// One-element type value.
    Unit,
    /// Its sole value (canonical; no reduction).
    Pt,
    /// Stuck unit-eliminator constant (iota on `unit_rect P b ()`; else neutral).
    UnitRect,
    /// Stuck W-type former (applied `W A B` is a type; see `check.rs`).
    W,
    /// Stuck W introduction (canonical tree once fully applied).
    Sup,
    /// Stuck W eliminator (iota needs an environment — see
    /// `w_rect_env_redex` — so unlike the other eliminators it never fires
    /// in `do_apply`/`whnf`, only in `eval`).
    WRect,
    Lam { name: String, body: Closure },
    App(Box<Value>, Box<Value>),
    /// An unsolved elaboration hole: `id` matches the [`Core::Hole`] it was
    /// elaborated from, `span` locates the surface `_` for error messages,
    /// and `spine` snapshots the environment at elaboration (levels are
    /// absolute, so the snapshot stays meaningful wherever checking goes —
    /// same convention as [`Closure`]). Stuck everywhere (no iota, no delta):
    /// solving happens in the checker's unification, never here.
    Meta { id: u32, span: Span, spine: Vec<Value> },
}

#[derive(Debug, Clone)]
pub struct EvalError {
    pub msg: String,
}

impl fmt::Display for EvalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "evaluation error: {}", self.msg)
    }
}

impl std::error::Error for EvalError {}

/// Values of already-checked globals, by def index. `None` = failed/unknown
/// (never unfolded; referencing one is a scope/check error raised earlier).
#[derive(Debug, Clone, Default)]
pub struct GlobalVals {
    vals: Vec<Option<GlobalDef>>,
}

/// One global definition: its value plus its scheme level-variables in
/// instance order, so `Global(g, inst)` unfolds by substituting `inst`.
#[derive(Debug, Clone)]
pub struct GlobalDef {
    pub value: Value,
    pub levels: Vec<u32>,
}

impl GlobalVals {
    pub fn new() -> Self {
        Self { vals: Vec::new() }
    }
    pub fn push(&mut self, v: Option<GlobalDef>) {
        self.vals.push(v);
    }
    pub fn get(&self, ix: usize) -> Option<&Option<GlobalDef>> {
        self.vals.get(ix)
    }
    #[allow(dead_code)]
    pub fn len(&self) -> usize {
        self.vals.len()
    }
}

/// Unfold `Global(g, inst)`: substitute the instance for the scheme variables
/// in the stored value. `None` = unknown/failed global or arity mismatch —
/// evaluation stays stuck (never fails on stuck terms); the checker rejects
/// mismatches with a clean error when inferring the same node.
fn unfold_global(g: usize, inst: &[Level], globals: &GlobalVals) -> Option<Value> {
    let def = globals.get(g)?.as_ref()?;
    if def.levels.len() != inst.len() {
        return None;
    }
    let m: HashMap<u32, Level> =
        def.levels.iter().copied().zip(inst.iter().copied()).collect();
    Some(subst_level_value(&def.value, &m))
}

// ---------------------------------------------------------------------------
// Evaluation (weak-head, closure-based)
// ---------------------------------------------------------------------------

fn lookup(env: &Env, ix: usize) -> Result<Value, EvalError> {
    if ix >= env.len() {
        return Err(EvalError { msg: format!("stuck de Bruijn index {ix} (env size {})", env.len()) });
    }
    Ok(env[env.len() - 1 - ix].clone())
}

pub fn eval(term: &Core, env: &Env, globals: &GlobalVals) -> Result<Value, EvalError> {
    let mut fuel = FUEL_LIMIT;
    eval_in(term, env, globals, &mut fuel, EVAL_DEPTH_LIMIT)
}

fn eval_in(term: &Core, env: &Env, globals: &GlobalVals, fuel: &mut u32, depth: u32) -> Result<Value, EvalError> {
    // Depth is threaded functionally (each nested call gets `depth - 1`),
    // so the cap cannot leak: exceeding it is always a clean error.
    if depth == 0 {
        return Err(EvalError { msg: "maximum evaluation depth exceeded (diverging term or excessively deep nesting)".to_string() });
    }
    // Structural recursion over the finite term; every potentially looping
    // step (beta via `apply`, iota below, delta via `whnf`) spends fuel, so
    // `eval` always terminates — with `EvalError`, never host-stack overflow.
    match term {
        Core::Bound(ix) => lookup(env, *ix),
        Core::Global(g, inst) => Ok(Value::Global(*g, inst.clone())),
        Core::Sort(s) => Ok(Value::Sort(*s)),
        Core::Void => Ok(Value::Void),
        Core::Absurd => Ok(Value::Absurd),
        Core::SigRect => Ok(Value::SigRect),
        Core::Unit => Ok(Value::Unit),
        Core::Pt => Ok(Value::Pt),
        Core::UnitRect => Ok(Value::UnitRect),
        Core::W => Ok(Value::W),
        Core::Sup => Ok(Value::Sup),
        Core::WRect => Ok(Value::WRect),
        Core::Match { scrut, motive, l_name, l_body, r_name, r_body } => {
            let sv = eval_in(scrut, env, globals, fuel, depth - 1)?;
            let mv = eval_in(motive, env, globals, fuel, depth - 1)?;
            // Iota eagerly when canonical; otherwise capture branch closures
            // (their bodies stay lazy, so no environment is ever missing).
            match sv {
                Value::Inl(a) => {
                    let mut env2 = env.clone();
                    env2.push(*a);
                    eval_in(l_body, &env2, globals, fuel, depth - 1)
                }
                Value::Inr(b) => {
                    let mut env2 = env.clone();
                    env2.push(*b);
                    eval_in(r_body, &env2, globals, fuel, depth - 1)
                }
                _ => Ok(Value::Match {
                    scrut: Box::new(sv),
                    mot: Box::new(mv),
                    l_name: l_name.clone(),
                    l_body: Closure::new(env.clone(), (**l_body).clone()),
                    r_name: r_name.clone(),
                    r_body: Closure::new(env.clone(), (**r_body).clone()),
                }),
            }
        }
        Core::Either(a, b) => {
            Ok(Value::Either(
                Box::new(eval_in(a, env, globals, fuel, depth - 1)?),
                Box::new(eval_in(b, env, globals, fuel, depth - 1)?),
            ))
        }
        Core::Inl(a) => Ok(Value::Inl(Box::new(eval_in(a, env, globals, fuel, depth - 1)?))),
        Core::Inr(b) => Ok(Value::Inr(Box::new(eval_in(b, env, globals, fuel, depth - 1)?))),
        Core::EitherRect => Ok(Value::EitherRect),
        Core::Quotient(a, r) => {
            Ok(Value::Quotient(
                Box::new(eval_in(a, env, globals, fuel, depth - 1)?),
                Box::new(eval_in(r, env, globals, fuel, depth - 1)?),
            ))
        }
        Core::QuotMk(a) => Ok(Value::QuotMk(Box::new(eval_in(a, env, globals, fuel, depth - 1)?))),
        Core::QuotLift => Ok(Value::QuotLift),
        Core::QuotInd => Ok(Value::QuotInd),
        Core::QuotSound => Ok(Value::QuotSound),
        Core::Pi { name, dom, cod } => {
            let dom_v = eval_in(dom, env, globals, fuel, depth - 1)?;
            Ok(Value::Pi {
                name: name.clone(),
                dom: Box::new(dom_v),
                cod: Closure::new(env.clone(), (**cod).clone()),
            })
        }
        Core::Sigma { name, dom, cod } => {
            let dom_v = eval_in(dom, env, globals, fuel, depth - 1)?;
            Ok(Value::Sigma {
                name: name.clone(),
                dom: Box::new(dom_v),
                cod: Closure::new(env.clone(), (**cod).clone()),
            })
        }
        Core::Pair(a, b) => {
            Ok(Value::Pair(
                Box::new(eval_in(a, env, globals, fuel, depth - 1)?),
                Box::new(eval_in(b, env, globals, fuel, depth - 1)?),
            ))
        }
        Core::Fst(p) => {
            // Iota eagerly: project now when canonical, else stuck-neutral.
            match eval_in(p, env, globals, fuel, depth - 1)? {
                Value::Pair(a, _) => Ok(*a),
                v => Ok(Value::Fst(Box::new(v))),
            }
        }
        Core::Snd(p) => {
            match eval_in(p, env, globals, fuel, depth - 1)? {
                Value::Pair(_, b) => Ok(*b),
                v => Ok(Value::Snd(Box::new(v))),
            }
        }
        Core::Lam { name, body } => Ok(Value::Lam {
            name: name.clone(),
            body: Closure::new(env.clone(), (**body).clone()),
        }),
        Core::App(f, a) => {
            let fv = eval_in(f, env, globals, fuel, depth - 1)?;
            let av = eval_in(a, env, globals, fuel, depth - 1)?;
            // W-iota needs the environment (to build the IH closure), so it
            // fires here — where `env` exists — and never in `do_apply` /
            // `whnf`, which lack one (see `w_rect_env_redex`).
            if let Some(v) = w_rect_env_redex(&fv, &av, env, globals, fuel, depth)? {
                return Ok(v);
            }
            do_apply(fv, av, globals, fuel, depth - 1)
        }
        Core::Let { val, body, .. } => {
            let vv = eval_in(val, env, globals, fuel, depth - 1)?;
            let mut env2 = env.clone();
            env2.push(vv);
            eval_in(body, &env2, globals, fuel, depth - 1)
        }
        Core::Ann(e, _) => eval_in(e, env, globals, fuel, depth - 1),
        // Holes evaluate to metas snapshotting the environment (never solved
        // here — see `check.rs`; the snapshot makes Miller-pattern solving
        // and the occurs check scope-correct).
        Core::Hole { id, span } => Ok(Value::Meta { id: *id, span: *span, spine: env.clone() }),
    }
}

fn do_apply(fun: Value, arg: Value, globals: &GlobalVals, fuel: &mut u32, depth: u32) -> Result<Value, EvalError> {
    if depth == 0 {
        return Err(EvalError { msg: "maximum evaluation depth exceeded (diverging term or excessively deep nesting)".to_string() });
    }
    match fun {
        Value::Lam { body, .. } => body.apply_in(arg, globals, fuel, depth - 1),
        // Delta: a global unfolding to a lambda applies too (instantiated).
        Value::Global(g, inst) => {
            // Only unfold one step here; `whnf` loops as needed. To avoid
            // infinite regress on (impossible) cyclic globals, unfold at
            // most once per `do_apply` and leave the rest to `whnf`.
            match unfold_global(g, &inst, globals) {
                Some(Value::Lam { body, .. }) => body.apply_in(arg, globals, fuel, depth - 1),
                _ => Ok(Value::App(
                    Box::new(Value::Global(g, inst.clone())),
                    Box::new(arg),
                )),
            }
        }
        _ => {
            // Eliminator iota (see `elim_redex`): complete redexes reduce
            // (`sig_rect` / `either_rect` / `unit_rect`); otherwise
            // stuck-neutral, exactly as before.
            if let Some(v) = elim_redex(&fun, &arg, globals, fuel, depth)? {
                return Ok(v);
            }
            Ok(Value::App(Box::new(fun), Box::new(arg)))
        }
    }
}

/// Detect an eliminator iota redex: `fun` must unfold (fuel-bounded, so a
/// global-aliased eliminator applied later still counts) to an eliminator-
/// rooted spine with all-but-one arguments collected, and `arg` must unfold
/// to a canonical introduction form. Returns the reduct, else `None` (stuck
/// terms — partial applications, neutrals — are never errors here).
/// Shapes: `sig_rect A B P f (a, b) ≡ f a b`;
/// `either_rect A B P f g (inl a) ≡ f a`,
/// `either_rect A B P f g (inr b) ≡ g b`;
/// `unit_rect P b () ≡ b`;
/// `quot_lift A R B f h (quot_mk a) ≡ f a`;
/// `quot_ind A R P f coh (quot_mk a) ≡ f a`.
fn elim_redex(
    fun: &Value,
    arg: &Value,
    globals: &GlobalVals,
    fuel: &mut u32,
    depth: u32,
) -> Result<Option<Value>, EvalError> {
    if depth == 0 {
        return Err(EvalError { msg: "maximum evaluation depth exceeded (diverging term or excessively deep nesting)".to_string() });
    }
    let mut head = whnf(fun, globals, fuel)?;
    let mut args: Vec<Value> = Vec::new();
    loop {
        match head {
            Value::App(f, a) => {
                args.push(*a);
                head = *f;
            }
            _ => break,
        }
    }
    // Collected innermost-first; reverse to outside-in argument order.
    args.reverse();
    // The iota step itself spends fuel like a beta-step; reconstruction
    // nests with `depth - 1`.
    let spend = |fuel: &mut u32| -> Result<(), EvalError> {
        if *fuel == 0 {
            return Err(EvalError { msg: "evaluation fuel exhausted (possibly diverging term)".to_string() });
        }
        *fuel -= 1;
        Ok(())
    };
    match head {
        Value::SigRect => {
            if args.len() != 4 {
                return Ok(None);
            }
            let f = args.pop().expect("sig_rect spine has four args");
            match whnf(arg, globals, fuel)? {
                Value::Pair(a, b) => {
                    spend(fuel)?;
                    let fa = do_apply(f, *a, globals, fuel, depth - 1)?;
                    Ok(Some(do_apply(fa, *b, globals, fuel, depth - 1)?))
                }
                _ => Ok(None),
            }
        }
        Value::EitherRect => {
            if args.len() != 5 {
                return Ok(None);
            }
            let g = args.pop().expect("either_rect spine has five args");
            let f = args.pop().expect("either_rect spine has five args");
            match whnf(arg, globals, fuel)? {
                Value::Inl(a) => {
                    spend(fuel)?;
                    Ok(Some(do_apply(f, *a, globals, fuel, depth - 1)?))
                }
                Value::Inr(b) => {
                    spend(fuel)?;
                    Ok(Some(do_apply(g, *b, globals, fuel, depth - 1)?))
                }
                _ => Ok(None),
            }
        }
        Value::UnitRect => {
            if args.len() != 2 {
                return Ok(None);
            }
            let b = args.pop().expect("unit_rect spine has two args");
            match whnf(arg, globals, fuel)? {
                Value::Pt => {
                    spend(fuel)?;
                    Ok(Some(b))
                }
                _ => Ok(None),
            }
        }
        Value::QuotLift => {
            if args.len() != 5 {
                return Ok(None);
            }
            let _h = args.pop().expect("quot_lift spine has five args");
            let f = args.pop().expect("quot_lift spine has five args");
            match whnf(arg, globals, fuel)? {
                Value::QuotMk(a) => {
                    spend(fuel)?;
                    Ok(Some(do_apply(f, *a, globals, fuel, depth - 1)?))
                }
                _ => Ok(None),
            }
        }
        Value::QuotInd => {
            if args.len() != 5 {
                return Ok(None);
            }
            let _coh = args.pop().expect("quot_ind spine has five args");
            let f = args.pop().expect("quot_ind spine has five args");
            match whnf(arg, globals, fuel)? {
                Value::QuotMk(a) => {
                    spend(fuel)?;
                    Ok(Some(do_apply(f, *a, globals, fuel, depth - 1)?))
                }
                _ => Ok(None),
            }
        }
        _ => Ok(None),
    }
}

/// Detect the `w_rect` iota redex — `w_rect A B P s w` with `w` canonical —
/// and reduce it to `s a f ih`, where `ih` is the induction-hypothesis
/// function `λb. w_rect A B P s (f b)`.
///
/// WHY HERE (IN `eval`, WITH AN ENVIRONMENT) AND NOT IN `do_apply`: building
/// `ih` needs a closure, closures pair a core term with an environment (to
/// resolve the quoted components' indices), and only `eval` has one.
/// `do_apply`/`whnf` work on bare values, whose levels carry no environment
/// mapping, so W-iota can never fire there.
///
/// This asymmetry is sound and complete *given fixed globals*: `eval`
/// normalizes every canonically-headed redex it evaluates (unfolding the
/// scrutinee first, so global-aliased trees count), while any redex `eval`
/// leaves stuck has a truly neutral scrutinee (variables, unknown globals,
/// stuck applications) — which later `whnf` calls over the same globals also
/// leave stuck. Deterministic either way; fuel exhaustion is fail-closed,
/// never a wrong answer. (The other eliminators need no environment — their
/// reducts rearrange existing values — so theirs lives in `do_apply`.)
///
/// Concretely: peel the eliminator spine (cheap filter first — most heads
/// are not eliminators, so no fuel is spent on ordinary applications);
/// require `WRect` (possibly global-aliased, unfolded fuel-bounded) with
/// exactly four collected args `[A, B, P, s]` plus a scrutinee unfolding to
/// a canonical `sup` application `[A', B', a, f]` (`A'`/`B'` were validated
/// at check time); quote the five IH components one level above the current
/// environment (quoting at `level + 1` lifts past the new `b` binder for
/// free — no explicit lift pass needed); evaluate the IH lambda in the
/// extended environment; rebuild `s a f ih` by nested application.
/// Shape: `w_rect A B P s (sup A B a f) ≡ s a f (λb. w_rect A B P s (f b))`.
fn w_rect_env_redex(
    fun: &Value,
    arg: &Value,
    env: &Env,
    globals: &GlobalVals,
    fuel: &mut u32,
    depth: u32,
) -> Result<Option<Value>, EvalError> {
    if depth == 0 {
        return Err(EvalError { msg: "maximum evaluation depth exceeded (diverging term or excessively deep nesting)".to_string() });
    }
    // Cheap syntactic filter: peel the App spine with no unfolding or fuel.
    // Only `WRect`- or possibly-aliased `Global`-rooted spines proceed.
    let mut head: &Value = fun;
    loop {
        match head {
            Value::App(f, _) => {
                head = f;
            }
            _ => break,
        }
    }
    match head {
        Value::WRect | Value::Global(_, _) => {}
        _ => return Ok(None),
    }
    // Full check with unfolding (fuel-bounded): re-peel the unfolded head.
    let mut head_w = whnf(fun, globals, fuel)?;
    let mut args: Vec<Value> = Vec::new();
    loop {
        match head_w {
            Value::App(f, a) => {
                args.push(*a);
                head_w = *f;
            }
            _ => break,
        }
    }
    args.reverse();
    // Need exactly `[A, B, P, s]` (the 5th argument is `arg` itself).
    if !matches!(head_w, Value::WRect) || args.len() != 4 {
        return Ok(None);
    }
    // Scrutinee canonical (unfolding for globals)?
    let mut shead = whnf(arg, globals, fuel)?;
    let mut sargs: Vec<Value> = Vec::new();
    loop {
        match shead {
            Value::App(f, a) => {
                sargs.push(*a);
                shead = *f;
            }
            _ => break,
        }
    }
    sargs.reverse();
    if !matches!(shead, Value::Sup) || sargs.len() != 4 {
        return Ok(None);
    }
    let a = sargs[2].clone();
    let f = sargs[3].clone();
    let (w_a, w_b, w_p, w_s) =
        (args[0].clone(), args[1].clone(), args[2].clone(), args[3].clone());
    // Metas in the components stay stuck: quoting drops `Meta` spines (they
    // quote to bare holes), so re-evaluating through the mirror would change
    // their meaning. Bailing (no iota) is fail-safe — the neutral redex is
    // revisited after the holes solve, if they ever do.
    if contains_meta(&w_a) || contains_meta(&w_b) || contains_meta(&w_p) || contains_meta(&w_s) || contains_meta(&f) {
        return Ok(None);
    }
    // Quote components one level above the current environment: the IH core
    // below binds `b`, and quoting at `level + 1` makes each `Var(l)` a
    // `Bound` denoting level `l` past the new binder — with no explicit
    // lift pass and no placeholder entry.
    //
    // The rebuilt closure is then evaluated in a *mirror* environment
    // (`Var(i)` at position `i`), NOT in `env`: quoted indices denote
    // absolute levels, so they resolve correctly only where entry `i`
    // denotes level `i`. The live `env` is an evaluation chain (often
    // holding closed entries at positions whose levels live elsewhere —
    // e.g. `[WNat, wzero, wsucc, ...]`), so resolving quoted free variables
    // against it silently rebinds them (a type lands in a term slot and
    // re-inference fails downstream). Closed subvalues quote to
    // self-contained cores and free variables quote to levels, so the
    // mirror environment loses nothing: every quoted index resolves to the
    // variable it names. (When `env` already mirrors levels, the mirror is
    // identical to it, so closed-term behavior is unchanged.)
    let level = env.len();
    let mut qc = |v: &Value| quote(level + 1, v, globals, fuel, 0);
    let ih_core = Core::Lam {
        name: "b".to_string(),
        body: Box::new(Core::app(
            Core::app(
                Core::app(Core::app(Core::app(Core::WRect, qc(&w_a)?), qc(&w_b)?), qc(&w_p)?),
                qc(&w_s)?,
            ),
            Core::app(qc(&f)?, Core::Bound(0)),
        )),
    };
    // Evaluate the IH lambda in the mirror environment (no placeholder
    // entry: the binder's value arrives with the application, and the
    // quoted parts already account for exactly that one push).
    let mirror: Env = (0..level).map(Value::Var).collect();
    let ih = eval_in(&ih_core, &mirror, globals, fuel, depth - 1)?;
    // Reconstruct `s a f ih` by nested application.
    if *fuel == 0 {
        return Err(EvalError { msg: "evaluation fuel exhausted (possibly diverging term)".to_string() });
    }
    *fuel -= 1;
    let sa = do_apply(w_s, a, globals, fuel, depth - 1)?;
    let saf = do_apply(sa, f, globals, fuel, depth - 1)?;
    Ok(Some(do_apply(saf, ih, globals, fuel, depth - 1)?))
}

/// Weak-head normal form with fuel. Unfolds `Global`s whose values are known
/// and beta-reduces head redexes. Never fails on stuck terms; returns
/// `EvalError` only when fuel runs out.
pub fn whnf(value: &Value, globals: &GlobalVals, fuel: &mut u32) -> Result<Value, EvalError> {
    let mut cur = value.clone();
    loop {
        if *fuel == 0 {
            return Err(EvalError { msg: "evaluation fuel exhausted (possibly diverging term)".to_string() });
        }
        *fuel -= 1;
        match cur {
            Value::App(f, a) => {
                let head = whnf(&f, globals, fuel)?;
                match head {
                    Value::Lam { body, .. } => {
                        cur = body.apply_in((*a).clone(), globals, fuel, EVAL_DEPTH_LIMIT)?;
                    }
                    Value::Global(g, inst) => {
                        match unfold_global(g, &inst, globals) {
                            Some(Value::Lam { body, .. }) => {
                                cur = body.apply_in((*a).clone(), globals, fuel, EVAL_DEPTH_LIMIT)?;
                            }
                            // Unfold non-lambda globals one step so that e.g.
                            // `id T` where `id` is a defined function still
                            // progresses if its value is an application chain.
                            // If it stays stuck, rebuild the application.
                            Some(gv) => {
                                // If unfolding made no progress (still the
                                // same global+instance), stop.
                                if matches!(&gv, Value::Global(g2, inst2) if *g2 == g && *inst2 == inst)
                                {
                                    return Ok(Value::App(
                                        Box::new(Value::Global(g, inst.clone())),
                                        a,
                                    ));
                                }
                                // Re-apply the unfolded head to the argument. (An
                                // earlier revision compared the recombined
                                // spine against the original application to
                                // stop here, but that shape check is
                                // unreachable: the head is already unfolded
                                // (never the original global), and falling
                                // through is correct regardless — each unfold
                                // moves to an earlier definition (scope
                                // forbids forward/self references), so this
                                // loop cannot cycle; fuel bounds it anyway.)
                                let recombined = do_apply(gv, (*a).clone(), globals, fuel, EVAL_DEPTH_LIMIT)
                                    .map_err(|e| e)?;
                                cur = recombined;
                            }
                            None => {
                                return Ok(Value::App(
                                    Box::new(Value::Global(g, inst.clone())),
                                    a,
                                ))
                            }
                        }
                    }
                    // Nothing else applies: try eliminator iota (currently
                    // only `sig_rect`; stuck otherwise). Routing through
                    // `do_apply` is behavior-preserving for non-redexes (its
                    // default arm rebuilds the application identically) and
                    // lets redexes completed by unfolding still reduce.
                    other => return do_apply(other, (*a).clone(), globals, fuel, EVAL_DEPTH_LIMIT),
                }
            }
            Value::Global(g, inst) => {
                match unfold_global(g, &inst, globals) {
                    Some(gv) => {
                        // Self-loop guard (should be unreachable: scope check
                        // forbids self/forward references, but be total).
                        if matches!(&gv, Value::Global(g2, inst2) if *g2 == g && *inst2 == inst)
                        {
                            return Ok(Value::Global(g, inst));
                        }
                        cur = gv;
                    }
                    _ => return Ok(Value::Global(g, inst)),
                }
            }
            // Iota for projections (completeness: scrutinees that only become
            // canonical after unfolding).
            Value::Fst(p) => {
                match whnf(&p, globals, fuel)? {
                    Value::Pair(a, _) => cur = *a,
                    _ => return Ok(Value::Fst(p)),
                }
            }
            Value::Snd(p) => {
                match whnf(&p, globals, fuel)? {
                    Value::Pair(_, b) => cur = *b,
                    _ => return Ok(Value::Snd(p)),
                }
            }
            // Iota for dependent match (completeness: a scrutinee that only
            // becomes canonical after unfolding — e.g. a global alias — still
            // reduces, using the stored branch closures, so no environment
            // is ever missing).
            Value::Match { scrut, mot, l_name, l_body, r_name, r_body } => {
                match whnf(&scrut, globals, fuel)? {
                    Value::Inl(a) => {
                        let mut env2 = l_body.env.clone();
                        env2.push(*a);
                        cur = eval_in(&l_body.term, &env2, globals, fuel, EVAL_DEPTH_LIMIT)?;
                    }
                    Value::Inr(b) => {
                        let mut env2 = r_body.env.clone();
                        env2.push(*b);
                        cur = eval_in(&r_body.term, &env2, globals, fuel, EVAL_DEPTH_LIMIT)?;
                    }
                    sw => {
                        return Ok(Value::Match {
                            scrut: Box::new(sw),
                            mot,
                            l_name,
                            l_body,
                            r_name,
                            r_body,
                        });
                    }
                }
            }
            _ => return Ok(cur),
        }
    }
}

// ---------------------------------------------------------------------------
// Quoting (value -> core, for error messages) and conversion
// ---------------------------------------------------------------------------

pub fn quote(level: usize, value: &Value, globals: &GlobalVals, fuel: &mut u32, depth: u32) -> Result<Core, EvalError> {
    if depth > DEPTH_LIMIT {
        return Err(EvalError { msg: "quote depth limit exceeded".to_string() });
    }
    if *fuel == 0 {
        return Err(EvalError { msg: "evaluation fuel exhausted while quoting".to_string() });
    }
    *fuel -= 1;
    let w = whnf(value, globals, fuel)?;
    match w {
        Value::Var(l) => {
            if l >= level {
                return Err(EvalError { msg: format!("stuck level {l} beyond context {level}") });
            }
            Ok(Core::Bound(level - 1 - l))
        }
        Value::Global(g, inst) => Ok(Core::Global(g, inst.clone())),
        Value::Sort(s) => Ok(Core::Sort(s)),
        Value::Void => Ok(Core::Void),
        Value::Absurd => Ok(Core::Absurd),
        Value::SigRect => Ok(Core::SigRect),
        Value::EitherRect => Ok(Core::EitherRect),
        Value::Unit => Ok(Core::Unit),
        Value::Pt => Ok(Core::Pt),
        Value::UnitRect => Ok(Core::UnitRect),
        Value::W => Ok(Core::W),
        Value::Sup => Ok(Core::Sup),
        Value::WRect => Ok(Core::WRect),
        Value::Pi { name, dom, cod } => {
            let dom_c = quote(level, &dom, globals, fuel, depth + 1)?;
            let fresh = Value::Var(level);
            let cod_v = cod.apply_in(fresh, globals, fuel, EVAL_DEPTH_LIMIT)?;
            let cod_c = quote(level + 1, &cod_v, globals, fuel, depth + 1)?;
            Ok(Core::Pi { name, dom: Box::new(dom_c), cod: Box::new(cod_c) })
        }
        Value::Sigma { name, dom, cod } => {
            let dom_c = quote(level, &dom, globals, fuel, depth + 1)?;
            let fresh = Value::Var(level);
            let cod_v = cod.apply_in(fresh, globals, fuel, EVAL_DEPTH_LIMIT)?;
            let cod_c = quote(level + 1, &cod_v, globals, fuel, depth + 1)?;
            Ok(Core::Sigma { name, dom: Box::new(dom_c), cod: Box::new(cod_c) })
        }
        Value::Pair(a, b) => {
            let ac = quote(level, &a, globals, fuel, depth + 1)?;
            let bc = quote(level, &b, globals, fuel, depth + 1)?;
            Ok(Core::Pair(Box::new(ac), Box::new(bc)))
        }
        Value::Either(a, b) => {
            let ac = quote(level, &a, globals, fuel, depth + 1)?;
            let bc = quote(level, &b, globals, fuel, depth + 1)?;
            Ok(Core::Either(Box::new(ac), Box::new(bc)))
        }
        Value::Inl(a) => {
            let ac = quote(level, &a, globals, fuel, depth + 1)?;
            Ok(Core::Inl(Box::new(ac)))
        }
        Value::Inr(b) => {
            let bc = quote(level, &b, globals, fuel, depth + 1)?;
            Ok(Core::Inr(Box::new(bc)))
        }
        Value::Quotient(a, r) => {
            let ac = quote(level, &a, globals, fuel, depth + 1)?;
            let rc = quote(level, &r, globals, fuel, depth + 1)?;
            Ok(Core::Quotient(Box::new(ac), Box::new(rc)))
        }
        Value::QuotMk(a) => {
            let ac = quote(level, &a, globals, fuel, depth + 1)?;
            Ok(Core::QuotMk(Box::new(ac)))
        }
        Value::QuotLift => Ok(Core::QuotLift),
        Value::QuotInd => Ok(Core::QuotInd),
        Value::QuotSound => Ok(Core::QuotSound),
        Value::Fst(p) => {
            let pc = quote(level, &p, globals, fuel, depth + 1)?;
            Ok(Core::Fst(Box::new(pc)))
        }
        Value::Snd(p) => {
            let pc = quote(level, &p, globals, fuel, depth + 1)?;
            Ok(Core::Snd(Box::new(pc)))
        }
        Value::Match { scrut, mot, l_name, l_body, r_name, r_body } => {
            let sc = quote(level, &scrut, globals, fuel, depth + 1)?;
            let mc = quote(level, &mot, globals, fuel, depth + 1)?;
            // Branch closures quote like lambda bodies (fresh var, extend).
            let fresh = Value::Var(level);
            let lv = l_body.apply_in(fresh.clone(), globals, fuel, EVAL_DEPTH_LIMIT)?;
            let lc = quote(level + 1, &lv, globals, fuel, depth + 1)?;
            let rv = r_body.apply_in(fresh, globals, fuel, EVAL_DEPTH_LIMIT)?;
            let rc = quote(level + 1, &rv, globals, fuel, depth + 1)?;
            Ok(Core::Match {
                scrut: Box::new(sc),
                motive: Box::new(mc),
                l_name: l_name.clone(),
                l_body: Box::new(lc),
                r_name: r_name.clone(),
                r_body: Box::new(rc),
            })
        }
        Value::Lam { name, body } => {
            let fresh = Value::Var(level);
            let b = body.apply_in(fresh, globals, fuel, EVAL_DEPTH_LIMIT)?;
            let bc = quote(level + 1, &b, globals, fuel, depth + 1)?;
            Ok(Core::Lam { name, body: Box::new(bc) })
        }
        Value::App(f, a) => {
            let fc = quote(level, &f, globals, fuel, depth + 1)?;
            let ac = quote(level, &a, globals, fuel, depth + 1)?;
            Ok(Core::app(fc, ac))
        }
        // Metas quote back to their hole (re-elaboration resolves the same
        // id — the spine is elaboration state, not syntax). The span survives
        // so requoted holes still report locations.
        Value::Meta { id, span, .. } => Ok(Core::Hole { id, span }),
    }
}

/// Sort equality inside conversion. Identical sorts hold. Distinct concrete
/// levels fail (no constraint can equate them). `*` does NOT lift into
/// `Type` here: conversion is equality (anything involving a level variable
/// records both-direction `<=` — wherever conversion runs, the two sides
/// must denote the same universe — and holds). One-directional cumulativity
/// (`*` fits in any `Type`, levels go up) lives in the checker's subsumption
/// (`require_sort_le` / `expect_conv`'s both-sorts fast path), not here:
/// lifting inside conversion equates small and large motive families, which
/// smuggles large elimination through small proofs (`liftPath`-shaped
/// ascriptions). `*`-motives against level-general primitives still check —
/// those go through subsumption, never this arm.
fn conv_sort_eq(x: Sort, y: Sort, ucs: &mut Vec<Constraint>) -> bool {
    match (x, y) {
        (Sort::Star, Sort::Star) => true,
        (Sort::Star, Sort::Type(_)) => false,
        (Sort::Type(a), Sort::Type(b)) if a == b => true,
        (Sort::Type(Level::Const(m)), Sort::Type(Level::Const(n))) => m == n,
        (Sort::Type(a), Sort::Type(b)) => {
            ucs.push(Constraint::new(a, Rel::Le, b));
            ucs.push(Constraint::new(b, Rel::Le, a));
            true
        }
        _ => false,
    }
}
/// Definitional equality with beta/delta and eta for functions, pairs, and
/// Unit. Sorts compare
/// by *universe equality*: identical sorts hold; distinct concrete levels
/// fail; anything involving a level variable records both-direction `<=`
/// constraints (equality — sound wherever conversion runs) and holds.
/// (`* <= Type(_)` cumulativity proper is the checker's subsumption, not
/// `conv`.) `ucs` collects the recorded constraints; callers must roll them
/// back if conversion ultimately fails (see `check.rs` checkpointing), since
/// a failed comparison must leave no trace.
pub fn conv(
    level: usize,
    a: &Value,
    b: &Value,
    globals: &GlobalVals,
    fuel: &mut u32,
    depth: u32,
    ucs: &mut Vec<Constraint>,
) -> Result<bool, EvalError> {
    if depth > DEPTH_LIMIT {
        return Ok(false);
    }
    if *fuel == 0 {
        return Err(EvalError { msg: "evaluation fuel exhausted during conversion".to_string() });
    }
    // NB: share fuel across both whnfs (no clones of the budget).
    let wa = whnf(a, globals, fuel)?;
    let wb = whnf(b, globals, fuel)?;
    match (wa, wb) {
        (Value::Sort(x), Value::Sort(y)) => Ok(conv_sort_eq(x, y, ucs)),
        (Value::Void, Value::Void) => Ok(true),
        (Value::Absurd, Value::Absurd) => Ok(true),
        (Value::SigRect, Value::SigRect) => Ok(true),
        (Value::EitherRect, Value::EitherRect) => Ok(true),
        (Value::Unit, Value::Unit) => Ok(true),
        (Value::Pt, Value::Pt) => Ok(true),
        (Value::UnitRect, Value::UnitRect) => Ok(true),
        (Value::W, Value::W) => Ok(true),
        (Value::Sup, Value::Sup) => Ok(true),
        (Value::WRect, Value::WRect) => Ok(true),
        (Value::Var(x), Value::Var(y)) => Ok(x == y),
        (Value::Global(x, xi), Value::Global(y, yi)) => {
            // Same definition with universe-equal instances (pairwise
            // equality, recording both-direction constraints on variables —
            // same contract as sorts above).
            if x != y || xi.len() != yi.len() {
                return Ok(false);
            }
            for (a, b) in xi.iter().zip(yi.iter()) {
                match (a, b) {
                    (Level::Const(m), Level::Const(n)) => {
                        if m != n {
                            return Ok(false);
                        }
                    }
                    _ if a == b => {}
                    _ => {
                        ucs.push(Constraint::new(*a, Rel::Le, *b));
                        ucs.push(Constraint::new(*b, Rel::Le, *a));
                    }
                }
            }
            Ok(true)
        }
        (Value::Pi { dom: d1, cod: c1, .. }, Value::Pi { dom: d2, cod: c2, .. }) => {
            if !conv(level, &d1, &d2, globals, fuel, depth + 1, ucs)? {
                return Ok(false);
            }
            let fresh = Value::Var(level);
            let v1 = c1.apply_in(fresh.clone(), globals, fuel, EVAL_DEPTH_LIMIT)?;
            let v2 = c2.apply_in(fresh, globals, fuel, EVAL_DEPTH_LIMIT)?;
            conv(level + 1, &v1, &v2, globals, fuel, depth + 1, ucs)
        }
        (Value::Sigma { dom: d1, cod: c1, .. }, Value::Sigma { dom: d2, cod: c2, .. }) => {
            if !conv(level, &d1, &d2, globals, fuel, depth + 1, ucs)? {
                return Ok(false);
            }
            let fresh = Value::Var(level);
            let v1 = c1.apply_in(fresh.clone(), globals, fuel, EVAL_DEPTH_LIMIT)?;
            let v2 = c2.apply_in(fresh, globals, fuel, EVAL_DEPTH_LIMIT)?;
            conv(level + 1, &v1, &v2, globals, fuel, depth + 1, ucs)
        }
        (Value::Pair(a1, b1), Value::Pair(a2, b2)) => {
            if !conv(level, &a1, &a2, globals, fuel, depth + 1, ucs)? {
                return Ok(false);
            }
            conv(level, &b1, &b2, globals, fuel, depth + 1, ucs)
        }
        // Sigma eta (definitional `p ≡ (fst p, snd p)`, like function eta and
        // Unit eta): a pair converts with a neutral iff the components convert
        // with the projections (iota fires on the pair side through `whnf`).
        // Only neutrals expand — canonicals of other types stay unequal.
        // Like the etas above, this is sound for well-typed inputs (`conv`
        // never learns types, so ill-typed comparisons can over-identify;
        // the checker only converts elaborated, well-typed terms).
        (Value::Pair(a, b), other)
            if matches!(
                other,
                Value::Var(_)
                    | Value::Global(_, _)
                    | Value::App(_, _)
                    | Value::Match { .. }
                    | Value::Fst(_)
                    | Value::Snd(_)
                    | Value::Meta { .. }
            ) =>
        {
            let fa = Value::Fst(Box::new(other.clone()));
            if !conv(level, &a, &fa, globals, fuel, depth + 1, ucs)? {
                return Ok(false);
            }
            let fb = Value::Snd(Box::new(other));
            conv(level, &b, &fb, globals, fuel, depth + 1, ucs)
        }
        (other, Value::Pair(a, b))
            if matches!(
                other,
                Value::Var(_)
                    | Value::Global(_, _)
                    | Value::App(_, _)
                    | Value::Match { .. }
                    | Value::Fst(_)
                    | Value::Snd(_)
                    | Value::Meta { .. }
            ) =>
        {
            let fa = Value::Fst(Box::new(other.clone()));
            if !conv(level, &fa, &a, globals, fuel, depth + 1, ucs)? {
                return Ok(false);
            }
            let fb = Value::Snd(Box::new(other));
            conv(level, &fb, &b, globals, fuel, depth + 1, ucs)
        }
        (Value::Either(a1, b1), Value::Either(a2, b2)) => {
            if !conv(level, &a1, &a2, globals, fuel, depth + 1, ucs)? {
                return Ok(false);
            }
            conv(level, &b1, &b2, globals, fuel, depth + 1, ucs)
        }
        (Value::Inl(a1), Value::Inl(a2)) => {
            conv(level, &a1, &a2, globals, fuel, depth + 1, ucs)
        }
        (Value::Inr(b1), Value::Inr(b2)) => {
            conv(level, &b1, &b2, globals, fuel, depth + 1, ucs)
        }
        (Value::Quotient(a1, r1), Value::Quotient(a2, r2)) => {
            if !conv(level, &a1, &a2, globals, fuel, depth + 1, ucs)? {
                return Ok(false);
            }
            conv(level, &r1, &r2, globals, fuel, depth + 1, ucs)
        }
        (Value::QuotMk(a1), Value::QuotMk(a2)) => {
            conv(level, &a1, &a2, globals, fuel, depth + 1, ucs)
        }
        (Value::QuotLift, Value::QuotLift) => Ok(true),
        (Value::QuotInd, Value::QuotInd) => Ok(true),
        (Value::QuotSound, Value::QuotSound) => Ok(true),
        (Value::Fst(p1), Value::Fst(p2)) => {
            conv(level, &p1, &p2, globals, fuel, depth + 1, ucs)
        }
        (Value::Snd(p1), Value::Snd(p2)) => {
            conv(level, &p1, &p2, globals, fuel, depth + 1, ucs)
        }
        (Value::Match { scrut: s1, mot: m1, l_body: l1, r_body: r1, .. },
         Value::Match { scrut: s2, mot: m2, l_body: l2, r_body: r2, .. }) => {
            if !conv(level, &s1, &s2, globals, fuel, depth + 1, ucs)? {
                return Ok(false);
            }
            if !conv(level, &m1, &m2, globals, fuel, depth + 1, ucs)? {
                return Ok(false);
            }
            // Branch bodies compare like lambda bodies (shared fresh var).
            let fresh = Value::Var(level);
            let lv1 = l1.apply_in(fresh.clone(), globals, fuel, EVAL_DEPTH_LIMIT)?;
            let lv2 = l2.apply_in(fresh.clone(), globals, fuel, EVAL_DEPTH_LIMIT)?;
            if !conv(level + 1, &lv1, &lv2, globals, fuel, depth + 1, ucs)? {
                return Ok(false);
            }
            let rv1 = r1.apply_in(fresh.clone(), globals, fuel, EVAL_DEPTH_LIMIT)?;
            let rv2 = r2.apply_in(fresh, globals, fuel, EVAL_DEPTH_LIMIT)?;
            conv(level + 1, &rv1, &rv2, globals, fuel, depth + 1, ucs)
        }
        (Value::Lam { body: b1, .. }, Value::Lam { body: b2, .. }) => {
            let fresh = Value::Var(level);
            let v1 = b1.apply_in(fresh.clone(), globals, fuel, EVAL_DEPTH_LIMIT)?;
            let v2 = b2.apply_in(fresh, globals, fuel, EVAL_DEPTH_LIMIT)?;
            conv(level + 1, &v1, &v2, globals, fuel, depth + 1, ucs)
        }
        // Eta: lambda vs anything.
        (Value::Lam { body, .. }, other) | (other, Value::Lam { body, .. }) => {
            let fresh = Value::Var(level);
            let v1 = body.apply_in(fresh.clone(), globals, fuel, EVAL_DEPTH_LIMIT)?;
            let v2 = do_apply(other, fresh, globals, fuel, EVAL_DEPTH_LIMIT)?;
            conv(level + 1, &v1, &v2, globals, fuel, depth + 1, ucs)
        }
        // Unit eta (definitional uniqueness of `()`): `Pt` converts with any
        // non-canonical term (neutrals — which may be Unit-typed). Canonical
        // introductions of other types, sorts, and type formers stay unequal
        // (identical pairs matched above; everything else falls below).
        // Like function eta, this is sound for well-typed inputs — `conv`
        // never learns types, so comparing ill-typed terms can over-identify
        // (same approximation class as cumulativity-in-conversion); the
        // checker only ever converts elaborated, well-typed terms.
        (Value::Pt, other) | (other, Value::Pt) => {
            match other {
                Value::Var(_)
                | Value::Global(_, _)
                | Value::App(_, _)
                | Value::Match { .. }
                | Value::Fst(_)
                | Value::Snd(_)
                | Value::Meta { .. } => Ok(true),
                _ => Ok(false),
            }
        }
        (Value::App(f1, a1), Value::App(f2, a2)) => {
            if !conv(level, &f1, &f2, globals, fuel, depth + 1, ucs)? {
                return Ok(false);
            }
            conv(level, &a1, &a2, globals, fuel, depth + 1, ucs)
        }
        // Metas (defensive: the checker's unification pre-scans for metas and
        // solves or postpones before calling `conv`, so these arms fire only
        // for same-unknown congruence, which holds structurally). Same unknown
        // with pairwise-convertible spines is equal (congruence); anything
        // else stays unequal here (unification decides solvability).
        (Value::Meta { id: i1, spine: s1, .. }, Value::Meta { id: i2, spine: s2, .. }) => {
            if i1 != i2 || s1.len() != s2.len() {
                return Ok(false);
            }
            for (a, b) in s1.iter().zip(s2.iter()) {
                if !conv(level, a, b, globals, fuel, depth + 1, ucs)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        _ => Ok(false),
    }
}

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        // Structural equality is only used in tests, never for typing
        // (typing uses `conv` modulo unfolding/eta). Keep it simple.
        match (self, other) {
            (Value::Var(a), Value::Var(b)) => a == b,
            (Value::Global(a, ai), Value::Global(b, bi)) => a == b && ai == bi,
            (Value::Sort(a), Value::Sort(b)) => a == b,
            (Value::Void, Value::Void) => true,
            (Value::Absurd, Value::Absurd) => true,
            (Value::SigRect, Value::SigRect) => true,
            (Value::EitherRect, Value::EitherRect) => true,
            (Value::QuotLift, Value::QuotLift) => true,
            (Value::QuotInd, Value::QuotInd) => true,
            (Value::QuotSound, Value::QuotSound) => true,
            (Value::Unit, Value::Unit) => true,
            (Value::Pt, Value::Pt) => true,
            (Value::UnitRect, Value::UnitRect) => true,
            (Value::W, Value::W) => true,
            (Value::Sup, Value::Sup) => true,
            (Value::WRect, Value::WRect) => true,
            (Value::Meta { id: a, .. }, Value::Meta { id: b, .. }) => a == b,
            _ => false,
        }
    }
}

// ---------------------------------------------------------------------------
// Level substitution + collection (universe polymorphism instantiation)
// ---------------------------------------------------------------------------

/// Substitute universe levels through a sort (`Var` nodes only).
pub fn subst_level_sort(s: &Sort, m: &HashMap<u32, Level>) -> Sort {
    match s {
        Sort::Star => Sort::Star,
        Sort::Type(Level::Const(n)) => Sort::Type(Level::Const(*n)),
        Sort::Type(Level::Var(a)) => match m.get(a) {
            Some(l) => Sort::Type(*l),
            None => Sort::Type(Level::Var(*a)),
        },
    }
}

fn subst_level_inst(inst: &[Level], m: &HashMap<u32, Level>) -> Vec<Level> {
    inst.iter()
        .map(|l| match l {
            Level::Const(n) => Level::Const(*n),
            Level::Var(a) => m.get(a).copied().unwrap_or(Level::Var(*a)),
        })
        .collect()
}

fn subst_level_closure(c: &Closure, m: &HashMap<u32, Level>) -> Closure {
    Closure {
        env: c.env.iter().map(|v| subst_level_value(v, m)).collect(),
        term: Box::new(subst_level_core(&c.term, m)),
    }
}

/// Substitute universe levels through a core term (including `Global`
/// instances — nested uses freshen consistently with the outer term).
pub fn subst_level_core(c: &Core, m: &HashMap<u32, Level>) -> Core {
    match c {
        Core::Bound(ix) => Core::Bound(*ix),
        Core::Global(ix, inst) => Core::Global(*ix, subst_level_inst(inst, m)),
        Core::Sort(s) => Core::Sort(subst_level_sort(s, m)),
        Core::Void => Core::Void,
        Core::Absurd => Core::Absurd,
        Core::SigRect => Core::SigRect,
        Core::EitherRect => Core::EitherRect,
        Core::Unit => Core::Unit,
        Core::Pt => Core::Pt,
        Core::UnitRect => Core::UnitRect,
        Core::W => Core::W,
        Core::Sup => Core::Sup,
        Core::WRect => Core::WRect,
        Core::Pi { name, dom, cod } => Core::Pi {
            name: name.clone(),
            dom: Box::new(subst_level_core(dom, m)),
            cod: Box::new(subst_level_core(cod, m)),
        },
        Core::Sigma { name, dom, cod } => Core::Sigma {
            name: name.clone(),
            dom: Box::new(subst_level_core(dom, m)),
            cod: Box::new(subst_level_core(cod, m)),
        },
        Core::Pair(a, b) => Core::Pair(
            Box::new(subst_level_core(a, m)),
            Box::new(subst_level_core(b, m)),
        ),
        Core::Fst(p) => Core::Fst(Box::new(subst_level_core(p, m))),
        Core::Snd(p) => Core::Snd(Box::new(subst_level_core(p, m))),
        Core::Either(a, b) => Core::Either(
            Box::new(subst_level_core(a, m)),
            Box::new(subst_level_core(b, m)),
        ),
        Core::Inl(a) => Core::Inl(Box::new(subst_level_core(a, m))),
        Core::Inr(b) => Core::Inr(Box::new(subst_level_core(b, m))),
        Core::Quotient(a, r) => Core::Quotient(
            Box::new(subst_level_core(a, m)),
            Box::new(subst_level_core(r, m)),
        ),
        Core::QuotMk(a) => Core::QuotMk(Box::new(subst_level_core(a, m))),
        Core::Match { scrut, motive, l_name, l_body, r_name, r_body } => Core::Match {
            scrut: Box::new(subst_level_core(scrut, m)),
            motive: Box::new(subst_level_core(motive, m)),
            l_name: l_name.clone(),
            l_body: Box::new(subst_level_core(l_body, m)),
            r_name: r_name.clone(),
            r_body: Box::new(subst_level_core(r_body, m)),
        },
        Core::Lam { name, body } => Core::Lam {
            name: name.clone(),
            body: Box::new(subst_level_core(body, m)),
        },
        Core::QuotLift => Core::QuotLift,
        Core::QuotInd => Core::QuotInd,
        Core::QuotSound => Core::QuotSound,
        Core::App(f, a) => Core::App(
            Box::new(subst_level_core(f, m)),
            Box::new(subst_level_core(a, m)),
        ),
        Core::Let { name, ann, val, body } => Core::Let {
            name: name.clone(),
            ann: ann.as_ref().map(|a| Box::new(subst_level_core(a, m))),
            val: Box::new(subst_level_core(val, m)),
            body: Box::new(subst_level_core(body, m)),
        },
        Core::Ann(e, t) => Core::Ann(
            Box::new(subst_level_core(e, m)),
            Box::new(subst_level_core(t, m)),
        ),
        // Holes carry no universe levels (separate namespace).
        Core::Hole { id, span } => Core::Hole { id: *id, span: *span },
    }
}

/// Substitute universe levels through a value (closures' environments and
/// terms; `Global` instances).
pub fn subst_level_value(v: &Value, m: &HashMap<u32, Level>) -> Value {
    match v {
        Value::Var(l) => Value::Var(*l),
        Value::Global(ix, inst) => Value::Global(*ix, subst_level_inst(inst, m)),
        Value::Sort(s) => Value::Sort(subst_level_sort(s, m)),
        Value::Void => Value::Void,
        Value::Absurd => Value::Absurd,
        Value::SigRect => Value::SigRect,
        Value::EitherRect => Value::EitherRect,
        Value::Unit => Value::Unit,
        Value::Pt => Value::Pt,
        Value::UnitRect => Value::UnitRect,
        Value::W => Value::W,
        Value::Sup => Value::Sup,
        Value::WRect => Value::WRect,
        Value::Pi { name, dom, cod } => Value::Pi {
            name: name.clone(),
            dom: Box::new(subst_level_value(dom, m)),
            cod: subst_level_closure(cod, m),
        },
        Value::Sigma { name, dom, cod } => Value::Sigma {
            name: name.clone(),
            dom: Box::new(subst_level_value(dom, m)),
            cod: subst_level_closure(cod, m),
        },
        Value::Pair(a, b) => Value::Pair(
            Box::new(subst_level_value(a, m)),
            Box::new(subst_level_value(b, m)),
        ),
        Value::Fst(p) => Value::Fst(Box::new(subst_level_value(p, m))),
        Value::Snd(p) => Value::Snd(Box::new(subst_level_value(p, m))),
        Value::Either(a, b) => Value::Either(
            Box::new(subst_level_value(a, m)),
            Box::new(subst_level_value(b, m)),
        ),
        Value::Inl(a) => Value::Inl(Box::new(subst_level_value(a, m))),
        Value::Inr(b) => Value::Inr(Box::new(subst_level_value(b, m))),
        Value::Quotient(a, r) => Value::Quotient(
            Box::new(subst_level_value(a, m)),
            Box::new(subst_level_value(r, m)),
        ),
        Value::QuotMk(a) => Value::QuotMk(Box::new(subst_level_value(a, m))),
        Value::Match { scrut, mot, l_name, l_body, r_name, r_body } => Value::Match {
            scrut: Box::new(subst_level_value(scrut, m)),
            mot: Box::new(subst_level_value(mot, m)),
            l_name: l_name.clone(),
            l_body: subst_level_closure(l_body, m),
            r_name: r_name.clone(),
            r_body: subst_level_closure(r_body, m),
        },
        Value::Lam { name, body } => Value::Lam {
            name: name.clone(),
            body: subst_level_closure(body, m),
        },
        Value::QuotLift => Value::QuotLift,
        Value::QuotInd => Value::QuotInd,
        Value::QuotSound => Value::QuotSound,
        Value::App(f, a) => Value::App(
            Box::new(subst_level_value(f, m)),
            Box::new(subst_level_value(a, m)),
        ),
        // The node is level-free; spine entries may mention level variables.
        Value::Meta { id, span, spine } => Value::Meta {
            id: *id,
            span: *span,
            spine: spine.iter().map(|e| subst_level_value(e, m)).collect(),
        },
    }
}

fn collect_sorted(out: &mut Vec<u32>, a: u32) {
    if !out.contains(&a) {
        out.push(a);
    }
}

/// Collect level-variable ids in a universe constraint (for scheme
/// generalization: every variable a retained constraint mentions must be
/// quantified, or instantiation would re-record the raw id and leak one
/// use's bounds into the next).
pub fn level_vars_constraint(c: &Constraint, out: &mut Vec<u32>) {
    for l in [&c.lhs, &c.rhs] {
        if let Level::Var(a) = l {
            collect_sorted(out, *a);
        }
    }
}

/// Collect level-variable ids in a value (for scheme generalization).
pub fn level_vars_value(v: &Value, out: &mut Vec<u32>) {
    match v {
        Value::Sort(Sort::Type(Level::Var(a))) => collect_sorted(out, *a),
        Value::Global(_, inst) => {
            for l in inst {
                if let Level::Var(a) = l {
                    collect_sorted(out, *a);
                }
            }
        }
        Value::Pi { dom, cod, .. } | Value::Sigma { dom, cod, .. } => {
            level_vars_value(dom, out);
            for e in &cod.env {
                level_vars_value(e, out);
            }
            level_vars_core(&cod.term, out);
        }
        Value::Pair(a, b) | Value::Either(a, b) | Value::App(a, b) => {
            level_vars_value(a, out);
            level_vars_value(b, out);
        }
        Value::Inl(a) | Value::Inr(a) | Value::Fst(a) | Value::Snd(a) => {
            level_vars_value(a, out);
        }
        Value::Quotient(a, r) => {
            level_vars_value(a, out);
            level_vars_value(r, out);
        }
        Value::QuotMk(a) => level_vars_value(a, out),
        Value::Match { scrut, mot, l_body, r_body, .. } => {
            level_vars_value(scrut, out);
            level_vars_value(mot, out);
            for e in l_body.env.iter().chain(r_body.env.iter()) {
                level_vars_value(e, out);
            }
            level_vars_core(&l_body.term, out);
            level_vars_core(&r_body.term, out);
        }
        Value::Lam { body, .. } => {
            for e in &body.env {
                level_vars_value(e, out);
            }
            level_vars_core(&body.term, out);
        }
        // Spine entries can mention sorts with level variables (e.g. a
        // universe-polymorphic value captured in a hole's context).
        Value::Meta { spine, .. } => {
            for e in spine {
                level_vars_value(e, out);
            }
        }
        _ => {}
    }
}

/// Collect level-variable ids in a core term.
pub fn level_vars_core(c: &Core, out: &mut Vec<u32>) {
    match c {
        Core::Sort(Sort::Type(Level::Var(a))) => collect_sorted(out, *a),
        Core::Global(_, inst) => {
            for l in inst {
                if let Level::Var(a) = l {
                    collect_sorted(out, *a);
                }
            }
        }
        Core::Pi { dom, cod, .. } | Core::Sigma { dom, cod, .. } => {
            level_vars_core(dom, out);
            level_vars_core(cod, out);
        }
        Core::Pair(a, b)
        | Core::Either(a, b)
        | Core::App(a, b)
        | Core::Ann(a, b) => {
            level_vars_core(a, out);
            level_vars_core(b, out);
        }
        Core::Inl(a)
        | Core::Inr(a)
        | Core::Fst(a)
        | Core::Snd(a)
        | Core::QuotMk(a)
        | Core::Lam { body: a, .. } => level_vars_core(a, out),
        Core::Quotient(a, r) => {
            level_vars_core(a, out);
            level_vars_core(r, out);
        }
        Core::Match { scrut, motive, l_body, r_body, .. } => {
            level_vars_core(scrut, out);
            level_vars_core(motive, out);
            level_vars_core(l_body, out);
            level_vars_core(r_body, out);
        }
        Core::Let { ann, val, body, .. } => {
            if let Some(a) = ann {
                level_vars_core(a, out);
            }
            level_vars_core(val, out);
            level_vars_core(body, out);
        }
        _ => {}
    }
}

// ---------------------------------------------------------------------------
// Pretty-printing (de Bruijn core with a name stack)
// ---------------------------------------------------------------------------

/// Render a core term with shadowing-avoiding names. `names` maps levels to
/// display names (outermost first); globals render as `g<ix>` unless global
/// names are supplied.
pub fn pretty_core(term: &Core, globals_names: &[String]) -> String {
    let mut names: Vec<String> = Vec::new();
    pretty_core_with(term, &mut names, globals_names)
}

fn freshen(base: &str, taken: &[String]) -> String {
    if !taken.iter().any(|n| n == base) {
        return base.to_string();
    }
    let mut i = 1u32;
    loop {
        let cand = format!("{base}{i}");
        if !taken.iter().any(|n| n == &cand) {
            return cand;
        }
        i += 1;
    }
}

fn pretty_core_with(term: &Core, names: &mut Vec<String>, gnames: &[String]) -> String {
    match term {
        Core::Bound(ix) => {
            if *ix < names.len() {
                names[names.len() - 1 - ix].clone()
            } else {
                format!("?b{ix}")
            }
        }
        Core::Global(g, _) => gnames.get(*g).cloned().unwrap_or_else(|| format!("g{g}")),
        Core::Sort(s) => s.to_string(),
        Core::Void => "Void".to_string(),
        Core::Absurd => "absurd".to_string(),
        Core::SigRect => "sig_rect".to_string(),
        Core::EitherRect => "either_rect".to_string(),
        Core::Unit => "Unit".to_string(),
        Core::Pt => "()".to_string(),
        Core::UnitRect => "unit_rect".to_string(),
        Core::W => "W".to_string(),
        Core::Sup => "sup".to_string(),
        Core::WRect => "w_rect".to_string(),
        Core::Pi { name, dom, cod } => {
            let disp = if name == "_" || name.is_empty() {
                "_".to_string()
            } else {
                freshen(name, names)
            };
            let dom_s = pretty_core_with(dom, names, gnames);
            names.push(disp.clone());
            let cod_s = pretty_core_with(cod, names, gnames);
            names.pop();
            if disp == "_" {
                format!("({dom_s} -> {cod_s})")
            } else {
                format!("(({disp} : {dom_s}) -> {cod_s})")
            }
        }
        Core::Lam { name, body } => {
            // Collect nested lambdas: `\x y. b`.
            let mut params = vec![name.clone()];
            let mut cur = &**body;
            while let Core::Lam { name: n, body: b } = cur {
                params.push(n.clone());
                cur = b;
            }
            // Freshen all params against the context.
            let mut disp_params = Vec::new();
            for p in &params {
                let d = if p == "_" || p.is_empty() {
                    "_".to_string()
                } else {
                    freshen(p, names)
                };
                names.push(d.clone());
                disp_params.push(d);
            }
            let body_s = pretty_core_with(cur, names, gnames);
            for _ in &params {
                names.pop();
            }
            format!("\\{} . {body_s}", disp_params.join(" "))
        }
        Core::Sigma { name, dom, cod } => {
            let disp = if name == "_" || name.is_empty() {
                "_".to_string()
            } else {
                freshen(name, names)
            };
            let dom_s = pretty_core_with(dom, names, gnames);
            names.push(disp.clone());
            let cod_s = pretty_core_with(cod, names, gnames);
            names.pop();
            if disp == "_" {
                format!("({dom_s} and {cod_s})")
            } else {
                format!("(({disp} : {dom_s}) and {cod_s})")
            }
        }
        Core::Pair(a, b) => {
            format!(
                "({}, {})",
                pretty_core_with(a, names, gnames),
                pretty_core_with(b, names, gnames)
            )
        }
        Core::Either(a, b) => {
            format!(
                "({} or {})",
                pretty_core_with(a, names, gnames),
                pretty_core_with(b, names, gnames)
            )
        }
        Core::Inl(a) => {
            format!("(inl {})", pretty_core_with(a, names, gnames))
        }
        Core::Inr(b) => {
            format!("(inr {})", pretty_core_with(b, names, gnames))
        }
        Core::Quotient(a, r) => {
            format!(
                "(Quot {} {})",
                pretty_core_with(a, names, gnames),
                pretty_core_with(r, names, gnames)
            )
        }
        Core::QuotMk(a) => {
            format!("(quot_mk {})", pretty_core_with(a, names, gnames))
        }
        Core::QuotLift => "quot_lift".to_string(),
        Core::QuotInd => "quot_ind".to_string(),
        Core::QuotSound => "quot_sound".to_string(),
        Core::Fst(p) => {
            format!("(fst {})", pretty_core_with(p, names, gnames))
        }
        Core::Snd(p) => {
            format!("(snd {})", pretty_core_with(p, names, gnames))
        }
        Core::Match { scrut, motive, l_name, l_body, r_name, r_body } => {
            let sc_s = pretty_core_with(scrut, names, gnames);
            let mo_s = pretty_core_with(motive, names, gnames);
            let dl = if l_name == "_" || l_name.is_empty() {
                "_".to_string()
            } else {
                freshen(l_name, names)
            };
            names.push(dl.clone());
            let bl = pretty_core_with(l_body, names, gnames);
            names.pop();
            let dr = if r_name == "_" || r_name.is_empty() {
                "_".to_string()
            } else {
                freshen(r_name, names)
            };
            names.push(dr.clone());
            let br = pretty_core_with(r_body, names, gnames);
            names.pop();
            format!("(match {sc_s} return {mo_s} {{ inl {dl} => {bl} | inr {dr} => {br} }})")
        }
        Core::App(f, a) => {
            format!("({} {})", pretty_core_with(f, names, gnames), pretty_core_with(a, names, gnames))
        }
        Core::Let { name, ann, val, body } => {
            let ann_s = match ann {
                Some(a) => pretty_core_with(a, names, gnames),
                None => "_".to_string(),
            };
            let val_s = pretty_core_with(val, names, gnames);
            let disp = if name == "_" { "_".to_string() } else { freshen(name, names) };
            names.push(disp.clone());
            let body_s = pretty_core_with(body, names, gnames);
            names.pop();
            format!("(let {disp} : {ann_s} = {val_s} in {body_s})")
        }
        Core::Ann(e, t) => {
            format!(
                "({} : {})",
                pretty_core_with(e, names, gnames),
                pretty_core_with(t, names, gnames)
            )
        }
        // Holes display as written (`_`); positions come from spans in hole
        // error messages, so distinct holes need no numbering here.
        Core::Hole { .. } => "_".to_string(),
    }
}

/// Render a value by quoting it first (for error messages).
pub fn pretty_value(v: &Value, level: usize, globals: &GlobalVals, gnames: &[String]) -> String {
    let mut fuel = FUEL_LIMIT;
    match quote(level, v, globals, &mut fuel, 0) {
        Ok(c) => pretty_core(&c, gnames),
        Err(_) => "<stuck>".to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn beta_reduces() {
        // (\x. x) * == *
        let globals = GlobalVals::new();
        let lam = Core::Lam { name: "x".into(), body: Box::new(Core::Bound(0)) };
        let app = Core::app(lam, Core::Sort(Sort::Star));
        let empty: Env = Vec::new();
        let v = eval(&app, &empty, &globals).unwrap();
        let mut fuel = FUEL_LIMIT;
        let w = whnf(&v, &globals, &mut fuel).unwrap();
        assert!(matches!(w, Value::Sort(Sort::Star)));
    }

    #[test]
    fn beta() {
        beta_reduces();
    }

    #[test]
    fn eta_conv_holds() {
        // \x. f x === f  (eta)
        let globals = GlobalVals::new();
        let f: Env = vec![Value::Var(0)];
        let lam_core = Core::Lam {
            name: "x".into(),
            body: Box::new(Core::App(
                Box::new(Core::Bound(1)),
                Box::new(Core::Bound(0)),
            )),
        };
        let lam_v = eval(&lam_core, &f, &globals).unwrap();
        let f_v = Value::Var(0);
        let mut fuel = FUEL_LIMIT;
        assert!(conv(1, &lam_v, &f_v, &globals, &mut fuel, 0, &mut Vec::new()).unwrap());
    }

    #[test]
    fn level_subst_renames_vars() {
        // `Type(?3)` under `[?3 := Type(?7)]` becomes `Type(?7)`; concrete
        // levels and `*` are untouched; instance entries map too.
        let mut m = HashMap::new();
        m.insert(3u32, Level::Var(7));
        let v = Value::Pi {
            name: "A".to_string(),
            dom: Box::new(Value::Sort(Sort::Type(Level::Var(3)))),
            cod: Closure::new(
                vec![Value::Sort(Sort::Star)],
                Core::Sort(Sort::Type(Level::Var(3))),
            ),
        };
        let out = subst_level_value(&v, &m);
        match out {
            Value::Pi { dom, cod, .. } => {
                assert!(matches!(*dom, Value::Sort(Sort::Type(Level::Var(7)))));
                assert!(matches!(*cod.term, Core::Sort(Sort::Type(Level::Var(7)))));
                // Closure env walked as well (`*` untouched).
                assert!(matches!(cod.env[0], Value::Sort(Sort::Star)));
            }
            _ => panic!("expected Pi"),
        }
        let g = Value::Global(2, vec![Level::Var(3), Level::Const(1)]);
        match subst_level_value(&g, &m) {
            Value::Global(2, inst) => {
                assert_eq!(inst, vec![Level::Var(7), Level::Const(1)]);
            }
            _ => panic!("expected Global"),
        }
    }

    #[test]
    fn level_vars_collected_once() {
        // Collector finds variables in types, closure envs, and instances —
        // deduplicated, in first-seen order.
        let v = Value::App(
            Box::new(Value::Global(0, vec![Level::Var(9)])),
            Box::new(Value::Sort(Sort::Type(Level::Var(4)))),
        );
        let mut out = Vec::new();
        level_vars_value(&v, &mut out);
        assert_eq!(out, vec![9, 4]);
        let mut out2 = Vec::new();
        level_vars_core(&Core::Sort(Sort::Star), &mut out2);
        assert!(out2.is_empty());
    }

    #[test]
    fn unit_eta_conv() {
        // Definitional uniqueness of `()`: converts with neutrals (which may
        // be Unit-typed), never with canonical intros of other types, sorts,
        // or type formers.
        let globals = GlobalVals::new();
        let t = |a: &Value, b: &Value| {
            let mut fuel = FUEL_LIMIT;
            conv(0, a, b, &globals, &mut fuel, 0, &mut Vec::new()).unwrap()
        };
        let pt = Value::Pt;
        // Neutrals: equal (both directions).
        assert!(t(&pt, &Value::Var(0)));
        assert!(t(&Value::Var(0), &pt));
        assert!(t(
            &pt,
            &Value::App(Box::new(Value::Var(0)), Box::new(Value::Var(1)))
        ));
        assert!(t(&pt, &Value::Global(3, vec![])));
        // Canonical others: unequal.
        assert!(!t(&pt, &Value::Inl(Box::new(Value::Var(0)))));
        assert!(!t(
            &pt,
            &Value::Pair(Box::new(Value::Pt), Box::new(Value::Pt))
        ));
        assert!(!t(&pt, &Value::Sort(Sort::Star)));
        assert!(!t(&pt, &Value::Void));
        assert!(!t(&pt, &Value::Unit));
    }

    #[test]
    fn sorts_not_equal() {
        let globals = GlobalVals::new();
        let mut fuel = FUEL_LIMIT;
        // Distinct concrete levels never convert ...
        assert!(!conv(
            0,
            &Value::Sort(Sort::Type(Level::Const(0))),
            &Value::Sort(Sort::Type(Level::Const(1))),
            &globals,
            &mut fuel,
            0,
            &mut Vec::new()
        )
        .unwrap());
        // ... and nothing lifts down into `*` ...
        assert!(!conv(
            0,
            &Value::Sort(Sort::Type(Level::Const(0))),
            &Value::Sort(Sort::Star),
            &globals,
            &mut fuel,
            0,
            &mut Vec::new()
        )
        .unwrap());
        // ... and `*` does NOT convert into `Type` (conversion is equality;
        // the `*`-into-`Type` direction is subsumption, which lives in the
        // checker's `require_sort_le`, not here — equating them inside
        // conversion collapses small and large motive families and smuggles
        // large elimination through small proofs).
        assert!(!conv(
            0,
            &Value::Sort(Sort::Star),
            &Value::Sort(Sort::Type(Level::Const(0))),
            &globals,
            &mut fuel,
            0,
            &mut Vec::new()
        )
        .unwrap());
        assert!(!conv(
            0,
            &Value::Sort(Sort::Star),
            &Value::Sort(Sort::Type(Level::Var(7))),
            &globals,
            &mut fuel,
            0,
            &mut Vec::new()
        )
        .unwrap());
    }

    #[test]
    fn w_rect_env_redex_fires_and_discriminates() {
        // Direct helper test (shape-only — no typing here): a complete
        // `w_rect` chain over a canonical `sup` chain reduces to `s a f ih`
        // (here `s` returns its first arg, so the result is `a`); partial
        // chains, neutral scrutinees, and non-W heads stay stuck (None).
        let globals = GlobalVals::new();
        let empty: Env = Vec::new();
        let mut fuel = FUEL_LIMIT;
        let a_ty = Core::Void;
        let b_fam = Core::Lam { name: "_".to_string(), body: Box::new(Core::Void) };
        let p_mot = Core::Lam { name: "_".to_string(), body: Box::new(Core::Void) };
        // s := \a f ih. a
        let s_lam = Core::Lam {
            name: "a".to_string(),
            body: Box::new(Core::Lam {
                name: "f".to_string(),
                body: Box::new(Core::Lam {
                    name: "ih".to_string(),
                    body: Box::new(Core::Bound(2)),
                }),
            }),
        };
        let chain = |f: Core, a: Core| Core::app(f, a);
        let wre = chain(
            chain(chain(chain(chain(Core::WRect, a_ty.clone()), b_fam.clone()), p_mot.clone()), s_lam.clone()),
            chain(chain(chain(chain(Core::Sup, a_ty.clone()), b_fam.clone()), a_ty.clone()), b_fam.clone()),
        );
        let v = eval(&wre, &empty, &globals).unwrap();
        // `s a f ih` with `s` returning `a` (here `a` is `Void` itself).
        assert!(matches!(v, Value::Void));
        // Partial chain (4 args, missing scrutinee): stuck, not iota.
        let partial = chain(
            chain(chain(chain(Core::WRect, a_ty.clone()), b_fam.clone()), p_mot.clone()),
            s_lam.clone(),
        );
        let pv = eval(&partial, &empty, &globals).unwrap();
        let r = w_rect_env_redex(&pv, &Value::Pt, &empty, &globals, &mut fuel, EVAL_DEPTH_LIMIT).unwrap();
        assert!(r.is_none());
        // Neutral scrutinee (unknown global): stuck.
        let nv = eval(&partial, &empty, &globals).unwrap();
        let r2 = w_rect_env_redex(&nv, &Value::Global(7, Vec::new()), &empty, &globals, &mut fuel, EVAL_DEPTH_LIMIT).unwrap();
        assert!(r2.is_none());
        // Non-W head: stuck.
        let lamv = eval(&s_lam, &empty, &globals).unwrap();
        let r3 = w_rect_env_redex(&lamv, &Value::Pt, &empty, &globals, &mut fuel, EVAL_DEPTH_LIMIT).unwrap();
        assert!(r3.is_none());
    }

    #[test]
    fn w_rect_rebuild_keeps_free_vars() {
        // Iota through a NON-mirroring environment with an OPEN family:
        // the payload family mentions an outer free variable (`Var(0)`),
        // but the environment holds closed entries at every position. The
        // rebuilt IH must keep the free variable free — resolving quoted
        // indices against the live env rebinds it (here to `Void`) and
        // silently puts a type where a term belongs.
        let globals = GlobalVals::new();
        let mut fuel = FUEL_LIMIT;
        let void = Core::Void;
        let closed_fam = Core::Lam { name: "_".to_string(), body: Box::new(Core::Void) };
        // s := \a f ih. ih Pt (forces the rebuilt IH, exposing its target).
        let s_lam = Core::Lam {
            name: "a".to_string(),
            body: Box::new(Core::Lam {
                name: "f".to_string(),
                body: Box::new(Core::Lam {
                    name: "ih".to_string(),
                    body: Box::new(Core::App(
                        Box::new(Core::Bound(0)),
                        Box::new(Core::Pt),
                    )),
                }),
            }),
        };
        // f := \_. Bound(1): ignores its argument, returns the outer free var.
        let f_lam = Core::Lam { name: "_".to_string(), body: Box::new(Core::Bound(1)) };
        let chain = |f: Core, a: Core| Core::app(f, a);
        let wre = chain(
            chain(chain(chain(Core::WRect, void.clone()), closed_fam.clone()), closed_fam.clone()),
            s_lam.clone(),
        );
        let sup = chain(
            chain(chain(chain(Core::Sup, void.clone()), closed_fam.clone()), void.clone()),
            f_lam.clone(),
        );
        // Outer free variable at level 0; evaluation env mirrors nothing.
        let outer: Env = vec![Value::Var(0)];
        let funv = eval(&wre, &outer, &globals).unwrap();
        let argv = eval(&sup, &outer, &globals).unwrap();
        let env2: Env = vec![Value::Void, Value::Void];
        let r = w_rect_env_redex(&funv, &argv, &env2, &globals, &mut fuel, EVAL_DEPTH_LIMIT)
            .unwrap()
            .expect("canonical sup target must fire iota");
        // Peel the rebuilt stuck spine `w_rect A B P s w`; the target `w`
        // is `(f Pt)` = the outer free variable, still free.
        let mut head = r;
        let mut args = Vec::new();
        loop {
            match head {
                Value::App(f, a) => {
                    args.push(*a);
                    head = *f;
                }
                _ => break,
            }
        }
        assert!(matches!(head, Value::WRect));
        assert_eq!(args.len(), 5);
        assert!(
            matches!(args[0], Value::Var(0)),
            "rebuilt target must stay free, got {:?}",
            args[0]
        );
    }

    #[test]
    fn match_iota_and_stuck() {
        // `match (inl v) ...` reduces to the left branch (iota); a neutral
        // scrutinee stays stuck with branch closures stored.
        let globals = GlobalVals::new();
        let empty: Env = Vec::new();
        let mk_match = |scrut: Core| Core::Match {
            scrut: Box::new(scrut),
            motive: Box::new(Core::Sort(Sort::Star)),
            l_name: "a".to_string(),
            l_body: Box::new(Core::Pt),
            r_name: "b".to_string(),
            r_body: Box::new(Core::Void),
        };
        let hit = mk_match(Core::Inl(Box::new(Core::Pt)));
        let v = eval(&hit, &empty, &globals).unwrap();
        assert!(matches!(v, Value::Pt));
        let stuck = mk_match(Core::Bound(0));
        let env: Env = vec![Value::Var(0)];
        let w = eval(&stuck, &env, &globals).unwrap();
        assert!(matches!(w, Value::Match { .. }));
    }

    #[test]
    fn unit_iota() {
        // `unit_rect P b ()` reduces to `b` (iota); partial applications
        // stay stuck-neutral.
        let globals = GlobalVals::new();
        let empty: Env = Vec::new();
        let redex = Core::app(
            Core::app(Core::app(Core::UnitRect, Core::Absurd), Core::Void),
            Core::Pt,
        );
        let v = eval(&redex, &empty, &globals).unwrap();
        assert!(matches!(v, Value::Void));
        let partial = Core::app(Core::UnitRect, Core::Absurd);
        let w = eval(&partial, &empty, &globals).unwrap();
        assert!(matches!(w, Value::App(_, _)));
    }

    #[test]
    fn absurd_is_stuck_neutral() {
        // `absurd` never unfolds and has no iota rule: applications of it are
        // neutral, and it is only convertible to itself.
        let globals = GlobalVals::new();
        let mut fuel = FUEL_LIMIT;
        let app = Value::App(Box::new(Value::Absurd), Box::new(Value::Void));
        let w = whnf(&app, &globals, &mut fuel).unwrap();
        assert!(matches!(w, Value::App(_, _)));
        let mut fuel = FUEL_LIMIT;
        assert!(conv(0, &Value::Absurd, &Value::Absurd, &globals, &mut fuel, 0, &mut Vec::new()).unwrap());
        let mut fuel = FUEL_LIMIT;
        assert!(!conv(0, &Value::Absurd, &Value::Void, &globals, &mut fuel, 0, &mut Vec::new()).unwrap());
    }

    #[test]
    fn pair_iota() {
        // `fst (a, b)` and `snd (a, b)` reduce; stuck scrutinees stay stuck.
        let globals = GlobalVals::new();
        let empty: Env = Vec::new();
        let pair = Core::Pair(Box::new(Core::Sort(Sort::Star)), Box::new(Core::Void));
        let f = Core::Fst(Box::new(pair.clone()));
        let v = eval(&f, &empty, &globals).unwrap();
        assert!(matches!(v, Value::Sort(Sort::Star)));
        let s = Core::Snd(Box::new(pair));
        let v = eval(&s, &empty, &globals).unwrap();
        assert!(matches!(v, Value::Void));
        // Neutral scrutinee: stuck.
        let stuck = Core::Fst(Box::new(Core::Bound(0)));
        let env: Env = vec![Value::Var(0)];
        let v = eval(&stuck, &env, &globals).unwrap();
        assert!(matches!(v, Value::Fst(_)));
    }

    #[test]
    fn sigma_pair_duality() {
        // `(a, b)` is values only: `A and B` does NOT convert with it.
        let globals = GlobalVals::new();
        let mut fuel = FUEL_LIMIT;
        let empty: Env = Vec::new();
        let sigma = Core::Sigma {
            name: "_".to_string(),
            dom: Box::new(Core::Sort(Sort::Star)),
            cod: Box::new(Core::Sort(Sort::Star)),
        };
        let pair = Core::Pair(Box::new(Core::Sort(Sort::Star)), Box::new(Core::Sort(Sort::Star)));
        let sv = eval(&sigma, &empty, &globals).unwrap();
        let pv = eval(&pair, &empty, &globals).unwrap();
        assert!(!conv(0, &sv, &pv, &globals, &mut fuel, 0, &mut Vec::new()).unwrap());
    }

    #[test]
    fn sigma_eta() {
        // `p ≡ (fst p, snd p)`: a neutral converts with its expansion, and
        // a pair converts with a neutral iff the components do.
        let globals = GlobalVals::new();
        let mut fuel = FUEL_LIMIT;
        let p = Value::Var(0);
        let eta = Value::Pair(
            Box::new(Value::Fst(Box::new(Value::Var(0)))),
            Box::new(Value::Snd(Box::new(Value::Var(0)))),
        );
        assert!(conv(0, &p, &eta, &globals, &mut fuel, 0, &mut Vec::new()).unwrap());
        // Control: different neutrals stay unequal through eta.
        let mut fuel = FUEL_LIMIT;
        let q = Value::Pair(
            Box::new(Value::Fst(Box::new(Value::Var(1)))),
            Box::new(Value::Snd(Box::new(Value::Var(1)))),
        );
        assert!(!conv(0, &p, &q, &globals, &mut fuel, 0, &mut Vec::new()).unwrap());
        // Canonicals of other types never expand.
        let mut fuel = FUEL_LIMIT;
        let inl = Value::Inl(Box::new(Value::Var(0)));
        assert!(!conv(0, &eta, &inl, &globals, &mut fuel, 0, &mut Vec::new()).unwrap());
    }
}
