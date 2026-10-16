//! First-order substitution for dependent `match` refinement.
//!
//! When `match x return P { inl a => … | inr b => … }` splits on a *variable*
//! scrutinee at level `lx`, branch bodies are checked with `x` replaced by
//! the constructor pattern — including inside the types (and values) of the
//! surrounding context entries. That replacement is what this module does.
//!
//! Design notes (all load-bearing, all tested below):
//! - Only ever variable-against-constructor-of-variable: the pattern is
//!   `Inl(Var(lf))` / `Inr(Var(lf))` for a fresh pattern level `lf`. No
//!   unification, no higher-order matching — total by construction.
//! - De Bruijn *levels* in values are absolute, so value substitution never
//!   shifts anything. Core terms use *indices* (relative), so core
//!   substitution resolves each index through the closure environment
//!   (stack order, exactly like evaluation): only an index that resolves to
//!   an entry that is *exactly* `Var(lx)` is replaced. Level arithmetic from
//!   the environment length alone is unsound here — closure environments are
//!   evaluation chains (often longer than the checking context and holding
//!   closed entries), so length-derived levels collide with live context
//!   levels and replace the wrong variable.
//! - Every closure term is scoped for its environment *plus one pending
//!   value-binder* (its own Pi/Sigma/Lam/branch binder, pushed on apply).
//!   Index `0` (past the core binders) denotes that pending binder, whose
//!   level is fresh — never `lx` — so it is always left unchanged.
//! - On any doubt (core-bound indices, the pending slot, non-variable
//!   entries, out-of-range indices, underflow), nodes are left unchanged.
//!   Skipping is fail-safe: it only ever *removes* refinement (more
//!   stuckness, i.e. possible incompleteness), never admits ill-typed terms
//!   (nothing new becomes convertible).
//! - Binary sums bind exactly one pattern variable, so substitution never
//!   changes arity/lengths anywhere. (Multi-binder patterns would need
//!   shifting — deferred with general patterns.)

use crate::core::{Closure, Core, Value};

/// Substitute the constructor pattern for level `lx` throughout a VALUE.
/// `is_left` selects `Inl`/`Inr`; the pattern variable is `lf` (the fresh
/// pattern level, valid in the extended context). Total.
pub fn subst_val(v: &Value, lx: usize, lf: usize, is_left: bool) -> Value {
    // The replacement value, built once per call site is wasteful; build
    // lazily only on hit (see `Var` arm).
    match v {
        Value::Var(l) => {
            if *l == lx {
                let inner = Value::Var(lf);
                if is_left {
                    Value::Inl(Box::new(inner))
                } else {
                    Value::Inr(Box::new(inner))
                }
            } else {
                Value::Var(*l)
            }
        }
        Value::App(f, a) => Value::App(
            Box::new(subst_val(f, lx, lf, is_left)),
            Box::new(subst_val(a, lx, lf, is_left)),
        ),
        Value::Pi { name, dom, cod } => Value::Pi {
            name: name.clone(),
            dom: Box::new(subst_val(dom, lx, lf, is_left)),
            cod: subst_closure(cod, lx, lf, is_left),
        },
        Value::Sigma { name, dom, cod } => Value::Sigma {
            name: name.clone(),
            dom: Box::new(subst_val(dom, lx, lf, is_left)),
            cod: subst_closure(cod, lx, lf, is_left),
        },
        Value::Lam { name, body } => Value::Lam {
            name: name.clone(),
            body: subst_closure(body, lx, lf, is_left),
        },
        Value::Pair(a, b) => Value::Pair(
            Box::new(subst_val(a, lx, lf, is_left)),
            Box::new(subst_val(b, lx, lf, is_left)),
        ),
        Value::Either(a, b) => Value::Either(
            Box::new(subst_val(a, lx, lf, is_left)),
            Box::new(subst_val(b, lx, lf, is_left)),
        ),
        Value::Inl(a) => Value::Inl(Box::new(subst_val(a, lx, lf, is_left))),
        Value::Inr(b) => Value::Inr(Box::new(subst_val(b, lx, lf, is_left))),
        Value::Quotient(a, r) => Value::Quotient(
            Box::new(subst_val(a, lx, lf, is_left)),
            Box::new(subst_val(r, lx, lf, is_left)),
        ),
        Value::QuotMk(a) => Value::QuotMk(Box::new(subst_val(a, lx, lf, is_left))),
        Value::Fst(p) => Value::Fst(Box::new(subst_val(p, lx, lf, is_left))),
        Value::Snd(p) => Value::Snd(Box::new(subst_val(p, lx, lf, is_left))),
        Value::Match { scrut, mot, l_name, l_body, r_name, r_body } => Value::Match {
            scrut: Box::new(subst_val(scrut, lx, lf, is_left)),
            mot: Box::new(subst_val(mot, lx, lf, is_left)),
            l_name: l_name.clone(),
            l_body: subst_closure(l_body, lx, lf, is_left),
            r_name: r_name.clone(),
            r_body: subst_closure(r_body, lx, lf, is_left),
        },
        // Metas: the node itself is level-free (identified by id); the
        // spine entries are ordinary values and substitute normally.
        Value::Meta { id, span, spine } => Value::Meta {
            id: *id,
            span: *span,
            spine: spine.iter().map(|v| subst_val(v, lx, lf, is_left)).collect(),
        },
        // Atoms (sorts, globals incl. instances, constants) contain no term
        // variables (universe levels live in a separate namespace).
        Value::Global(_, _)
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
        | Value::WRect => v.clone(),
    }
}

/// Substitute through a closure: environment entries (values) directly, and
/// the core term resolved through the environment (see `subst_core`).
fn subst_closure(c: &Closure, lx: usize, lf: usize, is_left: bool) -> Closure {
    Closure {
        env: c.env.iter().map(|v| subst_val(v, lx, lf, is_left)).collect(),
        term: Box::new(subst_core(&c.term, &c.env, lx, lf, is_left, 0)),
    }
}

/// Substitute in CORE terms with an environment for resolving variables:
/// `Bound(ix)` past `c` core binders resolves like evaluation against the
/// closure environment plus its pending value-binder — index `0` is the
/// pending binder (fresh level: never `lx`), deeper indices walk the
/// environment stack (innermost last, exactly like `eval`). Only an index
/// resolving to an entry that is *exactly* `Var(lx)` is replaced, by the
/// pattern core (`Inl`/`Inr` of the `lf`-denoting index in the same scope).
/// Checked arithmetic throughout: core-bound indices, the pending slot,
/// non-variable entries, out-of-range indices, and underflow are all left
/// unchanged (fail-safe — see module docs).
pub fn subst_core(
    t: &Core,
    env: &[Value],
    lx: usize,
    lf: usize,
    is_left: bool,
    c: usize,
) -> Core {
    // Mirror guard: the replacement index for `lf` resolves (stack order,
    // past the pending slot) to environment *position* `lf`, so `lf` must be
    // named there — `env[lf]` must be exactly `Var(lf)`. Shorter
    // environments (closures captured before the pattern binder was pushed)
    // or non-mirror ones cannot name the pattern at all: substituting would
    // capture a core binder or denote the wrong level. Skip the whole term
    // (fail-safe: less refinement, never a changed meaning).
    if env.len() <= lf || !matches!(env.get(lf), Some(Value::Var(l)) if *l == lf) {
        return t.clone();
    }
    match t {
        Core::Bound(ix) => {
            // Core binders shadow: nothing behind them has an absolute level.
            if *ix < c {
                return Core::Bound(*ix);
            }
            let j = (*ix - c) as u64;
            // Index 0 past the core binders is the pending value-binder
            // (pushed on apply): its level is fresh, never `lx`.
            if j == 0 {
                return Core::Bound(*ix);
            }
            // Stack offset into the environment (0 = innermost entry).
            let e = j - 1;
            if e >= env.len() as u64 {
                return Core::Bound(*ix);
            }
            let entry = &env[env.len() - 1 - e as usize];
            if !matches!(entry, Value::Var(l) if *l == lx) {
                return Core::Bound(*ix);
            }
            // Replace with the pattern at this same position: the `lf`
            // level denotes index `(env.len() + 1 + c) - 1 - lf` here (the
            // `+1` is the pending binder slot).
            let total = env.len() as u64 + 1 + c as u64;
            let replacement = total.checked_sub(1 + lf as u64);
            match replacement {
                Some(rix) => {
                    let inner = Core::Bound(rix as usize);
                    if is_left {
                        Core::Inl(Box::new(inner))
                    } else {
                        Core::Inr(Box::new(inner))
                    }
                }
                // `lf` out of scope here (cannot happen for well-formed
                // inputs, where the pattern level is always in range):
                // leave unchanged (fail-safe).
                None => Core::Bound(*ix),
            }
        }
        Core::App(f, a) => Core::App(
            Box::new(subst_core(f, env, lx, lf, is_left, c)),
            Box::new(subst_core(a, env, lx, lf, is_left, c)),
        ),
        Core::Pi { name, dom, cod } => Core::Pi {
            name: name.clone(),
            dom: Box::new(subst_core(dom, env, lx, lf, is_left, c)),
            cod: Box::new(subst_core(cod, env, lx, lf, is_left, c + 1)),
        },
        Core::Sigma { name, dom, cod } => Core::Sigma {
            name: name.clone(),
            dom: Box::new(subst_core(dom, env, lx, lf, is_left, c)),
            cod: Box::new(subst_core(cod, env, lx, lf, is_left, c + 1)),
        },
        Core::Lam { name, body } => Core::Lam {
            name: name.clone(),
            body: Box::new(subst_core(body, env, lx, lf, is_left, c + 1)),
        },
        Core::Pair(a, b) => Core::Pair(
            Box::new(subst_core(a, env, lx, lf, is_left, c)),
            Box::new(subst_core(b, env, lx, lf, is_left, c)),
        ),
        Core::Either(a, b) => Core::Either(
            Box::new(subst_core(a, env, lx, lf, is_left, c)),
            Box::new(subst_core(b, env, lx, lf, is_left, c)),
        ),
        Core::Inl(a) => Core::Inl(Box::new(subst_core(a, env, lx, lf, is_left, c))),
        Core::Inr(b) => Core::Inr(Box::new(subst_core(b, env, lx, lf, is_left, c))),
        Core::Quotient(a, r) => Core::Quotient(
            Box::new(subst_core(a, env, lx, lf, is_left, c)),
            Box::new(subst_core(r, env, lx, lf, is_left, c)),
        ),
        Core::QuotMk(a) => Core::QuotMk(Box::new(subst_core(a, env, lx, lf, is_left, c))),
        Core::Fst(p) => Core::Fst(Box::new(subst_core(p, env, lx, lf, is_left, c))),
        Core::Snd(p) => Core::Snd(Box::new(subst_core(p, env, lx, lf, is_left, c))),
        Core::Match { scrut, motive, l_name, l_body, r_name, r_body } => Core::Match {
            scrut: Box::new(subst_core(scrut, env, lx, lf, is_left, c)),
            motive: Box::new(subst_core(motive, env, lx, lf, is_left, c)),
            l_name: l_name.clone(),
            l_body: Box::new(subst_core(l_body, env, lx, lf, is_left, c + 1)),
            r_name: r_name.clone(),
            r_body: Box::new(subst_core(r_body, env, lx, lf, is_left, c + 1)),
        },
        Core::Let { name, ann, val, body } => Core::Let {
            name: name.clone(),
            ann: ann
                .as_ref()
                .map(|a| Box::new(subst_core(a, env, lx, lf, is_left, c))),
            val: Box::new(subst_core(val, env, lx, lf, is_left, c)),
            body: Box::new(subst_core(body, env, lx, lf, is_left, c + 1)),
        },
        Core::Ann(e, t) => Core::Ann(
            Box::new(subst_core(e, env, lx, lf, is_left, c)),
            Box::new(subst_core(t, env, lx, lf, is_left, c)),
        ),
        // Atoms and closed sorts: identity (instances untouched — separate
        // namespace; holes carry no indices).
        Core::Global(_, _)
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
        | Core::WRect
        | Core::Hole { .. } => t.clone(),
    }
}

// ---------------------------------------------------------------------------
// Metavariable traversals (for hole elaboration — see `check.rs`)
// ---------------------------------------------------------------------------
// All three resolve closure terms through their environments with the same
// discipline as `subst_core` (stack order like evaluation; core binders and
// the pending value-binder carry no absolute level). They are total and
// structural; depth is bounded by the value itself.

/// Whether a value mentions any metavariable (used to route conversion
/// around `conv`, which only decides closed problems).
pub fn contains_meta(v: &Value) -> bool {
    match v {
        Value::Meta { .. } => true,
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
        | Value::Quotient(f, a) => contains_meta(f) || contains_meta(a),
        Value::Pi { dom, cod, .. } | Value::Sigma { dom, cod, .. } => {
            contains_meta(dom) || contains_meta_closure(cod)
        }
        Value::Lam { body, .. } => contains_meta_closure(body),
        Value::Inl(a) | Value::Inr(a) | Value::Fst(a) | Value::Snd(a) | Value::QuotMk(a) => {
            contains_meta(a)
        }
        Value::Match { scrut, mot, l_body, r_body, .. } => {
            contains_meta(scrut)
                || contains_meta(mot)
                || contains_meta_closure(l_body)
                || contains_meta_closure(r_body)
        }
    }
}

fn contains_meta_closure(c: &Closure) -> bool {
    c.env.iter().any(contains_meta) || contains_meta_core(&c.term)
}

fn contains_meta_core(t: &Core) -> bool {
    match t {
        Core::Hole { .. } => true,
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
            contains_meta_core(dom) || contains_meta_core(cod)
        }
        Core::Pair(a, b)
        | Core::Either(a, b)
        | Core::App(a, b)
        | Core::Quotient(a, b)
        | Core::Ann(a, b) => contains_meta_core(a) || contains_meta_core(b),
        Core::Inl(a)
        | Core::Inr(a)
        | Core::Fst(a)
        | Core::Snd(a)
        | Core::QuotMk(a)
        | Core::Lam { body: a, .. } => contains_meta_core(a),
        Core::Match { scrut, motive, l_body, r_body, .. } => {
            contains_meta_core(scrut)
                || contains_meta_core(motive)
                || contains_meta_core(l_body)
                || contains_meta_core(r_body)
        }
        Core::Let { ann, val, body, .. } => {
            ann.as_ref().is_some_and(|a| contains_meta_core(a))
                || contains_meta_core(val)
                || contains_meta_core(body)
        }
    }
}

/// Whether metavariable `id` occurs in a value (occurs check for assignment:
/// assigning `?id := v` with `?id` inside `v` would build an infinite term).
/// Metavariables are absolute by id, so no environment resolution is needed
/// here — every node is visited, including closure environments and terms.
pub fn occurs_meta(id: u32, v: &Value) -> bool {
    match v {
        Value::Meta { id: j, spine, .. } => {
            *j == id || spine.iter().any(|e| occurs_meta(id, e))
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
        | Value::Quotient(f, a) => occurs_meta(id, f) || occurs_meta(id, a),
        Value::Pi { dom, cod, .. } | Value::Sigma { dom, cod, .. } => {
            occurs_meta(id, dom) || occurs_meta_closure(id, cod)
        }
        Value::Lam { body, .. } => occurs_meta_closure(id, body),
        Value::Inl(a) | Value::Inr(a) | Value::Fst(a) | Value::Snd(a) | Value::QuotMk(a) => {
            occurs_meta(id, a)
        }
        Value::Match { scrut, mot, l_body, r_body, .. } => {
            occurs_meta(id, scrut)
                || occurs_meta(id, mot)
                || occurs_meta_closure(id, l_body)
                || occurs_meta_closure(id, r_body)
        }
    }
}

fn occurs_meta_closure(id: u32, c: &Closure) -> bool {
    c.env.iter().any(|e| occurs_meta(id, e)) || occurs_meta_core(id, &c.term)
}

fn occurs_meta_core(id: u32, t: &Core) -> bool {
    match t {
        Core::Hole { id: j, .. } => *j == id,
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
            occurs_meta_core(id, dom) || occurs_meta_core(id, cod)
        }
        Core::Pair(a, b)
        | Core::Either(a, b)
        | Core::App(a, b)
        | Core::Quotient(a, b)
        | Core::Ann(a, b) => occurs_meta_core(id, a) || occurs_meta_core(id, b),
        Core::Inl(a)
        | Core::Inr(a)
        | Core::Fst(a)
        | Core::Snd(a)
        | Core::QuotMk(a)
        | Core::Lam { body: a, .. } => occurs_meta_core(id, a),
        Core::Match { scrut, motive, l_body, r_body, .. } => {
            occurs_meta_core(id, scrut)
                || occurs_meta_core(id, motive)
                || occurs_meta_core(id, l_body)
                || occurs_meta_core(id, r_body)
        }
        Core::Let { ann, val, body, .. } => {
            ann.as_ref().is_some_and(|a| occurs_meta_core(id, a))
                || occurs_meta_core(id, val)
                || occurs_meta_core(id, body)
        }
    }
}

/// Collect the free de Bruijn *levels* of a value (duplicates kept; use a set
/// at the call site if needed). Resolution mirrors evaluation exactly: core
/// binders and the closure pending slot carry no absolute level and are
/// skipped; deeper indices resolve through the environment stack, and
/// non-variable entries contribute the levels inside them. Used to bound
/// metavariable solutions to the context that created them.
pub fn free_levels_value(v: &Value, out: &mut Vec<usize>) {
    match v {
        Value::Var(l) => out.push(*l),
        Value::Global(_, _)
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
        | Value::WRect => {}
        Value::App(f, a)
        | Value::Pair(f, a)
        | Value::Either(f, a)
        | Value::Quotient(f, a) => {
            free_levels_value(f, out);
            free_levels_value(a, out);
        }
        Value::Pi { dom, cod, .. } | Value::Sigma { dom, cod, .. } => {
            free_levels_value(dom, out);
            free_levels_closure(cod, out);
        }
        Value::Lam { body, .. } => free_levels_closure(body, out),
        Value::Inl(a) | Value::Inr(a) | Value::Fst(a) | Value::Snd(a) | Value::QuotMk(a) => {
            free_levels_value(a, out);
        }
        Value::Match { scrut, mot, l_body, r_body, .. } => {
            free_levels_value(scrut, out);
            free_levels_value(mot, out);
            free_levels_closure(l_body, out);
            free_levels_closure(r_body, out);
        }
        // A metavariable's own level footprint is its spine's (the unknown
        // itself contributes no level; its solution must fit the spine).
        Value::Meta { spine, .. } => {
            for e in spine {
                free_levels_value(e, out);
            }
        }
    }
}

fn free_levels_closure(c: &Closure, out: &mut Vec<usize>) {
    for e in &c.env {
        free_levels_value(e, out);
    }
    free_levels_core(&c.term, &c.env, 0, out);
}

fn free_levels_core(t: &Core, env: &[Value], c: usize, out: &mut Vec<usize>) {
    match t {
        Core::Bound(ix) => {
            // Core binders and the pending slot carry no absolute level.
            if *ix < c + 1 {
                return;
            }
            // Stack offset into the environment (0 = innermost entry).
            let e = ix - c - 1;
            if e >= env.len() {
                return;
            }
            let entry = &env[env.len() - 1 - e];
            match entry {
                // The entry IS the variable: record its absolute level.
                Value::Var(l) => out.push(*l),
                // Otherwise the index denotes this value: collect inside it.
                _ => free_levels_value(entry, out),
            }
        }
        Core::Hole { .. } => {}
        Core::Global(_, _)
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
        | Core::WRect => {}
        Core::Pi { dom, cod, .. } | Core::Sigma { dom, cod, .. } => {
            free_levels_core(dom, env, c, out);
            free_levels_core(cod, env, c + 1, out);
        }
        Core::Pair(a, b)
        | Core::Either(a, b)
        | Core::App(a, b)
        | Core::Quotient(a, b)
        | Core::Ann(a, b) => {
            free_levels_core(a, env, c, out);
            free_levels_core(b, env, c, out);
        }
        // `Inl`/`Inr`/`Fst`/`Snd`/`QuotMk` wrap terms without binding
        // anything (only `Lam` — and match/let bodies above — extend `c`).
        Core::Inl(a) | Core::Inr(a) | Core::Fst(a) | Core::Snd(a) | Core::QuotMk(a) => {
            free_levels_core(a, env, c, out)
        }
        Core::Lam { body: a, .. } => free_levels_core(a, env, c + 1, out),
        Core::Match { scrut, motive, l_body, r_body, .. } => {
            free_levels_core(scrut, env, c, out);
            free_levels_core(motive, env, c, out);
            free_levels_core(l_body, env, c + 1, out);
            free_levels_core(r_body, env, c + 1, out);
        }
        Core::Let { ann, val, body, .. } => {
            if let Some(a) = ann {
                free_levels_core(a, env, c, out);
            }
            free_levels_core(val, env, c, out);
            free_levels_core(body, env, c + 1, out);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::{Env, GlobalVals, Sort};

    fn lvl(l: usize) -> Value {
        Value::Var(l)
    }
    /// Structural comparison for tests (`Value::PartialEq` is deliberately
    /// shallow — atoms only — since typing uses `conv`, never `==`).
    fn dbg(v: &Value) -> String {
        format!("{v:?}")
    }

    #[test]
    fn var_hit_and_miss() {
        // Hit: `Var(2)` becomes `Inl(Var(9))`; miss: others untouched.
        assert_eq!(
            dbg(&subst_val(&lvl(2), 2, 9, true)),
            dbg(&Value::Inl(Box::new(Value::Var(9))))
        );
        assert_eq!(
            dbg(&subst_val(&lvl(2), 2, 9, false)),
            dbg(&Value::Inr(Box::new(Value::Var(9))))
        );
        assert_eq!(dbg(&subst_val(&lvl(5), 2, 9, true)), dbg(&lvl(5)));
    }

    #[test]
    fn structural_walk() {
        // Goes through App/Pi without shifting unrelated levels.
        let v = Value::App(
            Box::new(lvl(2)),
            Box::new(Value::Pi {
                name: "x".to_string(),
                dom: Box::new(Value::Sort(Sort::Star)),
                cod: Closure { env: vec![lvl(2)], term: Box::new(Core::Bound(1)) },
            }),
        );
        let out = subst_val(&v, 2, 9, true);
        // Head became the pattern; closure env entry substituted; the core
        // `Bound(1)` resolves through the env to `Var(2)` (a hit), but the
        // pattern level 9 is out of scope here — unchanged (fail-safe).
        match out {
            Value::App(f, a) => {
                assert_eq!(dbg(&f), dbg(&Value::Inl(Box::new(Value::Var(9)))));
                match *a {
                    Value::Pi { cod, .. } => {
                        assert_eq!(cod.env.len(), 1);
                        assert_eq!(dbg(&cod.env[0]), dbg(&Value::Inl(Box::new(Value::Var(9)))));
                        assert_eq!(*cod.term, Core::Bound(1));
                    }
                    _ => panic!("expected Pi"),
                }
            }
            _ => panic!("expected App"),
        }
    }

    #[test]
    fn core_resolution() {
        // Env-resolving indices: `Bound(2)` with env `[Var(7), Var(2), Var(8)]`
        // resolves (stack order, past the pending slot) to `Var(2)` → hit;
        // `Bound(1)` resolves to `Var(8)` → miss; `Bound(0)` is the pending
        // binder slot → always missed.
        let env = vec![lvl(7), lvl(2), lvl(8)];
        // Hit but pattern level out of scope → unchanged (fail-safe).
        assert_eq!(
            subst_core(&Core::Bound(2), &env, 2, 9, true, 0),
            Core::Bound(2)
        );
        // The pattern level must be NAMED in the environment (`env[lf]` is
        // exactly `Var(lf)`): here `env[0]` is `Var(7)`, so `lf = 0` is not
        // nameable — unchanged, even though the target resolves. (The old
        // arithmetic replaced it with `Inl(Bound(3))`, which denotes `Var(7)`
        // here, not the pattern — a miscapture.)
        assert_eq!(
            subst_core(&Core::Bound(2), &env, 2, 0, true, 0),
            Core::Bound(2)
        );
        // Genuine mirror environment: `env[lf]` names the pattern, so the
        // hit replaces with the pattern at the resolving index. Env
        // `[Var(0), Var(1), Var(2)]`, target 1, pattern 2: `Bound(2)`
        // resolves to `Var(1)` → `Inl(Bound(1))`, and `Bound(1)` resolves
        // back to `env[2] = Var(2)`, exactly the pattern level.
        let dense = vec![lvl(0), lvl(1), lvl(2)];
        assert_eq!(
            subst_core(&Core::Bound(2), &dense, 1, 2, true, 0),
            Core::Inl(Box::new(Core::Bound(1)))
        );
        // Misses: non-target entry, pending slot, core binder.
        assert_eq!(
            subst_core(&Core::Bound(1), &env, 2, 0, true, 0),
            Core::Bound(1)
        );
        assert_eq!(
            subst_core(&Core::Bound(0), &env, 2, 0, true, 0),
            Core::Bound(0)
        );
        let lam = Core::Lam { name: "x".into(), body: Box::new(Core::Bound(0)) };
        assert_eq!(subst_core(&lam, &env, 2, 0, true, 0), lam);
    }

    #[test]
    fn stale_env_no_false_hit() {
        // Regression: closure environments are evaluation chains (often
        // longer than the checking context, mixing closed entries), so
        // length-derived levels collide with live levels. Resolution must go
        // through the actual entries: `Bound(3)` here would denote level 1
        // by length arithmetic, but resolves to a closed entry — no hit.
        // (This exact shape corrupted `w_rect` induction motives: the `P`
        // position was rewritten with the match pattern.)
        let closed_a = Value::Global(4, Vec::new());
        let closed_b = Value::Global(5, Vec::new());
        let p_lam = Value::Lam {
            name: "_".into(),
            body: Closure { env: vec![lvl(0)], term: Box::new(Core::Global(6, Vec::new())) },
        };
        let env = vec![closed_a, closed_b, p_lam, lvl(1), lvl(2)];
        let head = Core::App(
            Box::new(Core::Bound(3)),
            Box::new(Core::App(
                Box::new(Core::Bound(1)),
                Box::new(Core::Bound(0)),
            )),
        );
        // Nothing replaced: head resolves to closed `Bf`, arg resolves to
        // `Var(2)` (not the target level 1), tail is the pending slot.
        assert_eq!(subst_core(&head, &env, 1, 4, false, 0), head);
        // The old arithmetic replaced `Bound(2)` (resolving to `Var(1)`) with
        // the pattern at index 1 — but index 1 resolves back to `Var(2)`,
        // not the pattern level 4 (`env[4]` is `Var(2)`). A replacement must
        // denote `lf`; this one did not, so the whole term stays unchanged.
        let occ = Core::App(
            Box::new(Core::Bound(3)),
            Box::new(Core::Bound(2)),
        );
        assert_eq!(subst_core(&occ, &env, 1, 4, false, 0), occ);
    }

    #[test]
    fn short_env_skips() {
        // Closures captured before the pattern binder was pushed have
        // environments shorter than `lf + 1`: the pattern is unnameable, so
        // substitution is the identity (the old arithmetic produced a
        // core-bound index here — variable capture).
        let env = vec![lvl(0), lvl(1)];
        assert_eq!(
            subst_core(&Core::Bound(2), &env, 1, 5, true, 0),
            Core::Bound(2)
        );
        // Same under a core binder (the guard is scope-independent).
        let lam = Core::Lam { name: "x".into(), body: Box::new(Core::Bound(3)) };
        assert_eq!(subst_core(&lam, &env, 1, 5, true, 0), lam);
    }

    #[test]
    fn underflow_is_identity() {
        // Stuck/out-of-range indices never panic and never match.
        let env = vec![lvl(0), lvl(1), lvl(2)];
        assert_eq!(
            subst_core(&Core::Bound(7), &env, 2, 9, true, 0),
            Core::Bound(7)
        );
        // Empty environment: the pending slot and nothing else.
        let empty: Vec<Value> = Vec::new();
        assert_eq!(
            subst_core(&Core::Bound(0), &empty, 0, 0, false, 0),
            Core::Bound(0)
        );
        assert_eq!(
            subst_core(&Core::Bound(3), &empty, 0, 0, false, 0),
            Core::Bound(3)
        );
    }

    #[test]
    fn free_levels_sees_through_nonbinders() {
        // `Inl`/`Inr`/`Fst`/`Snd`/`QuotMk` bind nothing: a variable under
        // them resolves through the environment like anywhere else (the
        // level must be collected for hole solutions to stay in scope).
        let env = vec![lvl(3)];
        let mut out = Vec::new();
        free_levels_core(&Core::Inl(Box::new(Core::Bound(1))), &env, 0, &mut out);
        assert_eq!(out, vec![3]);
        let mut out2 = Vec::new();
        free_levels_core(&Core::Fst(Box::new(Core::Bound(1))), &env, 0, &mut out2);
        assert_eq!(out2, vec![3]);
        // ...while a genuine core binder still shadows its index ...
        let lam = Core::Lam { name: "x".into(), body: Box::new(Core::Inl(Box::new(Core::Bound(1)))) };
        let mut out3 = Vec::new();
        free_levels_core(&lam, &env, 0, &mut out3);
        assert!(out3.is_empty());
        // ... and resolution continues correctly beneath binders (the old
        // grouping skipped this: `Bound(2)` denotes the outer entry).
        let env2 = vec![lvl(7), lvl(8)];
        let lam2 = Core::Lam { name: "x".into(), body: Box::new(Core::Inl(Box::new(Core::Bound(2)))) };
        let mut out4 = Vec::new();
        free_levels_core(&lam2, &env2, 0, &mut out4);
        assert_eq!(out4, vec![8]);
    }

    #[test]
    fn subst_replacement_denotes_pattern() {
        // The audit's scenario (`env.len() == lf`): with env `[Var(0),
        // Var(1)]`, target level 0, pattern level 2, `Bound(2)` resolves to
        // `Var(0)` (a hit) — but the pattern level is unnameable here
        // (`env.len() <= lf`), so the term stays unchanged. The old code
        // produced `Inl(Bound(0))` — the pending slot, which denotes
        // whatever is applied later, not level 2. (On the real match path
        // this shape cannot occur: the branch context always names `lf` at
        // mirror position, since entries only append.)
        let env = vec![lvl(0), lvl(1)];
        assert_eq!(
            subst_core(&Core::Bound(2), &env, 0, 2, true, 0),
            Core::Bound(2)
        );
    }

    #[test]
    fn subst_is_noop_without_target() {
        // A value with no occurrence comes back structurally equal.
        let v = Value::Pi {
            name: "x".to_string(),
            dom: Box::new(Value::Sort(Sort::Star)),
            cod: Closure { env: vec![], term: Box::new(Core::Bound(0)) },
        };
        let _env: Env = Vec::new();
        let _globals = GlobalVals::new();
        assert_eq!(dbg(&subst_val(&v, 4, 9, true)), dbg(&v));
    }

    fn meta(id: u32, spine: Vec<Value>) -> Value {
        Value::Meta { id, span: crate::lexer::Span::empty(0), spine }
    }

    #[test]
    fn contains_meta_finds_nested() {
        // Direct, in spines, through closures (env and term), and in cores.
        assert!(contains_meta(&meta(3, vec![lvl(0)])));
        assert!(contains_meta(&Value::App(
            Box::new(lvl(0)),
            Box::new(meta(3, vec![])),
        )));
        assert!(contains_meta(&Value::Lam {
            name: "x".into(),
            body: Closure { env: vec![lvl(0)], term: Box::new(Core::Hole { id: 7, span: crate::lexer::Span::empty(0) }) },
        }));
        assert!(!contains_meta(&lvl(0)));
        assert!(!contains_meta(&Value::App(Box::new(lvl(0)), Box::new(lvl(1)))));
        // Substitution preserves the finding (spine entries substitute).
        let v = meta(3, vec![lvl(2)]);
        let out = subst_val(&v, 2, 9, true);
        assert!(contains_meta(&out));
    }

    #[test]
    fn occurs_meta_through_assignments_shape() {
        // Direct occurrence, nested in spine, nested in closure envs/terms.
        assert!(occurs_meta(3, &meta(3, vec![lvl(0)])));
        assert!(occurs_meta(3, &meta(4, vec![meta(3, vec![])])));
        assert!(!occurs_meta(3, &meta(4, vec![lvl(0)])));
        assert!(occurs_meta(3, &Value::Lam {
            name: "x".into(),
            body: Closure {
                env: vec![meta(3, vec![])],
                term: Box::new(Core::Bound(1)),
            },
        }));
        assert!(!occurs_meta(3, &lvl(3)));
    }

    #[test]
    fn free_levels_resolves_env() {
        // `Bound(2)` with env `[Var(7), Var(2), Var(8)]` resolves (stack
        // order, past the pending slot) to `Var(2)` — level 2 is free.
        let env = vec![lvl(7), lvl(2), lvl(8)];
        let mut out = Vec::new();
        free_levels_core(&Core::Bound(2), &env, 0, &mut out);
        assert_eq!(out, vec![2]);
        // Pending slot and core binders contribute nothing.
        let mut out2 = Vec::new();
        free_levels_core(&Core::Bound(0), &env, 0, &mut out2);
        assert!(out2.is_empty());
        let lam = Core::Lam { name: "x".into(), body: Box::new(Core::Bound(0)) };
        let mut out3 = Vec::new();
        free_levels_core(&lam, &env, 0, &mut out3);
        assert!(out3.is_empty());
        // Non-variable entries contribute the levels inside them.
        let env2 = vec![Value::App(Box::new(lvl(5)), Box::new(lvl(6)))];
        let mut out4 = Vec::new();
        free_levels_core(&Core::Bound(1), &env2, 0, &mut out4);
        assert_eq!(out4, vec![5, 6]);
        // Values: meta spines contribute, the unknown itself nothing.
        let mut out5 = Vec::new();
        free_levels_value(&meta(9, vec![lvl(4)]), &mut out5);
        assert_eq!(out5, vec![4]);
    }
}
