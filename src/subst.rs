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

    fn lvl(l: usize) -> Value {
        Value::Var(l)
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

    fn meta(id: u32, spine: Vec<Value>) -> Value {
        Value::Meta { id, span: crate::lexer::Span::empty(0), spine }
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
