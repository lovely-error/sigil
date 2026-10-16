//! Universe levels, constraints, and the satisfiability check.
//!
//! ECC-shaped hierarchy, Phase 1 (see `check.rs` header for the full story):
//! - `Level ::= Const(n) | Var(a)`. Deliberately NO `Succ`/`Max`: instead of
//!   computing successors and maxima symbolically, formation mints a fresh
//!   level variable with `<=` constraints (`Type(l) : Type(?m)` with `l < ?m`;
//!   Pi/Sigma/Either at `Type(?m)` with both sides `<= ?m`). Concrete inputs
//!   still compute directly (no variables, no constraints).
//! - `Star` (`*`, impredicative bottom) is NOT a level: level variables range
//!   over `Type`-levels (`>= 0`) only. For constraint math `Star` ranks as
//!   `-1`, so `Star <= anything` is free and `anything <= Star` (other than
//!   `Star` itself) is unsatisfiable.
//! - Constraints are difference constraints (`Le`/`Lt`) over `i64` ranks.
//!   Satisfiability = no negative cycle (Bellman-Ford with all-zero init, so
//!   disconnected components are covered too) plus the `>= 0` floor for vars.
//! - `fresh_level_var` is a process-wide atomic counter: parse order and
//!   elaboration order are both deterministic for fixed input, so ids are
//!   deterministic too. Tests must never assert specific ids.

use std::collections::HashMap;
use std::fmt;
use std::sync::atomic::{AtomicU32, Ordering};

/// A universe level: concrete `Const(n)` (`Type0`, `Type1`, ...) or an
/// inference variable `Var(a)` (surface `Type`, typical ambiguity).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Level {
    Const(u32),
    Var(u32),
}

/// Relation between levels: `<=` (cumulativity, formation bounds) or `<`
/// (axiom `Type(l) : Type(?m)` needs `l < ?m`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Rel {
    Le,
    Lt,
}

/// One level constraint `lhs rel rhs`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Constraint {
    pub lhs: Level,
    pub rhs: Level,
    pub rel: Rel,
}

impl Constraint {
    pub fn new(lhs: Level, rel: Rel, rhs: Level) -> Self {
        Self { lhs, rel, rhs }
    }
}

impl fmt::Display for Constraint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let op = match self.rel {
            Rel::Le => "<=",
            Rel::Lt => "<",
        };
        write!(f, "{} {op} {}", self.lhs, self.rhs)
    }
}

impl fmt::Display for Level {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Level::Const(n) => write!(f, "{n}"),
            Level::Var(a) => write!(f, "?{a}"),
        }
    }
}

static LEVEL_SUPPLY: AtomicU32 = AtomicU32::new(0);

/// Substitute levels through one side of a constraint.
fn subst_side(l: Level, m: &HashMap<u32, Level>) -> Level {
    match l {
        Level::Const(n) => Level::Const(n),
        Level::Var(a) => m.get(&a).copied().unwrap_or(Level::Var(a)),
    }
}

/// Substitute universe levels through a constraint (scheme instantiation).
pub fn subst_level_constraint(c: &Constraint, m: &HashMap<u32, Level>) -> Constraint {
    Constraint::new(subst_side(c.lhs, m), c.rel, subst_side(c.rhs, m))
}

/// Mint a fresh level variable id. Deterministic for fixed input (single
/// elaboration order); ids carry no meaning across runs — never assert them.
pub fn fresh_level_var() -> u32 {
    LEVEL_SUPPLY.fetch_add(1, Ordering::SeqCst)
}

/// Check a set of constraints for satisfiability. `Ok(())` means some
/// assignment of `Type`-levels (`>= 0`) to variables satisfies all of them;
/// `Err` describes one violated requirement (concrete contradiction or a
/// negative cycle through variables).
pub fn check_satisfiable(cs: &[Constraint]) -> Result<(), String> {
    // Collect variable ids.
    let mut ids: Vec<u32> = Vec::new();
    for c in cs {
        for l in [c.lhs, c.rhs] {
            if let Level::Var(a) = l {
                if !ids.contains(&a) {
                    ids.push(a);
                }
            }
        }
    }
    let idx: HashMap<u32, usize> = ids.iter().enumerate().map(|(i, a)| (*a, i)).collect();
    let nvars = ids.len();
    // Node `nvars` is the constant-zero reference. Edges `(u, v, w)` mean
    // `x_v <= x_u + w`. Variable nodes also get the `>= 0` floor as
    // `x_ref <= x_v + 0`.
    let z = nvars;
    let mut edges: Vec<(usize, usize, i64)> = Vec::new();
    for c in cs {
        let (a, b) = (c.lhs, c.rhs);
        // Strictness as offset: `a < b` iff `a + 1 <= b`.
        let off: i64 = match c.rel {
            Rel::Le => 0,
            Rel::Lt => 1,
        };
        match (a, b) {
            (Level::Const(m), Level::Const(n)) => {
                let ok = match c.rel {
                    Rel::Le => m as i64 <= n as i64,
                    Rel::Lt => (m as i64) < n as i64,
                };
                if !ok {
                    return Err(format!("level contradiction: {c}"));
                }
            }
            (Level::Const(m), Level::Var(v)) => {
                // `m (+off) <= x_v`: edge `v -> z` with weight `-(m+off)`.
                edges.push((idx[&v], z, -((m as i64) + off)));
            }
            (Level::Var(v), Level::Const(n)) => {
                // `x_v + off <= n`: edge `z -> v` with weight `n - off`.
                edges.push((z, idx[&v], (n as i64) - off));
            }
            (Level::Var(u), Level::Var(v)) => {
                // `x_u + off <= x_v`, i.e. `x_u <= x_v + (-off)`:
                // edge `v -> u` with weight `-off`.
                edges.push((idx[&v], idx[&u], -off));
            }
        }
    }
    // `Star` handling: constraints never mention `Star` as a `Level` (it is a
    // separate `Sort` constructor). Callers normalize `Star` away before
    // pushing: `Star <= _` is dropped (free), `_ <= Star` with a `Type` side
    // is an immediate error, `Star <= Star` is dropped. So nothing to do here
    // beyond the floor below.
    for v in 0..nvars {
        // Floor `x_v >= 0`: edge `v -> z` weight `0`.
        edges.push((v, z, 0));
    }
    let nnodes = nvars + 1;
    // Bellman-Ford with all-zero init (catches cycles in every component).
    let mut dist = vec![0i64; nnodes];
    let mut pred: Vec<Option<usize>> = vec![None; nnodes];
    let mut last = None;
    for _ in 0..nnodes {
        last = None;
        for (ei, &(u, v, w)) in edges.iter().enumerate() {
            if dist[v] > dist[u] + w {
                dist[v] = dist[u] + w;
                pred[v] = Some(ei);
                last = Some(v);
            }
        }
    }
    if let Some(tip) = last {
        // Negative cycle: walk back to extract it for the message. Every
        // node on a relaxed cycle has a predecessor (it relaxed this very
        // round), but a hostile shape reaching a never-relaxed node must
        // fail closed, never panic on a user program.
        let step = |v: usize, pred: &[Option<usize>]| -> Option<usize> {
            pred.get(v).and_then(|o| *o).map(|ei| edges[ei].0)
        };
        let mut v = tip;
        for _ in 0..nnodes {
            match step(v, &pred) {
                Some(u) => v = u,
                None => return Err("universe inconsistency (cyclic level constraints)".to_string()),
            }
        }
        let start = v;
        let mut cycle = vec![v];
        loop {
            match step(v, &pred) {
                Some(u) => v = u,
                None => return Err("universe inconsistency (cyclic level constraints)".to_string()),
            }
            cycle.push(v);
            if v == start || cycle.len() > nnodes + 1 {
                break;
            }
        }
        cycle.reverse();
        let involved: Vec<String> = cycle
            .iter()
            .filter_map(|&n| {
                if n == z {
                    Some("0".to_string())
                } else {
                    ids.get(n).map(|a| format!("?{a}"))
                }
            })
            .collect();
        return Err(format!(
            "universe inconsistency (cyclic level constraints through {})",
            involved.join(", ")
        ));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn concrete_levels() {
        // `0 <= 1`, `1 < 2` fine; `2 <= 1`, `1 < 1` contradictory.
        assert!(check_satisfiable(&[
            Constraint::new(Level::Const(0), Rel::Le, Level::Const(1)),
            Constraint::new(Level::Const(1), Rel::Lt, Level::Const(2)),
        ])
        .is_ok());
        assert!(check_satisfiable(&[Constraint::new(
            Level::Const(2),
            Rel::Le,
            Level::Const(1)
        )])
        .is_err());
        assert!(check_satisfiable(&[Constraint::new(
            Level::Const(1),
            Rel::Lt,
            Level::Const(1)
        )])
        .is_err());
    }

    #[test]
    fn var_bounds_and_floor() {
        // `?a >= 3`, `?a <= 5` satisfiable; `?a <= -1`-via-`?a < 0`
        // (i.e. `?a <= Const(0)-1`) violates the `>= 0` floor.
        let a = Level::Var(9001);
        assert!(check_satisfiable(&[
            Constraint::new(Level::Const(3), Rel::Le, a),
            Constraint::new(a, Rel::Le, Level::Const(5)),
        ])
        .is_ok());
        assert!(check_satisfiable(&[Constraint::new(a, Rel::Lt, Level::Const(0))]).is_err());
    }

    #[test]
    fn strict_cycle_fails_loose_cycle_passes() {
        // `?a <= ?b <= ?a` fine (set equal); `?a < ?b <= ?a` impossible.
        let (a, b) = (Level::Var(9101), Level::Var(9102));
        assert!(check_satisfiable(&[
            Constraint::new(a, Rel::Le, b),
            Constraint::new(b, Rel::Le, a),
        ])
        .is_ok());
        assert!(check_satisfiable(&[
            Constraint::new(a, Rel::Lt, b),
            Constraint::new(b, Rel::Le, a),
        ])
        .is_err());
    }

    #[test]
    fn hurkens_shaped_cycle_fails() {
        // The shape lurking inside paradoxes: `?a < ?b`, `?b <= ?c`,
        // `?c <= ?a` forces `?a < ?a`.
        let (a, b, c) = (Level::Var(9201), Level::Var(9202), Level::Var(9203));
        assert!(check_satisfiable(&[
            Constraint::new(a, Rel::Lt, b),
            Constraint::new(b, Rel::Le, c),
            Constraint::new(c, Rel::Le, a),
        ])
        .is_err());
    }
}
