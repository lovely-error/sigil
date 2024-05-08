use core::{cell::UnsafeCell, fmt::{Debug, Write}, sync::atomic::compiler_fence};
use std::{borrow::Cow, collections::{HashSet, VecDeque}, iter::zip, ptr::addr_of_mut, rc::Rc};

use crate::{parser::{Atom, RefinedPExpr}, sema::{ScopedDecl, GenericError, DefId, ScopedTerm, ThinPExpr, Lambda, ScopeCheckCtx, scope_check_decls, RcBox, ScopedTermRepr, render_term, render_thin_pexpr_impl, render_lambda, render_thin_pexpr, render_args, render_decl_impl, render_global_ix, render_term_impl, render_lambda_impl, render_args_impl, SubstIndex}, utils::{Outcome, inside_out}, lexer::{pad_string, SourceTextParser}};


#[derive(Debug, Clone, Copy, PartialEq)]
enum CheckState {
  Untouched,
  Began,
  Ok,
  Bad
}

#[derive(Debug)]
enum ElabIssue {
  UnproductiveCycle(Vec<DefId>),
  InvalidInhabitance,
  InvalidBinder
}

struct CheckableDecl(UnsafeCell<CheckableDeclInner>);
#[derive(Debug)]
struct CheckableDeclInner {
  scoped_decl: ScopedDecl,
  check_state: CheckState,
  elab_trace: Option<String>,
  issues: Vec<ElabIssue>
}
impl CheckableDecl {
  fn new(
    sd: ScopedDecl
  ) -> Self {
    Self(UnsafeCell::new(CheckableDeclInner {
      scoped_decl: sd, check_state: CheckState::Untouched, elab_trace: None,
      issues: vec![]
    }))
  }
  fn inner(&self) -> &mut CheckableDeclInner {
    unsafe { &mut*self.0.get() }
  }
  fn get_value(&self) -> ScopedTerm {
    unsafe{(*self.0.get()).scoped_decl.value.shallow_clone()}
  }
  fn get_type(&self) -> ScopedTerm {
    unsafe{(*self.0.get()).scoped_decl.type_.shallow_clone()}
  }
  fn log_elab_if_requested(&self, op: impl FnOnce(&mut dyn Write)) {
    let inner = unsafe {&mut*self.0.get()};
    if let Some(et) = inner.elab_trace.as_mut() {
      op(et);
      et.push_str("\n\n")
    }
  }
}
impl Debug for CheckableDecl {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
      f.debug_tuple("CheckableDecl").field(unsafe{&*self.0.get()}).finish()
  }
}
#[derive(Debug)]
struct ScopedEnv {
  decls: Vec<CheckableDecl>
}
struct ElabItem {

}
struct ElabEnv {
  defs: ScopedEnv,
  postponed: VecDeque<ElabItem>,
}
impl ElabEnv {
  fn get_def(&self, gix: DefId) -> &CheckableDecl {
    &self.defs.decls[gix.get_def_index()]
  }
  fn new_from_scoped_defs(defs: Vec<ScopedDecl>) -> ElabEnv {
    let checakbles =
      defs
      .into_iter()
      .map(CheckableDecl::new)
      .collect();
    ElabEnv { defs: ScopedEnv { decls: checakbles }, postponed: VecDeque::new() }
  }
}
impl Debug for ElabEnv {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let mut s = f.debug_struct("ElabEnv");
    s.field("defs", &self.defs);
    s.finish()
  }
}

fn check_productivity(
  ctx: &ElabEnv,
  start_decl: &CheckableDecl,
  term: &ScopedTerm,
  found_ground_terms: &mut bool,
  mut trace: Vec<DefId>
) {
  match term.get_repr() {
    ScopedTermRepr::App(head, _) => {
      check_productivity(ctx, start_decl, head, found_ground_terms, trace);
    },
    ScopedTermRepr::GlobalRef(id) => {
      let reappears = trace.contains(id);
      if reappears { // this is a cycle.
        if !*found_ground_terms { // which produces no ground terms
          start_decl.inner().issues.push(ElabIssue::UnproductiveCycle(trace));
        }
        return;
      }
      trace.push(*id);
      let next_decl = ctx.get_def(*id);
      let next_term = &next_decl.inner().scoped_decl.value;
      check_productivity(ctx, start_decl, next_term, found_ground_terms, trace);
    },
    ScopedTermRepr::Lambda(clauses) => {
      let mut count = 0;
      for clause in clauses {
        let mut found = false;
        check_productivity(ctx, start_decl, &clause, &mut found, trace.clone());
        if found { count += 1 }
      }
      if count == clauses.len() {
        *found_ground_terms = true;
      }
    }
    ScopedTermRepr::LetGroup(_, _) => todo!(),
    ScopedTermRepr::SubstRef(_) |
    ScopedTermRepr::Sigma { .. } |
    ScopedTermRepr::Pi { .. } |
    ScopedTermRepr::Void |
    ScopedTermRepr::Pt |
    ScopedTermRepr::Either(_, _) |
    ScopedTermRepr::Arrow(_, _) |
    ScopedTermRepr::Tuple(_, _) |
    ScopedTermRepr::Inl(_) |
    ScopedTermRepr::Inr(_) |
    ScopedTermRepr::Pair(_, _) => {
      *found_ground_terms = true;
      return;
    },
    ScopedTermRepr::Null => (),
    ScopedTermRepr::USort |
    ScopedTermRepr::Star => (),
    ScopedTermRepr::LambdaHead(_, tail) => {
      check_productivity(ctx, start_decl, tail, found_ground_terms, trace)
    },
  }
}

fn elab(
  env: &ElabEnv
) {
  for item in &env.defs.decls {
    let mut found_ground = false;
    let trace = vec![item.inner().scoped_decl.index];
    check_productivity(env, item, &item.inner().scoped_decl.value, &mut found_ground, trace);

    // let u = ScopedTerm::new_from_repr(ScopedTermRepr::USort);
    // check_inhabitance(env, item, &u, &item.get_type());
    check_inhabitance(env, item, &item.get_type(), &item.get_value(), &mut Vec::new());
  }
}

fn check_inhabitance(
  env: &ElabEnv,
  root_def: &CheckableDecl,
  type_: &ScopedTerm,
  value: &ScopedTerm,
  openers: &mut Vec<OpenerTerm>
) {
  match type_.get_repr() {
    t@(ScopedTermRepr::USort | ScopedTermRepr::Star) => {
      match value.get_repr() {
        ScopedTermRepr::Pi { binder:_, head, tail } |
        ScopedTermRepr::Sigma { binder:_, head, tail } => {
          // check that binder is valid
          check_inhabitance(env, root_def, type_, head, openers);
          check_inhabitance(env, root_def, type_, tail, openers);
        },
        ScopedTermRepr::Either(a, b) |
        ScopedTermRepr::Pair(a, b) |
        ScopedTermRepr::Arrow(a, b) => {
          check_inhabitance(env, root_def, type_, a, openers);
          check_inhabitance(env, root_def, type_, b, openers);
        },
        ScopedTermRepr::Star => {
          if let ScopedTermRepr::Star = t {
            root_def.inner().issues.push(ElabIssue::InvalidInhabitance);
          }
        },
        ScopedTermRepr::Void |
        ScopedTermRepr::Pt => (),

        ScopedTermRepr::GlobalRef(_) => todo!(),
        ScopedTermRepr::App(_, _) => todo!(),
        ScopedTermRepr::SubstRef(_) => todo!(),
        ScopedTermRepr::LetGroup(_, _) => todo!(),

        ScopedTermRepr::Lambda(_) |
        ScopedTermRepr::Inl(_) |
        ScopedTermRepr::Inr(_) |
        ScopedTermRepr::Null |
        ScopedTermRepr::LambdaHead(_, _) |
        ScopedTermRepr::Tuple(_, _) => {
          root_def.inner().issues.push(ElabIssue::InvalidInhabitance);
        },
        ScopedTermRepr::USort => unreachable!(),
      }
    },
    ScopedTermRepr::Arrow(head, tail) => {
      match value.get_repr() {
        ScopedTermRepr::Lambda(clauses) => {
          for clause in clauses {
            let mut copy = openers.clone();
            check_inhabitance(env, root_def, type_, clause, &mut copy);
          }
        },
        ScopedTermRepr::LambdaHead(decon_pat, rest) => {
          check_pi_tip(env, root_def, openers.last_mut().unwrap(), head, decon_pat);
          check_inhabitance(env, root_def, tail, rest, openers)
        }
        _ => {
          root_def.inner().issues.push(ElabIssue::InvalidInhabitance);
          return;
        }
      }
    }
    ScopedTermRepr::Pi { binder:_, head, tail } => {
      match value.get_repr() {
        ScopedTermRepr::Lambda(clauses) => {
          for clause in clauses {
            let mut copy = openers.clone();
            check_inhabitance(env, root_def, type_, clause, &mut copy);
          }
        },
        ScopedTermRepr::LambdaHead(decon_pat, rest) => {
          openers.push(OpenerTerm::Unrefined);
          check_pi_tip(env, root_def, openers.last_mut().unwrap(), head, decon_pat);
          check_inhabitance(env, root_def, tail, rest, openers)
        }
        _ => {
          root_def.inner().issues.push(ElabIssue::InvalidInhabitance);
          return;
        }
      }
    },
    ScopedTermRepr::Sigma { binder, head, tail } => {
      let ScopedTermRepr::Tuple(fst, snd) = value.get_repr() else {
        root_def.inner().issues.push(ElabIssue::InvalidInhabitance);
        return;
      };
      todo!()
    },
    ScopedTermRepr::Pair(_, _) => {
      let ScopedTermRepr::Tuple(_, _) = value.get_repr() else {
        root_def.inner().issues.push(ElabIssue::InvalidInhabitance);
        return;
      };
      todo!()
    },
    ScopedTermRepr::Either(l, r) => {
      match value.get_repr() {
        ScopedTermRepr::Inl(v) => {
          check_inhabitance(env, root_def, l, v, openers);
        },
        ScopedTermRepr::Inr(v) => {
          check_inhabitance(env, root_def, r, v, openers);
        },
        _ => {
          root_def.inner().issues.push(ElabIssue::InvalidInhabitance);
          return;
        }
      }
    },
    ScopedTermRepr::App(tar, args) => {
      let tar = tar.deep_lazy_clone();
      elim_app(env, root_def, &tar, args, openers);
      check_inhabitance(env, root_def, &tar, value, openers)
    },
    ScopedTermRepr::LetGroup(_, _) => todo!(),
    ScopedTermRepr::GlobalRef(_) => todo!(),
    ScopedTermRepr::SubstRef(_) => todo!(),

    ScopedTermRepr::Tuple(_, _) |
    ScopedTermRepr::Inl(_) |
    ScopedTermRepr::Inr(_) |
    ScopedTermRepr::Lambda(_) |
    ScopedTermRepr::LambdaHead(_, _) |
    ScopedTermRepr::Null => {
      root_def.inner().issues.push(ElabIssue::InvalidInhabitance);
    }
    ScopedTermRepr::Void => {
      let ScopedTermRepr::Null = value.get_repr() else {
        root_def.inner().issues.push(ElabIssue::InvalidInhabitance);
        return
      };
    }
    ScopedTermRepr::Pt => {
      let ScopedTermRepr::Pt = value.get_repr() else {
        root_def.inner().issues.push(ElabIssue::InvalidInhabitance);
        return
      };
    },
  }
}
#[derive(Debug, Clone)]
enum OpenerTerm {
  Unrefined,
  Inl(Box<Self>),
  Inr(Box<Self>),
  Tuple(Box<Self>, Box<Self>),
  Pt
}
fn elim_app(
  env: &ElabEnv,
  root_def: &CheckableDecl,
  head: &ScopedTerm,
  args: &Vec<ScopedTerm>,
  openers: &Vec<OpenerTerm>,
) {
  match head.get_repr() {
    ScopedTermRepr::App(a, b) => {
      elim_app(env, root_def, a, b, openers);
      elim_app(env, root_def, a, args, openers);
    },
    ScopedTermRepr::GlobalRef(_) => todo!(),
    ScopedTermRepr::SubstRef(_) => todo!(),
    ScopedTermRepr::LetGroup(_, _) => todo!(),
    ScopedTermRepr::LambdaHead(_, _) => todo!(),
    ScopedTermRepr::Lambda(cls) => {
      match elim_lambda(env, root_def, cls, args, openers) {
        Some(term) => {
          head.assign_from(&term);
        },
        None => panic!("failed to elim app"),
      }
    },
    ScopedTermRepr::Sigma { .. } |
    ScopedTermRepr::Pi { .. } |
    ScopedTermRepr::Either(_, _) |
    ScopedTermRepr::Pair(_, _) |
    ScopedTermRepr::Arrow(_, _) |
    ScopedTermRepr::Tuple(_, _) |
    ScopedTermRepr::Inl(_) |
    ScopedTermRepr::Inr(_) |
    ScopedTermRepr::Star |
    ScopedTermRepr::Void |
    ScopedTermRepr::Null |
    ScopedTermRepr::USort |
    ScopedTermRepr::Pt => unreachable!()
  }
}
#[must_use]
fn elim_global_ref(
  env: &ElabEnv,
  term: &ScopedTerm,
) -> i32 {
  let ScopedTermRepr::GlobalRef(ix) = term.get_repr() else {
    panic!()
  };
  let def = env.get_def(*ix);
  match def.inner().check_state {
    CheckState::Untouched => {
      -2
    },
    CheckState::Began => {
      -1
    },
    CheckState::Ok => {
      term.assign_from(&def.get_value());
      1
    },
    CheckState::Bad => {
      0
    },
  }
}

fn elim_lambda(
  env: &ElabEnv,
  root_def: &CheckableDecl,
  clauses: &Vec<ScopedTerm>,
  args: &Vec<ScopedTerm>,
  openers: &Vec<OpenerTerm>,
) -> Option<ScopedTerm> {
  let mut bind_items = Vec::new();
  for clause in clauses {
    let mut matched = true;
    match try_match(env, root_def, clause, args, &mut bind_items, openers, &mut matched) {
      v@Some(_) => {
        return v;
      },
      None => {
        bind_items.clear();
        continue
      },
    }
  }
  return None;
}

fn try_match(
  env: &ElabEnv,
  root_def: &CheckableDecl,
  clause: &ScopedTerm,
  args: &[ScopedTerm],
  bound_values: &mut Vec<ScopedTerm>,
  openers: &Vec<OpenerTerm>,
  matched: &mut bool
) -> Option<ScopedTerm> {
  match clause.get_repr() {
    ScopedTermRepr::LambdaHead(pattern, tail) => {
      try_deconstruct(env, root_def, pattern, &args[0], bound_values, openers, matched);
      if !*matched { return None }
      return try_match(env, root_def, tail, &args[1..], bound_values, openers, matched);
    },
    _ => {
      let res = clause.deep_lazy_clone();
      bind(&res, &bound_values);
      return Some(res);
    }
  }
}
fn bind(
  term: &ScopedTerm,
  bound: &Vec<ScopedTerm>
) {
  match term.get_repr() {
    ScopedTermRepr::App(head, args) => {
      bind(head, bound);
      for arg in args {
        bind(arg, bound)
      }
    },
    ScopedTermRepr::GlobalRef(_) => (),
    ScopedTermRepr::SubstRef(ix) => {
      let bound_value = &bound[ix.get_index()];
      term.assign_from(bound_value)
    },
    ScopedTermRepr::Pi { binder:_, head, tail } |
    ScopedTermRepr::Sigma { binder:_, head, tail } => {
      bind(head, bound);
      bind(tail, bound);
    },
    ScopedTermRepr::Tuple(a, b) |
    ScopedTermRepr::Arrow(a, b) |
    ScopedTermRepr::Pair(a, b) |
    ScopedTermRepr::Either(a, b) => {
      bind(a, bound);
      bind(b, bound);
    },
    ScopedTermRepr::Inl(a) |
    ScopedTermRepr::Inr(a) => {
      bind(a, bound)
    },
    ScopedTermRepr::LetGroup(_, _) => todo!(),
    ScopedTermRepr::LambdaHead(_, t) => {
      bind(t, bound);
    },
    ScopedTermRepr::Lambda(clauses) => {
      for clause in clauses {
        bind(clause, bound)
      }
    },
    ScopedTermRepr::Star |
    ScopedTermRepr::Void |
    ScopedTermRepr::Null |
    ScopedTermRepr::USort |
    ScopedTermRepr::Pt => (),
  }
}
fn opener_to_term(
  opener: &OpenerTerm
) -> ScopedTerm {
  match opener {
    OpenerTerm::Unrefined => {
      ScopedTerm::new_from_repr(ScopedTermRepr::Null)
    },
    OpenerTerm::Inl(v) => {
      ScopedTerm::new_from_repr(ScopedTermRepr::Inl(opener_to_term(v)))
    },
    OpenerTerm::Inr(v) => {
      ScopedTerm::new_from_repr(ScopedTermRepr::Inr(opener_to_term(v)))
    },
    OpenerTerm::Tuple(a, b) => {
      let a = opener_to_term(a);
      let b = opener_to_term(b);
      ScopedTerm::new_from_repr(ScopedTermRepr::Tuple(a, b))
    },
    OpenerTerm::Pt => {
      ScopedTerm::new_from_repr(ScopedTermRepr::Pt)
    },
  }
}
fn try_deconstruct(
  env: &ElabEnv,
  root_def: &CheckableDecl,
  pattern: &ThinPExpr,
  term: &ScopedTerm,
  items: &mut Vec<ScopedTerm>,
  openers: &Vec<OpenerTerm>,
  matched: &mut bool
) {
  match (pattern, term.get_repr()) {
    (_, ScopedTermRepr::App(head, args)) => {
      // rewrite app
      elim_app(env, root_def, head, args, openers)
    },
    (_, ScopedTermRepr::GlobalRef(_)) => {
      // pull this in
      todo!()
    },
    (_, ScopedTermRepr::SubstRef(ix)) => {
      // pull from substs
      let opener = &openers[ix.get_index()];
      let t = opener_to_term(opener);
      try_deconstruct(env, root_def, pattern, &t, items, openers, matched)
    },
    (_, ScopedTermRepr::LetGroup(_, _)) => {
      // produce value
      todo!()
    },
    (ThinPExpr::Discard, _) => {
      ()
    },
    (ThinPExpr::Binder(i), _) => {
      assert!(i.get_index() == items.len());
      items.push(term.shallow_clone());
    },
    (ThinPExpr::Group(_, _), ScopedTermRepr::Pi { .. }) |
    (ThinPExpr::Group(_, _), ScopedTermRepr::Sigma { .. }) => {
      *matched = false;
    },
    (ThinPExpr::Group(_, _), ScopedTermRepr::Either(_, _)) |
    (ThinPExpr::Group(_, _), ScopedTermRepr::Pair(_, _)) |
    (ThinPExpr::Group(_, _), ScopedTermRepr::Void) |
    (ThinPExpr::Group(_, _), ScopedTermRepr::Arrow(_, _)) => {
      *matched = false;
    },
    (ThinPExpr::Group(atom, rest), ScopedTermRepr::Tuple(fst, snd)) => {
      match atom {
        Atom::TupleCtor => {
          try_deconstruct(env, root_def, &rest[0], fst, items, openers, matched);
          if !*matched { return };
          try_deconstruct(env, root_def, &rest[1], snd, items, openers, matched);
        },
        _ => {
          *matched = false;
        }
      }
    },
    (ThinPExpr::Pt, a) => {
      match a {
        ScopedTermRepr::Pt => (),
        _ => {
          *matched = false;
        }
      }
    },
    (ThinPExpr::Group(atom, val), ScopedTermRepr::Inl(v)) => {
      match atom {
        Atom::Inl => {
          try_deconstruct(env, root_def, &val[0], v, items, openers, matched);
        },
        _ => {
          *matched = false;
        }
      }
    },
    (ThinPExpr::Group(atom, val), ScopedTermRepr::Inr(v)) => {
      match atom {
        Atom::Inr => {
          try_deconstruct(env, root_def, &val[0], v, items, openers, matched);
        },
        _ => {
          *matched = false;
        }
      }
    },
    (ThinPExpr::Group(_, _), ScopedTermRepr::Lambda(_)) |
    (ThinPExpr::Group(_, _), ScopedTermRepr::Star) |
    (ThinPExpr::Group(_, _), ScopedTermRepr::Null) |
    (ThinPExpr::Group(_, _), ScopedTermRepr::USort) |
    (ThinPExpr::Group(_, _), ScopedTermRepr::Pt) |
    (ThinPExpr::Group(_, _), ScopedTermRepr::LambdaHead(_, _)) => {
      *matched = false;
    },
  }
}

fn check_pi_tip(
  env: &ElabEnv,
  root_def: &CheckableDecl,
  opener: &mut OpenerTerm,
  head: &ScopedTerm,
  pattern: &ThinPExpr,
) {
  match head.get_repr() {
    ScopedTermRepr::Sigma { binder, head, tail } => todo!(),
    ScopedTermRepr::Pi { binder, head, tail } => todo!(),
    ScopedTermRepr::Either(l, r) => {
      match pattern {
        ThinPExpr::Discard => (),
        ThinPExpr::Binder(_) => (),
        ThinPExpr::Group(atom, rest) => {
          match atom {
            Atom::Inl => {
              let mut local_opener = OpenerTerm::Unrefined;
              check_pi_tip(env, root_def, &mut local_opener, l, &rest[0]);
              *opener = OpenerTerm::Inl(Box::new(local_opener));
            },
            Atom::Inr => {
              let mut local_opener = OpenerTerm::Unrefined;
              check_pi_tip(env, root_def, &mut local_opener, r, &rest[0]);
              *opener = OpenerTerm::Inr(Box::new(local_opener));
            },
            _ => {
              root_def.inner().issues.push(ElabIssue::InvalidBinder);
              return;
            }
          }
        },
        ThinPExpr::Pt => {
          root_def.inner().issues.push(ElabIssue::InvalidBinder);
          return;
        },
      }
    },
    ScopedTermRepr::Pair(l, r) => {
      match pattern {
        ThinPExpr::Discard => (),
        ThinPExpr::Binder(_) => (),
        ThinPExpr::Group(atom, rest) => {
          match atom {
            Atom::TupleCtor => {
              let mut local_opener_l = OpenerTerm::Unrefined;
              check_pi_tip(env, root_def, &mut local_opener_l, l, &rest[0]);
              let mut local_opener_r = OpenerTerm::Unrefined;
              check_pi_tip(env, root_def, &mut local_opener_r, r, &rest[1]);
              *opener = OpenerTerm::Tuple(Box::new(local_opener_l), Box::new(local_opener_r));
            }
            _ => {
              root_def.inner().issues.push(ElabIssue::InvalidBinder);
              return;
            }
          }
        },
        ThinPExpr::Pt => {
          root_def.inner().issues.push(ElabIssue::InvalidBinder);
          return;
        },
      }
    },
    ScopedTermRepr::Arrow(_, _) => {
      match pattern {
        ThinPExpr::Discard => (),
        ThinPExpr::Binder(_) => (),
        _ => {
          root_def.inner().issues.push(ElabIssue::InvalidBinder);
          return;
        }
      }
    },
    ScopedTermRepr::Star => {
      match pattern {
        ThinPExpr::Discard => (),
        ThinPExpr::Binder(_) => (),
        _ => {
          root_def.inner().issues.push(ElabIssue::InvalidBinder);
          return;
        }
      }
    },
    ScopedTermRepr::Void => {
      root_def.inner().issues.push(ElabIssue::InvalidBinder);
      return;
    },
    ScopedTermRepr::Pt => {
      match pattern {
        ThinPExpr::Discard |
        ThinPExpr::Binder(_) |
        ThinPExpr::Pt => {
          *opener = OpenerTerm::Pt;
        },
        _ => {
          root_def.inner().issues.push(ElabIssue::InvalidBinder);
          return;
        }
      }
    },

    ScopedTermRepr::App(_, _) => todo!(),
    ScopedTermRepr::GlobalRef(_) => todo!(),
    ScopedTermRepr::SubstRef(_) => todo!(),
    ScopedTermRepr::LetGroup(_, _) => todo!(),

    ScopedTermRepr::Tuple(_, _) => todo!(),
    ScopedTermRepr::Inl(_) => todo!(),
    ScopedTermRepr::Inr(_) => todo!(),
    ScopedTermRepr::Lambda(_) => todo!(),
    ScopedTermRepr::USort => unreachable!(),
    ScopedTermRepr::Null => {
      root_def.inner().issues.push(ElabIssue::InvalidBinder);
      return;
    },
    ScopedTermRepr::LambdaHead(_, _) => todo!(),
  }
}

#[test]
fn build_env() {
  let mut text =
    "a : (m: () or ()) -> { inl () => Void, inr () => () } m = { inl () => !, inr () => () }".to_string() +
    ""
  ;
  pad_string(&mut text);
  let mut parser = SourceTextParser::new(text.as_bytes());
  let raw_decls = match parser.parse_to_end() {
    Ok(raw_decls) => raw_decls,
    Err(err) => panic!("{:?}", err),
  };
  let mut scoped_checker = ScopeCheckCtx::new(text.as_bytes());
  let scoped = match scope_check_decls(&mut scoped_checker, &raw_decls) {
    Ok(scoped) => scoped,
    Err(err) => panic!("{:?}", err),
  };
  let elab_env = ElabEnv::new_from_scoped_defs(scoped);
  elab(&elab_env);
  println!("{:#?}", elab_env);

}

