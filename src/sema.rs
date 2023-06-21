use std::{collections::{HashSet, HashMap}, any::Any, cell::UnsafeCell, hash::Hash};

use crate::{
  parser::{PrecedenceResolvedTExpr, AtomRef, RefinedPExpr, resolve_precendece},
  lexer::{CharsData, RawDecl, SourceTextParser}, utils::SomeDebug
};

#[derive(Debug)]
struct ScopedDecl(u32, ScopedTExpr, ScopedTExpr);

struct DeclCheckCtx<'i> {
  chars: &'i String,
  encountered_names: HashMap<&'i str, u32>,
  errors: Vec<SemanticError>,
}
impl <'i> DeclCheckCtx<'i> {
  fn new(names: &'i String) -> Self {
    Self { chars: names, encountered_names: HashMap::new(), errors: Vec::new() }
  }
}
fn check_decls(ctx: &mut DeclCheckCtx, decls: &Vec<RawDecl>) -> Vec<ScopedDecl> {
  let str = |&CharsData { offset_from_start, offset_from_head }| unsafe {
    std::str::from_utf8(std::slice::from_raw_parts(
      ctx.chars.as_ptr().add(offset_from_start as usize), offset_from_head as usize))
      .unwrap()
  };
  let mut res_decls = Vec::new();
  let end_index = decls.len();
  let mut ix = 0;
  while ix != end_index {
    let RawDecl(name_chars, texpr, oexpr) = unsafe { decls.get_unchecked(ix) };
    let name = str(name_chars);
    match name {
      "inl" | "inr" | "and" | "or" => {
        ctx.errors.push(SemanticError::ReservedName);
      }
      name => {
        let outcome = ctx.encountered_names.insert(name, ix as u32);
        if outcome.is_some() { ctx.errors.push(SemanticError::DuplicateName) }
        else {
          let rtexpr = resolve_precendece(ctx.chars,texpr);
          let roexpr = resolve_precendece(ctx.chars, oexpr);
          match (rtexpr, roexpr) {
            (Ok(rtexpr), Ok(roexpr)) => {
              let mut ctx_ = SemaCheckCtx {
                aggregated_errors: Vec::new(),
                encountered_names: &ctx.encountered_names, chars: ctx.chars };
              let rtexpr = check_scope(&mut ctx_, &rtexpr, None);
              let roexpr = check_scope(&mut ctx_, &roexpr, None);
              match (rtexpr, roexpr) {
                (Some(rtexpr), Some(roexpr)) => {
                  res_decls.push(ScopedDecl(ix as u32, rtexpr, roexpr));
                },
                _ => {
                  ctx.errors.append(&mut ctx_.aggregated_errors)
                }
              }
            },
            (Err(err1), Err(err2)) => {
              ctx.errors.push(SemanticError::SomeError(err1));
              ctx.errors.push(SemanticError::SomeError(err2))
            },
            (Err(err), _) | (_, Err(err)) => {
              ctx.errors.push(SemanticError::SomeError(err))
            },
          }
        }
      }
    }
    ix += 1;
  }
  return res_decls
}

#[derive(Debug)]
enum ScopedTExpr {
  App(Box<Self>, Vec<Self>),
  GlobalRef(u32),
  SubstRef(u32),
  AtomRef(AtomRef),
  Arrow(Box<Self>, Box<Self>),
  DArrow(RefinedPExpr, Box<Self>, Box<Self>),
  And(Box<Self>, Box<Self>),
  DAnd(RefinedPExpr, Box<Self>, Box<Self>),
  Or(Box<Self>, Box<Self>),
  Star,
  Let(Vec<(RefinedPExpr, Self)>, Box<Self>),
  Lambda(Vec<(Vec<RefinedPExpr>, Self)>),
  Tilda(Box<Self>, Box<Self>),
  Pt,
  Void,
  Inl(Box<Self>),
  Inr(Box<Self>),
  Tuple(Box<Self>, Box<Self>)
}

#[derive(Debug)]
enum SemanticError {
  InvalidAppHead, ReservedName, DuplicateName,
  IncorrectArgNum, InvalidRef,
  SomeError(Box<dyn Any>)
}
struct SemaCheckCtx<'i> {
  aggregated_errors: Vec<SemanticError>,
  encountered_names: &'i HashMap<&'i str, u32>,
  chars: &'i String,
}

type Maybe<T> = Option<T>;
fn check_scope(
  ctx: &mut SemaCheckCtx ,
  obj: &PrecedenceResolvedTExpr,
  binders_vars: Option<&HashMap<&str, u32>>
) -> Maybe<ScopedTExpr> {
  match obj {
    PrecedenceResolvedTExpr::App(head, args) => {
      let head = check_scope(ctx, head, binders_vars);
      let mut failed = head.is_none();
      let mut args_ = Vec::new();
      for arg in args {
        let arg = check_scope(ctx, arg, binders_vars);
        match arg {
          Some(arg) => {
            args_.push(arg)
          },
          None => failed = true,
        }
      }
      if failed { return None }
      let head = head.unwrap();
      return Some(ScopedTExpr::App(Box::new(head), args_));
    },
    PrecedenceResolvedTExpr::Tuple(l, r) => {
      let l = check_scope(ctx, l, binders_vars);
      let r = check_scope(ctx, r, binders_vars);
      match (l, r) {
        (Some(l), Some(r)) => {
          return Some(ScopedTExpr::Tuple(Box::new(l), Box::new(r)))
        },
        _ => return None
      }
    }
    PrecedenceResolvedTExpr::Arrow(l, r) => {
      let l = check_scope(ctx, l, binders_vars);
      let r = check_scope(ctx, r, binders_vars);
      match (l, r) {
        (Some(l), Some(r)) => {
          return Some(ScopedTExpr::Arrow(Box::new(l), Box::new(r)))
        },
        _ => return None
      }
    }
    PrecedenceResolvedTExpr::And(l, r) => {
      let l = check_scope(ctx, l, binders_vars);
      let r = check_scope(ctx, r, binders_vars);
      match (l, r) {
        (Some(l), Some(r)) => {
          return Some(ScopedTExpr::And(Box::new(l), Box::new(r)))
        },
        _ => return None
      }
    }
    PrecedenceResolvedTExpr::Or(l, r) => {
      let l = check_scope(ctx, l, binders_vars);
      let r = check_scope(ctx, r, binders_vars);
      match (l, r) {
        (Some(l), Some(r)) => {
          return Some(ScopedTExpr::Or(Box::new(l), Box::new(r)))
        },
        _ => return None
      }
    }
    PrecedenceResolvedTExpr::Tilda(l, r) => {
      let l = check_scope(ctx, l, binders_vars);
      let r = check_scope(ctx, r, binders_vars);
      match (l, r) {
        (Some(l), Some(r)) => {
          return Some(ScopedTExpr::Tilda(Box::new(l), Box::new(r)))
        },
        _ => return None
      }
    },
    PrecedenceResolvedTExpr::Ref(chars) => {
      let ident = get_name(ctx.chars, chars);
      if let Some(bctx) = binders_vars {
        if let Some(ix) = bctx.get(ident) {
          return Some(ScopedTExpr::SubstRef(*ix));
        }
      }
      if let Some(ix) = ctx.encountered_names.get(ident) {
        return Some(ScopedTExpr::GlobalRef(*ix))
      } else {
        ctx.aggregated_errors.push(SemanticError::InvalidRef);
        return None
      }
    },
    PrecedenceResolvedTExpr::AtomRef(atom) => return Some(ScopedTExpr::AtomRef(*atom)),
    PrecedenceResolvedTExpr::DArrow(bind, head, spine) => {
      let chk_head = check_scope(ctx, head, binders_vars);
      let binders_store = if let Some(bin_store) = binders_vars {
        bin_store.clone()
      } else { HashMap::new() };
      let mut cbctx = CollectBinderCtx {
        binders: binders_store,
        errors: Vec::new(), str: ctx.chars, index: 0 };
      collect_binders(&mut cbctx, bind);
      let chk_spine = check_scope(ctx, spine, Some(&cbctx.binders));
      if !cbctx.errors.is_empty() {
        ctx.aggregated_errors.append(&mut cbctx.errors);
      }
      match (chk_head, chk_spine) {
        (Some(head), Some(spine)) => {
          return Some(ScopedTExpr::DArrow(bind.clone(), Box::new(head), Box::new(spine)))
        },
        _ => return None
      }
    },
    PrecedenceResolvedTExpr::DAnd(bind, head, spine) => {
      let chk_head = check_scope(ctx, head, binders_vars);
      let binders_store = if let Some(bin_store) = binders_vars {
        bin_store.clone()
      } else { HashMap::new() };
      let mut cbctx = CollectBinderCtx {
        binders: binders_store,
        errors: Vec::new(), str: ctx.chars, index: 0 };
      collect_binders(&mut cbctx, bind);
      let chk_spine = check_scope(ctx, spine, Some(&cbctx.binders));
      if !cbctx.errors.is_empty() {
        ctx.aggregated_errors.append(&mut cbctx.errors);
      }
      match (chk_head, chk_spine) {
        (Some(head), Some(spine)) => {
          return Some(ScopedTExpr::DAnd(bind.clone(), Box::new(head), Box::new(spine)))
        },
        _ => return None
      }
    },
    PrecedenceResolvedTExpr::Star => return Some(ScopedTExpr::Star),
    PrecedenceResolvedTExpr::Let(items, tail) => {
      let binders_store = if let Some(bin_store) = binders_vars {
        bin_store.clone()
      } else { HashMap::new() };
      let mut cbctx = CollectBinderCtx {
        binders: binders_store, errors: Vec::new(), str: ctx.chars, index: 0 };
      for (pexpr, _) in items {
        collect_binders(&mut cbctx, pexpr);
      }
      let mut items_ = Vec::new();
      for (pexpr, expr) in items {
        if let Some(expr) =  check_scope(ctx, expr, Some(&cbctx.binders)) {
          items_.push((pexpr.clone(),expr))
        }
      }
      if !cbctx.errors.is_empty() {
        ctx.aggregated_errors.append(&mut cbctx.errors);
      }
      if let Some(tail) = check_scope(ctx, tail, Some(&cbctx.binders)) {
        return Some(ScopedTExpr::Let(items_, Box::new(tail)))
      }
      return None
    },
    PrecedenceResolvedTExpr::Lambda(clauses) => {
      let mut checked_clauses = Vec::new();
      for (patterns, rhs) in clauses {
        let binders_store = if let Some(bin_store) = binders_vars {
          bin_store.clone()
        } else { HashMap::new() };
        let mut cbctx = CollectBinderCtx {
          binders: binders_store, errors: Vec::new(), str: ctx.chars, index: 0 };
        for pattern in patterns {
          collect_binders(&mut cbctx, pattern);
        }
        if let Some(rhs) = check_scope(ctx, rhs, Some(&cbctx.binders)) {
          checked_clauses.push((patterns.clone(), rhs))
        }
        if !cbctx.errors.is_empty() {
          ctx.aggregated_errors.append(&mut cbctx.errors)
        }
      }
      if !ctx.aggregated_errors.is_empty() { return None }
      return Some(ScopedTExpr::Lambda(checked_clauses));
    },
    PrecedenceResolvedTExpr::Pt => return Some(ScopedTExpr::Pt),
    PrecedenceResolvedTExpr::Void => return Some(ScopedTExpr::Void),
    PrecedenceResolvedTExpr::Inl(t) => {
      let t = check_scope(ctx, t, binders_vars)?;
      return Some(ScopedTExpr::Inl(Box::new(t)))
    },
    PrecedenceResolvedTExpr::Inr(t) => {
      let t = check_scope(ctx, t, binders_vars)?;
      return Some(ScopedTExpr::Inr(Box::new(t)))
    },
  }
}

fn check_clauses(
  ctx: &mut SemaCheckCtx,
  clauses: &Vec<(Vec<RefinedPExpr>, PrecedenceResolvedTExpr)>
) -> Maybe<ScopedTExpr> {
  todo!()
}

fn check_clause(
  ctx: &mut SemaCheckCtx,
  clause: &(Vec<RefinedPExpr>, PrecedenceResolvedTExpr)
) {

}

pub fn get_name<'i, 'k>(str: &'i String, chars: &'k CharsData) -> &'i str {
  unsafe {
    let slice = std::slice::from_raw_parts(
      str.as_ptr().add(chars.offset_from_start as usize),
      chars.offset_from_head as usize);
    std::str::from_utf8_unchecked(slice)
  }
}

fn get_arity(
  ctx: &mut SemaCheckCtx,
  expr: &PrecedenceResolvedTExpr
) -> Maybe<usize> {
  match expr {
    PrecedenceResolvedTExpr::AtomRef(atom) => {
      match atom {
        AtomRef::And | AtomRef::Arrow | AtomRef::Or | AtomRef::Tilda |
        AtomRef::TupleCtor => {
          return Some(2)
        }
        AtomRef::Inl | AtomRef::Inr=> return Some(1),
      }
    },
    PrecedenceResolvedTExpr::App(head, args) => {
      let head_arity = get_arity(ctx, head)?;
      let arg_count = args.len();
      if arg_count > head_arity {
        ctx.aggregated_errors.push(SemanticError::IncorrectArgNum);
        return None
      }
      return Some(head_arity - arg_count)
    }
    PrecedenceResolvedTExpr::Lambda(_) => {
      todo!()
    }
    PrecedenceResolvedTExpr::Ref(_) => {
      todo!()
    }
    _ => ()
  }
  let mut obj = expr;
  let mut count = 0;
  while let
    PrecedenceResolvedTExpr::Arrow(_, tail) |
    PrecedenceResolvedTExpr::DArrow(_, _, tail) = obj {
    count += 1;
    obj = tail;
  }
  return Some(count)
}

struct CollectBinderCtx<'i> {
  str: &'i String,
  errors: Vec<SemanticError>,
  binders: HashMap<&'i str, u32>,
  index: u32,
}
fn fresh_ident(ctx: &mut CollectBinderCtx) -> u32 {
  ctx.index += 1;
  return ctx.index
}
fn collect_binders(
  ctx: &mut CollectBinderCtx, pexpr: &RefinedPExpr
) {
  match pexpr {
    RefinedPExpr::Pt |
    RefinedPExpr::AtomRef(_) |
    RefinedPExpr::Discard => (),
    RefinedPExpr::Ref(chars) => {
      let ident = get_name(ctx.str, chars);
      let ix = fresh_ident(ctx);
      let outcome = ctx.binders.insert(ident, ix);
      if outcome.is_some() {
        ctx.errors.push(SemanticError::DuplicateName)
      }
    },
    RefinedPExpr::Tuple(l, r) |
    RefinedPExpr::Arrow(l, r) |
    RefinedPExpr::Tilda(l, r) |
    RefinedPExpr::Or(l, r) |
    RefinedPExpr::And(l, r) => {
      collect_binders(ctx, l);
      collect_binders(ctx, r)
    },
    RefinedPExpr::Inr(t) |
    RefinedPExpr::Inl(t) => collect_binders(ctx, t),
    RefinedPExpr::Group(_, subpats) => {
      for subpat in subpats {
        collect_binders(ctx, subpat)
      }
    },
  }
}

#[test]
fn delc_cheking() {
  let s =
    "".to_string() +
    "k : () -> ! = { () => (i: ()) and k i }\n" +
    "d : () -> ! = { () => (i: ()) and k i }"
    ;
  let mut parser = SourceTextParser::new(&s);
  let expr = parser.parse_to_end();
  match expr {
    Err(err) => println!("{:?}", err),
    Ok(raw_decls) => {
      println!("{:#?}", raw_decls);
      let mut ctx = DeclCheckCtx::new(&parser.chars);
      let decls = check_decls(&mut ctx, &raw_decls);
      if !ctx.errors.is_empty() {
        println!("{:#?}", ctx.errors)
      }
      println!("{:#?}", decls)
    }
  }
}
