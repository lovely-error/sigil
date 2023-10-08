use std::{collections::{HashSet, HashMap}, any::Any, cell::UnsafeCell, hash::Hash};

use crate::{
  parser::{PrecedenceResolvedTExpr, AtomRef, RefinedPExpr, resolve_precendece, LiftKind, PrecedenceResolutionError},
  lexer::{CharsData, RawDecl, SourceTextParser}, utils::SomeDebug
};

#[derive(Debug)]
pub struct ScopedDecl(u32, ScopedTExpr, ScopedTExpr);

pub struct DeclCheckCtx<'i> {
  chars: &'i [u8],
  encountered_names: HashMap<&'i str, u32>,
  errors: Vec<SemanticError>,
}
impl <'i> DeclCheckCtx<'i> {
  pub fn new(names: &'i [u8]) -> Self {
    Self { chars: names, encountered_names: HashMap::new(), errors: Vec::new() }
  }
  pub fn get_errors_if_any(&self) -> Option<Vec<SemanticError>> {
    if self.errors.is_empty() { return None ;}
    Some(self.errors.clone())
  }
}
pub fn check_decls(ctx: &mut DeclCheckCtx, decls: &Vec<RawDecl>) -> Vec<ScopedDecl> {
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
              ctx.errors.push(SemanticError::PrecedenceError(err1));
              ctx.errors.push(SemanticError::PrecedenceError(err2))
            },
            (Err(err), _) | (_, Err(err)) => {
              ctx.errors.push(SemanticError::PrecedenceError(err))
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
pub enum ScopedTExpr {
  App(Box<Self>, Vec<Self>),
  GlobalRef(u32),
  SubstRef(u32),
  AtomRef(AtomRef),
  Lift(LiftKind,RefinedPExpr, Box<Self>, Box<Self>),
  Star,
  Let(Vec<(RefinedPExpr, Self)>, Box<Self>),
  Lambda(Vec<(Vec<RefinedPExpr>, Self)>),
  Pt,
  Void,
}

#[derive(Debug, Clone)]
pub enum SemanticError {
  InvalidAppHead,
  ReservedName,
  DuplicateName,
  IncorrectArgNum,
  InvalidRef(String),
  PrecedenceError(PrecedenceResolutionError),
}
pub struct SemaCheckCtx<'i> {
  aggregated_errors: Vec<SemanticError>,
  encountered_names: &'i HashMap<&'i str, u32>,
  chars: &'i [u8],
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
        ctx.aggregated_errors.push(SemanticError::InvalidRef(ident.to_string()));
        return None
      }
    },
    PrecedenceResolvedTExpr::AtomRef(atom) => return Some(ScopedTExpr::AtomRef(*atom)),
    PrecedenceResolvedTExpr::Lift(k, bind, head, spine) => {
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
          return Some(ScopedTExpr::Lift(*k,bind.clone(), Box::new(head), Box::new(spine)))
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
      for (pexpr, _, _) in items {
        collect_binders(&mut cbctx, pexpr);
      }
      let mut items_ = Vec::new();
      for (pexpr, _, expr) in items {
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

pub fn get_name<'i, 'k>(str: &'i [u8], chars: &'k CharsData) -> &'i str {
  unsafe {
    let slice = std::slice::from_raw_parts(
      str.as_ptr().add(chars.offset_from_start as usize),
      chars.offset_from_head as usize);
    std::str::from_utf8_unchecked(slice)
  }
}

struct CollectBinderCtx<'i> {
  str: &'i [u8],
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
  let mut parser = SourceTextParser::new(s.as_bytes());
  let expr = parser.parse_to_end();
  match expr {
    Err(err) => println!("{:?}", err),
    Ok(raw_decls) => {
      println!("{:#?}", raw_decls);
      let mut ctx = DeclCheckCtx::new(s.as_bytes());
      let decls = check_decls(&mut ctx, &raw_decls);
      if !ctx.errors.is_empty() {
        println!("{:#?}", ctx.errors)
      }
      println!("{:#?}", decls)
    }
  }
}
