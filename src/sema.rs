use core::{fmt::{Debug, Display, Write}, hash::Hash};
use std::{alloc::{alloc, Layout}, cell::UnsafeCell, collections::{HashMap, HashSet, VecDeque}, mem::forget, ptr::{addr_of, addr_of_mut, copy_nonoverlapping, NonNull}, rc::Rc};

use crate::{
  parser::{PrecedenceResolvedTExpr, Atom, RefinedPExpr, resolve_precendece, PrecedenceResolutionFailure},
  lexer::{CharsData, RawDecl, SourceTextParser, ParseFailure, pad_string}
};

#[derive(Debug, Clone)]
pub enum GenericError {
  SemanticError(SemanticError),
  PrecedenceError(PrecedenceResolutionFailure),
  ParseFailure(ParseFailure),
  String(String)
}

#[derive(Debug)]
pub struct ScopedDecl{
  pub index: DefId,
  pub name: String,
  pub type_: ScopedTerm,
  pub value: ScopedTerm
}

pub struct ScopeCheckCtx<'i> {
  chars: &'i [u8],
  encountered_names: HashMap<&'i str, u32>,
  errors: Vec<GenericError>,
}
impl <'i> ScopeCheckCtx<'i> {
  pub fn new(names: &'i [u8]) -> Self {
    Self { chars: names, encountered_names: HashMap::new(), errors: Vec::new() }
  }
}
pub fn scope_check_decls(
  ctx: &mut ScopeCheckCtx,
  decls: &Vec<RawDecl>
) -> Result<Vec<ScopedDecl>, Vec<GenericError>> {
  let str = |&CharsData { off1:offset_from_start, off2: offset_from_head }| unsafe {
    std::str::from_utf8(std::slice::from_raw_parts(
      ctx.chars.as_ptr().add(offset_from_start as usize), offset_from_head as usize))
      .unwrap()
  };
  let mut ix = 0;
  for decl in decls {
    let name = str(&decl.0);
    let outcome = ctx.encountered_names.insert(name, ix as u32);
    if outcome.is_some() {
      ctx.errors.push(GenericError::SemanticError(
        SemanticError::DuplicateName(name.to_string())))
    }
  }
  if !ctx.errors.is_empty() {
    return Err(ctx.errors.clone());
  }
  let mut res_decls = Vec::new();
  let end_index = decls.len();
  ix = 0;
  while ix != end_index {
    let RawDecl(name_chars, texpr, oexpr) = unsafe { decls.get_unchecked(ix) };
    let name = str(name_chars);
    match name {
      "inl" | "inr" | "and" | "or" | "Void" => {
        ctx.errors.push(GenericError::SemanticError(SemanticError::ReservedName));
      }
      name => {
        let rtexpr = resolve_precendece(ctx.chars,texpr);
        let roexpr = resolve_precendece(ctx.chars, oexpr);
        match (rtexpr, roexpr) {
          (Ok(rtexpr), Ok(roexpr)) => {
            let mut ctx_ = SemaCheckCtx {
              aggregated_errors: Vec::new(),
              encountered_names: &ctx.encountered_names, chars: ctx.chars };
            let mut binder_ctx = CollectBinderCtx {
              binders: HashMap::new(),
              errors: Vec::new(), str: ctx.chars, index: 0 };
            let rtexpr = check_scope(&mut ctx_, &rtexpr, &mut binder_ctx);
            binder_ctx.binders.clear();
            let roexpr = check_scope(&mut ctx_, &roexpr, &mut binder_ctx);
            match (rtexpr, roexpr) {
              (Some(rtexpr), Some(roexpr)) => {
                let decl = ScopedDecl {
                  index: DefId(ix as u32),
                  name: name.to_string(),
                  type_: rtexpr,
                  value: roexpr,
              };
                res_decls.push(decl);
              },
              _ => {
                ctx.errors.append(&mut ctx_.aggregated_errors)
              }
            }
          },
          (Err(err1), Err(err2)) => {
            ctx.errors.push(GenericError::PrecedenceError(err1));
            ctx.errors.push(GenericError::PrecedenceError(err2))
          },
          (Err(err), _) | (_, Err(err)) => {
            ctx.errors.push(GenericError::PrecedenceError(err))
          },
        }
      }
    }
    ix += 1;
  }
  if !ctx.errors.is_empty() {
    return Err(ctx.errors.clone());
  }
  return Ok(res_decls)
}

#[derive(Debug,Clone, Copy, PartialEq, Eq)]
pub struct DefId(u32);
impl DefId {
  pub fn get_def_index(&self) -> usize { self.0 as _ }
}
impl Hash for DefId {
  fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
    self.0.hash(state);
  }
}

#[derive(Debug)]
pub struct RcBox<T>(NonNull<RcBoxInner<T>>);
#[repr(C)]
struct RcBoxInner<T> {
  ref_count: usize,
  data: T
}
impl<T> RcBox<T> {
  pub fn new(value:T) -> Self { unsafe {
    let mem = alloc(Layout::new::<RcBoxInner<T>>()).cast::<RcBoxInner<T>>();
    (*mem).ref_count = 1;
    addr_of_mut!((*mem).data).write(value);
    return Self(NonNull::new_unchecked(mem));
  } }
  pub fn shallow_copy(&self) -> Self { unsafe {
    (*self.0.as_ptr()).ref_count += 1;
    return Self(self.0);
  } }
  pub fn get_mut(&self) -> &mut T {
    unsafe{&mut (*self.0.as_ptr()).data}
  }
  pub fn get_ref(&self) -> &T {
    unsafe{&(*self.0.as_ptr()).data}
  }
  fn release_reference(&self) { unsafe {
    let inner_alloc = self.0.as_ptr();
    let inner = &mut *inner_alloc;
    inner.ref_count -= 1;
    if inner.ref_count == 0 {
      addr_of_mut!(inner.data).drop_in_place();
      std::alloc::dealloc(inner_alloc.cast(), Layout::new::<RcBoxInner<T>>());
    }
  } }
  fn drop_box(&self) { unsafe {
    let inner_alloc = self.0.as_ptr();
    std::alloc::dealloc(inner_alloc.cast(), Layout::new::<RcBoxInner<T>>());
  } }
}
impl <T:Clone> RcBox<T> {
  pub fn deep_copy(&self) -> Self { unsafe {
    let cloned_data = (*self.0.as_ptr()).data.clone();
    Self::new(cloned_data)
  } }
}
impl<T> Drop for RcBox<T> {
  fn drop(&mut self) {
    self.release_reference()
  }
}

pub struct ScopedTerm(UnsafeCell<ScopedTermInner>);
struct ScopedTermInner {
  repr: RcBox<ScopedTermRepr>,
  marked_for_cloning: bool
}
impl ScopedTerm {
  pub fn new_from_repr(repr: ScopedTermRepr) -> Self {
    ScopedTerm(
      UnsafeCell::new(ScopedTermInner { repr: RcBox::new(repr), marked_for_cloning: false }))
  }
  pub fn set_repr(&self, new_repr: ScopedTermRepr) { unsafe {
    let inner = &mut*self.0.get();
    if inner.marked_for_cloning {
      let new_box = RcBox::new(new_repr);
      inner.repr = new_box;
    } else {
      *inner.repr.get_mut() = new_repr;
    }
  } }
  pub fn assign_from(&self, another:&Self) { unsafe {
    let inner = &mut*self.0.get();
    let another_inner = &*another.0.get();
    if inner.repr.0.addr() == another_inner.repr.0.addr() { return }
    if inner.marked_for_cloning {
      inner.repr = (*another.0.get()).repr.shallow_copy();
    } else {
      *inner.repr.get_mut() = (*(*another.0.get()).repr.0.as_ptr()).data.deep_clone_one_layer();
    }
  } }
  pub fn shallow_clone(&self) -> Self {
    let inner = unsafe{&*self.0.get()};
    ScopedTerm(UnsafeCell::new(
      ScopedTermInner { repr: inner.repr.shallow_copy(), marked_for_cloning: false }
    ))
  }
  pub fn deep_lazy_clone(&self) -> Self {
    let inner = unsafe{&*self.0.get()};
    ScopedTerm(UnsafeCell::new(
      ScopedTermInner { marked_for_cloning:true, repr:inner.repr.shallow_copy() }
    ))
  }
  pub fn get_repr(&self) -> &ScopedTermRepr {
    let inner = unsafe{&mut *self.0.get()};
    inner.repr.get_ref()
  }
  pub fn get_repr_mut(&self) -> &mut ScopedTermRepr {
    let inner = unsafe{&mut *self.0.get()};
    if inner.marked_for_cloning {
      inner.marked_for_cloning = false;
      let new_repr = inner.repr.get_ref().deep_clone_one_layer();
      inner.repr = RcBox::new(new_repr);
    }
    return inner.repr.get_mut();
  }
}
#[derive(Debug, Clone, Copy)]
pub struct SubstIndex(u32);
impl SubstIndex {
  pub fn get_index(&self) -> usize {
    self.0 as _
  }
}

#[derive(Debug)]
pub enum ScopedTermRepr {
  App(ScopedTerm, Vec<ScopedTerm>),
  GlobalRef(DefId),
  SubstRef(SubstIndex),
  Sigma {
    binder: ThinPExpr,
    head: ScopedTerm,
    tail: ScopedTerm,
  },
  Pi {
    binder: ThinPExpr,
    head: ScopedTerm,
    tail: ScopedTerm,
  },
  Either(ScopedTerm, ScopedTerm),
  Pair(ScopedTerm, ScopedTerm),
  Arrow(ScopedTerm, ScopedTerm),
  Tuple(ScopedTerm, ScopedTerm),
  Inl(ScopedTerm),
  Inr(ScopedTerm),

  LetGroup(Vec<(ThinPExpr, ScopedTerm, ScopedTerm)>, ScopedTerm),
  LambdaHead(ThinPExpr, ScopedTerm),
  Lambda(Vec<ScopedTerm>),
  Star,
  Void,
  USort,
  Pt,
}
impl ScopedTermRepr {
  fn release_subnodes(&self) { unsafe {
    match self {
      ScopedTermRepr::App(h, args) => {
        (*h.0.get()).repr.release_reference();
        for arg in args {
          (*arg.0.get()).repr.release_reference()
        }
      },
      ScopedTermRepr::GlobalRef(_) => (),
      ScopedTermRepr::SubstRef(_) => (),
      ScopedTermRepr::Star => (),
      ScopedTermRepr::LetGroup(vs, t) => {
        for (_, ty, val) in vs {
          (*ty.0.get()).repr.release_reference();
          (*val.0.get()).repr.release_reference()
        }
        (*t.0.get()).repr.release_reference()
      },
      ScopedTermRepr::LambdaHead(_, tail) => {
        (*tail.0.get()).repr.release_reference()
      },
      ScopedTermRepr::Pt |
      ScopedTermRepr::Void |
      ScopedTermRepr::USort => (),
      ScopedTermRepr::Sigma { head, tail, .. } |
      ScopedTermRepr::Pi { head, tail, .. } => {
        (*head.0.get()).repr.release_reference();
        (*tail.0.get()).repr.release_reference();
      },
      ScopedTermRepr::Inl(a) |
      ScopedTermRepr::Inr(a) => {
        (*a.0.get()).repr.release_reference();
      }
      ScopedTermRepr::Arrow(a, b) |
      ScopedTermRepr::Tuple(a, b) |
      ScopedTermRepr::Either(a, b) |
      ScopedTermRepr::Pair(a, b) => {
        (*a.0.get()).repr.release_reference();
        (*b.0.get()).repr.release_reference();
      },
      ScopedTermRepr::Lambda(cls) => {
        for i in cls {
          (*i.0.get()).repr.release_reference();
        }
      },
    }
  } }
  fn deep_clone_one_layer(&self) -> Self {
    match self {
      ScopedTermRepr::App(h, a) => {
        ScopedTermRepr::App(
          h.deep_lazy_clone(), a.iter().map(|e|e.deep_lazy_clone()).collect())
      },
      ScopedTermRepr::GlobalRef(id) => {
        ScopedTermRepr::GlobalRef(*id)
      },
      ScopedTermRepr::SubstRef(id) => {
        ScopedTermRepr::SubstRef(*id)
      },
      ScopedTermRepr::Star => ScopedTermRepr::Star,
      ScopedTermRepr::LetGroup(gr, t) => {
        let mut v = Vec::new();
        for (p, ty, val) in gr {
          v.push((p.clone(), ty.deep_lazy_clone(), val.deep_lazy_clone()))
        }
        ScopedTermRepr::LetGroup(v, t.deep_lazy_clone())
      },
      ScopedTermRepr::LambdaHead(head, tail) => {
        ScopedTermRepr::LambdaHead(head.clone(), tail.deep_lazy_clone())
      }
      ScopedTermRepr::Pt => ScopedTermRepr::Pt,
      ScopedTermRepr::Void => ScopedTermRepr::Void,
      ScopedTermRepr::USort => {
        ScopedTermRepr::USort
      },
      ScopedTermRepr::Sigma { binder, head, tail } => {
        return ScopedTermRepr::Sigma { binder:binder.clone(), head:head.shallow_clone(), tail:tail.shallow_clone() };
      },
      ScopedTermRepr::Pi { binder, head, tail } => {
        return ScopedTermRepr::Pi { binder:binder.clone(), head:head.shallow_clone(), tail:tail.shallow_clone() };
      },
      ScopedTermRepr::Inl(a) => {
        return ScopedTermRepr::Inl(a.deep_lazy_clone());
      }
      ScopedTermRepr::Inr(a) => {
        return ScopedTermRepr::Inr(a.deep_lazy_clone());
      }
      ScopedTermRepr::Arrow(a, b) => {
        return ScopedTermRepr::Arrow(a.deep_lazy_clone(), b.deep_lazy_clone());
      }
      ScopedTermRepr::Tuple(a, b) => {
        return ScopedTermRepr::Tuple(a.deep_lazy_clone(), b.deep_lazy_clone());
      }
      ScopedTermRepr::Either(a, b) => {
        return ScopedTermRepr::Either(a.deep_lazy_clone(), b.deep_lazy_clone());
      }
      ScopedTermRepr::Pair(a, b) => {
        return ScopedTermRepr::Pair(a.deep_lazy_clone(), b.deep_lazy_clone());
      },
      ScopedTermRepr::Lambda(cls) => {
        ScopedTermRepr::Lambda(cls.iter().map(|e|e.deep_lazy_clone()).collect())
      },
    }
  }
}
// impl Drop for ScopedTermRepr {
//   fn drop(&mut self) {
//     self.release_subnodes()
//   }
// }
pub fn render_term(term: &ScopedTerm) -> String {
  let mut str = String::new();
  render_term_impl(&mut str, term);
  return str;
}
pub fn render_term_impl(str:&mut dyn Write, term: &ScopedTerm) {
  match term.get_repr() {
    ScopedTermRepr::App(h, args) => {
      render_term_impl(str, h);
      for arg in args {
        str.write_str(" (").unwrap();
        render_term_impl(str, arg);
        str.write_str(")").unwrap();
      }
    },
    ScopedTermRepr::GlobalRef(ix) => {
      render_global_ix(str, *ix);
    },
    ScopedTermRepr::SubstRef(ix) => {
      render_subst(str, *ix);
    },
    k@(
      ScopedTermRepr::Sigma { binder, head, tail } |
      ScopedTermRepr::Pi { binder, head, tail }
    ) => {
      str.write_char('(').unwrap();
      render_thin_pexpr_impl(str, binder);
      str.write_str(" : ").unwrap();
      render_term_impl(str, head);
      match k {
        ScopedTermRepr::Sigma { .. } => {
          str.write_str(") and ").unwrap();
        },
        ScopedTermRepr::Pi { .. } => {
          str.write_str(") -> ").unwrap();
        },
        _ => unreachable!()
      }
      render_term_impl(str, tail);
    },
    ScopedTermRepr::Star => {
      str.write_char('*').unwrap();
    },
    ScopedTermRepr::LetGroup(lg, t) => {
      str.write_char('(').unwrap();
      for (p, ty, val) in lg {
        render_thin_pexpr_impl(str, p);
        str.write_str(" : ").unwrap();
        render_term_impl(str, ty);
        str.write_str(" = ").unwrap();
        render_term_impl(str, val);
        str.write_str(", ").unwrap();
      }
      str.write_str(" => ").unwrap();
      render_term_impl(str, t)
    },
    ScopedTermRepr::LambdaHead(binder, tail) => {
      str.write_char('\\').unwrap();
      render_thin_pexpr_impl(str, binder);
      str.write_str(".").unwrap();
      render_term_impl(str, tail);
    }
    ScopedTermRepr::Pt => {
      str.write_str("()").unwrap();
    },
    ScopedTermRepr::Void => {
      str.write_str("Void").unwrap();
    },
    ScopedTermRepr::USort => {
      str.write_str("#").unwrap();
    },
    ScopedTermRepr::Pair(a, b) => {
      render_term_impl(str, a);
      str.write_str(" and ").unwrap();
      render_term_impl(str, b);
    },
    ScopedTermRepr::Either(a, b) => {
      render_term_impl(str, a);
      str.write_str(" or ").unwrap();
      render_term_impl(str, b);
    },
    ScopedTermRepr::Arrow(a, b) => {
      render_term_impl(str, a);
      str.write_str(" -> ").unwrap();
      render_term_impl(str, b);
    },
    ScopedTermRepr::Tuple(a, b) => {
      str.write_char('(').unwrap();
      render_term_impl(str, a);
      str.write_str(", ").unwrap();
      render_term_impl(str, b);
      str.write_char(')').unwrap();
    },
    ScopedTermRepr::Inl(a) => {
      str.write_str("inl ").unwrap();
      render_term_impl(str, a);
    },
    ScopedTermRepr::Inr(b) => {
      str.write_str("inr ").unwrap();
      render_term_impl(str, b);
    },
    ScopedTermRepr::Lambda(cls) => {
      str.write_str("{ ").unwrap();
      for item in cls {
        render_term_impl(str, item);
        str.write_char(',').unwrap();
      }
      str.write_str(" }");
    },
  }
}
pub fn render_args(args: &[ScopedTerm]) -> String {
  let mut str = String::new();
  render_args_impl(&mut str,args);
  return str;
}
pub fn render_args_impl(str:&mut dyn Write, args: &[ScopedTerm]) {
  for arg in args {
    render_term_impl(str, arg);
    str.write_char(' ').unwrap();
  }
}
pub fn render_lambda(lambda: &Lambda) -> String {
  let mut str = String::new();
  render_lambda_impl(&mut str,lambda);
  return str;
}
pub fn render_lambda_impl(str:&mut dyn Write, lambda: &Lambda) {
  str.write_str("{ ");
  for (pbs, rhs) in &lambda.0 {
    for pb in pbs {
      render_thin_pexpr_impl(str, pb);
      str.write_str(", ").unwrap();
    }
    str.write_str(" => ").unwrap();
    render_term_impl(str, rhs);
    str.write_str(", ").unwrap();
  }
  str.write_str(" }").unwrap();
}
fn render_atom(str:&mut dyn Write, atom: &Atom) {
  match atom {
    Atom::And => str.write_str("and"),
    Atom::Or => str.write_str("or"),
    Atom::Arrow => str.write_str("->"),
    Atom::Tilda => str.write_str("~"),
    Atom::TupleCtor => str.write_str("(,)"),
    Atom::Inl => str.write_str("inl"),
    Atom::Inr => str.write_str("inr"),
  }.unwrap();
}
pub fn render_thin_pexpr(pexpr: &ThinPExpr) -> String {
  let mut str = String::new();
  render_thin_pexpr_impl(&mut str,pexpr);
  return str;
}
pub fn render_thin_pexpr_impl(str:&mut dyn Write, pexpr: &ThinPExpr) {
  match pexpr {
    ThinPExpr::Discard => {
      str.write_char('_').unwrap();
    },
    ThinPExpr::Binder(b) => {
      render_subst(str, *b);
    },
    ThinPExpr::Group(atom, args) => {
      render_atom(str, atom);
      str.write_char(' ').unwrap();
      for arg in args {
        render_thin_pexpr_impl(str, arg);
        str.write_char(' ').unwrap();
      }
    },
    ThinPExpr::Pt => {
      str.write_str("()").unwrap();
    },
  }
}
pub fn render_decl(decl: &ScopedDecl) -> String {
  let mut str = String::new();
  render_decl_impl(&mut str, decl);
  return str;
}
pub fn render_decl_impl(str:&mut dyn Write, decl: &ScopedDecl) {
  str.write_str("def ");
  str.write_str(&decl.name);
  str.write_str(" : ");
  render_term_impl(str, &decl.type_);
  str.write_str(" = ");
  render_term_impl(str, &decl.value);
}
pub fn render_global_ix(str:&mut dyn Write, gix: DefId) {
  write!(str, "{}G", gix.0).unwrap();
}
pub fn render_subst(str:&mut dyn Write, six: SubstIndex) {
  write!(str, "{}B", six.0).unwrap();
}

#[derive(Debug)]
pub struct Lambda(pub Vec<(Vec<ThinPExpr>, ScopedTerm)>);

#[derive(Debug, Clone)]
pub enum ThinPExpr {
  Discard,
  Binder(SubstIndex),
  Group(Atom, Vec<Self>),
  Pt
}
#[derive(Debug, Clone)]
pub enum SemanticError {
  ReservedName,
  DuplicateName(String),
  InvalidRef(String),
  GenericMessage(String)
}
pub struct SemaCheckCtx<'i> {
  aggregated_errors: Vec<GenericError>,
  encountered_names: &'i HashMap<&'i str, u32>,
  chars: &'i [u8],
}

type Maybe<T> = Option<T>;
fn check_scope(
  ctx: &mut SemaCheckCtx ,
  obj: &PrecedenceResolvedTExpr,
  binder_ctx: &mut CollectBinderCtx
) -> Maybe<ScopedTerm> {
  match obj {
    PrecedenceResolvedTExpr::App(head, args) => {
      let mut failed = false;
      let mut args_ = Vec::new();
      for arg in args {
        let arg = check_scope(ctx, arg, binder_ctx);
        match arg {
          Some(arg) => {
            args_.push(arg)
          },
          None => failed = true,
        }
      }
      if failed { return None }
      match head.as_ref() {
        PrecedenceResolvedTExpr::AtomRef(atom) => {
          let arg_lim = match atom {
            Atom::And |
            Atom::Or |
            Atom::Arrow |
            Atom::Tilda |
            Atom::TupleCtor => 2,
            Atom::Inl |
            Atom::Inr => 1,
          };
          if args_.len() > arg_lim {
            let msg = format!("invalid args in {:?}", obj);
            ctx.aggregated_errors.push(GenericError::String(msg));
            return None
          }
          let term = match atom {
            Atom::And => {
              if arg_lim != 2 {
                let msg = format!("invalid args in {:?}", obj);
                ctx.aggregated_errors.push(GenericError::String(msg));
                return None
              }
              ScopedTerm::new_from_repr(ScopedTermRepr::Pair(args_[0].shallow_clone(), args_[1].shallow_clone()))
            },
            Atom::Or => {
              if arg_lim != 2 {
                let msg = format!("invalid args in {:?}", obj);
                ctx.aggregated_errors.push(GenericError::String(msg));
                return None
              }
              ScopedTerm::new_from_repr(ScopedTermRepr::Either(args_[0].shallow_clone(), args_[1].shallow_clone()))
            },
            Atom::Arrow => {
              if arg_lim != 2 {
                let msg = format!("invalid args in {:?}", obj);
                ctx.aggregated_errors.push(GenericError::String(msg));
                return None
              }
              ScopedTerm::new_from_repr(ScopedTermRepr::Arrow(args_[0].shallow_clone(), args_[1].shallow_clone()))
            },
            Atom::Tilda => {
              if arg_lim != 2 {
                let msg = format!("invalid args in {:?}", obj);
                ctx.aggregated_errors.push(GenericError::String(msg));
                return None
              }
              todo!()
            },
            Atom::TupleCtor => {
              if arg_lim != 2 {
                let msg = format!("invalid args in {:?}", obj);
                ctx.aggregated_errors.push(GenericError::String(msg));
                return None
              }
              ScopedTerm::new_from_repr(ScopedTermRepr::Tuple(args_[0].shallow_clone(), args_[1].shallow_clone()))
            },
            Atom::Inl => {
              if arg_lim != 1 {
                let msg = format!("invalid args in {:?}", obj);
                ctx.aggregated_errors.push(GenericError::String(msg));
                return None
              }
              ScopedTerm::new_from_repr(ScopedTermRepr::Inl(args_[0].shallow_clone()))
            },
            Atom::Inr => {
              if arg_lim != 1 {
                let msg = format!("invalid args in {:?}", obj);
                ctx.aggregated_errors.push(GenericError::String(msg));
                return None
              }
              ScopedTerm::new_from_repr(ScopedTermRepr::Inr(args_[0].shallow_clone()))
            },
          };
          return Some(term);
        },
        head => {
          let head_ = check_scope(ctx, head, binder_ctx)?;
          return Some(ScopedTerm::new_from_repr(ScopedTermRepr::App(head_, args_)));
        }
      };
    },
    PrecedenceResolvedTExpr::Ref(chars) => {
      let ident = get_name(ctx.chars, chars);
      match ident {
        "Void" => {
          return Some(ScopedTerm::new_from_repr(ScopedTermRepr::Void));
        },
        _ => ()
      }
      if let Some(ix) = binder_ctx.binders.get(ident) {
        return Some(ScopedTerm::new_from_repr(ScopedTermRepr::SubstRef(SubstIndex(*ix))));
      }
      if let Some(ix) = ctx.encountered_names.get(ident) {
        return Some(ScopedTerm::new_from_repr(ScopedTermRepr::GlobalRef(DefId(*ix))))
      } else {
        ctx.aggregated_errors.push(
          GenericError::SemanticError(SemanticError::InvalidRef(ident.to_string())));
        return None
      }
    },
    k@(
      PrecedenceResolvedTExpr::Sigma { binder, head, tail } |
      PrecedenceResolvedTExpr::Pi { binder, head, tail }
    ) => {
      let chk_head = check_scope(ctx, head, binder_ctx);
      let thin = build_thin_pexpr(binder_ctx, binder);
      let chk_spine = check_scope(ctx, tail, binder_ctx);
      if !binder_ctx.errors.is_empty() {
        ctx.aggregated_errors.append(&mut binder_ctx.errors);
      }
      match (chk_head, chk_spine) {
        (Some(head), Some(spine)) => {
          if let PrecedenceResolvedTExpr::Sigma { .. } = k {
            return Some(ScopedTerm::new_from_repr(
              ScopedTermRepr::Sigma { binder: thin, head: head, tail: spine }))
          }
          if let PrecedenceResolvedTExpr::Pi { .. } = k {
            return Some(ScopedTerm::new_from_repr(
              ScopedTermRepr::Pi { binder: thin, head: head, tail: spine }))
          }
          unreachable!()
        },
        _ => return None
      }
    },
    PrecedenceResolvedTExpr::Star =>
      return Some(ScopedTerm::new_from_repr(ScopedTermRepr::Star)),
    PrecedenceResolvedTExpr::Let(items, tail) => {
      let mut thins = Vec::new();
      for (pexpr, _, _) in items {
        let thin = build_thin_pexpr(binder_ctx, pexpr);
        thins.push(thin);
      }
      let mut items_ = Vec::new();
      for (thin, (_, ty, val)) in std::iter::zip(thins, items) {
        let ty = check_scope(ctx, ty, binder_ctx);
        let val = check_scope(ctx, val, binder_ctx);
        match (ty, val) {
          (Some(ty), Some(val)) => items_.push((thin.clone(),ty, val)),
          _ => ()
        }
      }
      if !binder_ctx.errors.is_empty() {
        ctx.aggregated_errors.append(&mut binder_ctx.errors);
      }
      if let Some(tail) = check_scope(ctx, tail, binder_ctx) {
        return Some(ScopedTerm::new_from_repr(ScopedTermRepr::LetGroup(items_, tail)))
      }
      return None
    },
    PrecedenceResolvedTExpr::Lambda(clauses) => {
      let mut checked_clauses = Vec::new();
      for (patterns, rhs) in clauses {
        let mut thins = Vec::new();
        for pattern in patterns {
          let i = build_thin_pexpr(binder_ctx, pattern);
          thins.push(i);
        }
        if let Some(rhs) = check_scope(ctx, rhs, binder_ctx) {
          checked_clauses.push((thins.clone(), rhs))
        }
        if !binder_ctx.errors.is_empty() {
          ctx.aggregated_errors.append(&mut binder_ctx.errors)
        }
      }
      if !ctx.aggregated_errors.is_empty() { return None }
      let cls = checked_clauses.iter().map(|e|change_lambda_repr(&e.0[..], e.1.shallow_clone(), 0));
      return Some(ScopedTerm::new_from_repr(ScopedTermRepr::Lambda(cls.collect())));
    },
    PrecedenceResolvedTExpr::Pt => return Some(ScopedTerm::new_from_repr(ScopedTermRepr::Pt)),
    PrecedenceResolvedTExpr::Void => return Some(ScopedTerm::new_from_repr(ScopedTermRepr::Void)),
    PrecedenceResolvedTExpr::AtomRef(_) => todo!(),
  }
}
fn change_lambda_repr(cls: &[ThinPExpr], rhs: ScopedTerm, index: usize) -> ScopedTerm {
  let head = &cls[0];
  let rest = &cls[1..];
  if rest.is_empty() {
    return ScopedTerm::new_from_repr(ScopedTermRepr::LambdaHead(head.clone(), rhs));
  } else {
    let next = change_lambda_repr(rest, rhs, index+1);
    return ScopedTerm::new_from_repr(ScopedTermRepr::LambdaHead(head.clone(), next));
  }
}

pub fn get_name<'i, 'k>(str: &'i [u8], chars: &'k CharsData) -> &'i str {
  unsafe {
    let slice = std::slice::from_raw_parts(
      str.as_ptr().add(chars.off1 as usize),
      chars.off2 as usize);
    std::str::from_utf8_unchecked(slice)
  }
}

struct CollectBinderCtx<'i> {
  str: &'i [u8],
  errors: Vec<GenericError>,
  binders: HashMap<&'i str, u32>,
  index: u32,
}
fn fresh_ident(ctx: &mut CollectBinderCtx) -> u32 {
  let id = ctx.index;
  ctx.index += 1;
  return id
}
fn build_thin_pexpr(
  ctx: &mut CollectBinderCtx, pexpr: &RefinedPExpr
) -> ThinPExpr {
  match pexpr {
    RefinedPExpr::Pt => ThinPExpr::Pt,
    RefinedPExpr::Discard => ThinPExpr::Discard,
    RefinedPExpr::Binder(chars) => {
      let ident = get_name(ctx.str, chars);
      let ix = fresh_ident(ctx);
      let outcome = ctx.binders.insert(ident, ix);
      if outcome.is_some() {
        let str = format!("Dup binder: {}", ident);
        ctx.errors.push(
          GenericError::SemanticError(SemanticError::GenericMessage(str)))
      }
      return ThinPExpr::Binder(SubstIndex(ix));
    },
    RefinedPExpr::Group(head, subpats) => {
      let mut subpats_ = Vec::new();
      for subpat in subpats {
        let sp = build_thin_pexpr(ctx, subpat);
        subpats_.push(sp);
      }
      return ThinPExpr::Group(*head, subpats_);
    },
  }
}

pub fn build_defs(
  bytes: &[u8],
) -> Result<Vec<ScopedDecl>, Vec<GenericError>>{
  let mut parser = SourceTextParser::new(bytes);
  let res = parser.parse_to_end();
  match res {
    Ok(defs) => {
      let mut scchk = ScopeCheckCtx::new(bytes);
      let out = scope_check_decls(&mut scchk, &defs);
      return out;
    },
    Err(err) => {
      return Err(vec!(GenericError::ParseFailure(err)));
    },
  }
}

impl Debug for ScopedTerm {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let str = render_term(self);
    f.write_str(&str)
  }
}
impl Display for ScopedTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&render_term(self))
    }
}

#[test]
fn delc_cheking() {
  let mut s =
    "".to_string() +
    "d : * = (T:*) -> (K:*) -> T and K or ()"
    ;
  pad_string(&mut s);
  let mut parser = SourceTextParser::new(s.as_bytes());
  let expr = parser.parse_to_end();
  match expr {
    Err(err) => println!("{:?}", err),
    Ok(raw_decls) => {
      let mut ctx = ScopeCheckCtx::new(s.as_bytes());
      let decls = scope_check_decls(&mut ctx, &raw_decls);

      println!("{:#?}", decls)
    }
  }
}

#[test]
fn delc_cheking4() {
  let mut s =
    "".to_string() +
    "a : * = { i => { m,i_ => i i_ m } }"
    ;
  pad_string(&mut s);
  let mut parser = SourceTextParser::new(s.as_bytes());
  let expr = parser.parse_to_end();
  match expr {
    Err(err) => println!("{:?}", err),
    Ok(raw_decls) => {
      let mut ctx = ScopeCheckCtx::new(s.as_bytes());
      let decls = scope_check_decls(&mut ctx, &raw_decls);

      println!("{:#?}", decls)
    }
  }
}

#[test]
fn cloning() {
  let term = ScopedTerm::new_from_repr(ScopedTermRepr::Star);
  println!("started with original {}", render_term(&term));
  let clone = term.deep_lazy_clone();
  clone.assign_from(&ScopedTerm::new_from_repr(ScopedTermRepr::Pt));
  println!("after reassign original is {}", render_term(&term));
  drop(term);
  println!("and clone is {}", render_term(&clone));
  drop(clone);
}