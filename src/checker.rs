use core::{cell::UnsafeCell, fmt::{Debug, Write}, future::{poll_fn, Future}, mem::transmute, pin::Pin, sync::atomic::compiler_fence, task::Poll};
use std::{borrow::Cow, collections::{HashSet, VecDeque}, iter::zip, ptr::addr_of_mut, rc::Rc};

use crate::{parser::{Atom, RefinedPExpr}, sema::{ScopedDecl, GenericError, DefId, ScopedTerm, ThinPExpr, Lambda, ScopeCheckCtx, scope_check_decls, RcBox, ScopedTermRepr, render_term, render_thin_pexpr_impl, render_lambda, render_thin_pexpr, render_args, render_decl_impl, render_global_ix, render_term_impl, render_lambda_impl, render_args_impl, SubstIndex}, utils::{Outcome, inside_out}, lexer::{pad_string, SourceTextParser}};


#[derive(Debug, Clone, Copy, PartialEq)]
enum CheckState {
  Began,
  Ok,
  Bad
}

#[derive(Debug)]
enum ElabIssue {
  UnproductiveCycle(Vec<DefId>),
  InvalidInhabitance,
  InvalidBinder,
  UnsupportedBinder,
  TypeMismatch {
    rep: String
  },
  BadDef,
  InvalidApplication
}

struct CheckableDecl(UnsafeCell<CheckableDeclInner>);

struct CheckableDeclInner {
  scoped_decl: ScopedDecl,
  check_state: Option<CheckState>,
  elab_trace: Option<String>,
  issues: Vec<ElabIssue>,
  dependants: Vec<ElabItem>
}
impl CheckableDecl {
  fn new(
    sd: ScopedDecl
  ) -> Self {
    Self(UnsafeCell::new(CheckableDeclInner {
      scoped_decl: sd, check_state: None, elab_trace: None,
      issues: vec![],
      dependants: vec![]
    }))
  }
  fn inner(&self) -> &mut CheckableDeclInner {
    unsafe { &mut*self.0.get() }
  }
  fn get_value(&self) -> &ScopedTerm {
    &self.inner().scoped_decl.value
  }
  fn get_type(&self) -> &ScopedTerm {
    &self.inner().scoped_decl.type_
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
    let inner = self.inner();
    let mut s = f.debug_tuple("CheckableDecl");
    s.field(&inner.check_state);
    s.field(&inner.elab_trace);
    s.field(&inner.issues);
    s.field(&inner.scoped_decl);
    s.finish()
  }
}
#[derive(Debug)]
struct ScopedEnv {
  decls: Vec<CheckableDecl>
}
struct ElabItem {
  repr: Box<dyn Future<Output = ()>>,
  start_decl: DefId
}

struct ElabEnv(UnsafeCell<ElabEnvInner>);
struct ElabEnvInner {
  defs: ScopedEnv,
}
impl ElabEnv {
  fn inner(&self) -> &mut ElabEnvInner {
    unsafe { &mut *self.0.get() }
  }
  fn get_def(&self, gix: DefId) -> &CheckableDecl {
    &self.inner().defs.decls[gix.get_def_index()]
  }
  fn new_from_scoped_defs(defs: Vec<ScopedDecl>) -> ElabEnv {
    let checakbles =
      defs
      .into_iter()
      .map(CheckableDecl::new)
      .collect();
    ElabEnv(UnsafeCell::new(ElabEnvInner { defs: ScopedEnv { decls: checakbles } }))
  }
}
impl Debug for ElabEnv {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let mut s = f.debug_struct("ElabEnv");
    s.field("defs", &self.inner().defs);
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
          for item in &trace {
            ctx.get_def(*item).inner().check_state = Some(CheckState::Bad);
          }
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
    ScopedTermRepr::USort |
    ScopedTermRepr::Star => (),
    ScopedTermRepr::LambdaHead(_, tail) => {
      check_productivity(ctx, start_decl, tail, found_ground_terms, trace)
    },
  }
}

fn begin_elab(
  env: &ElabEnv,
  thunks: &mut VecDeque<ElabItem>,
) {
  let inner = env.inner();
  for item in &inner.defs.decls {
    let item_inner = item.inner();
    item_inner.check_state = Some(CheckState::Began);

    let mut found_ground = false;
    let trace = vec![item.inner().scoped_decl.index];
    check_productivity(env, item, &item.inner().scoped_decl.value, &mut found_ground, trace);

    let cpy: &ElabEnv = unsafe { transmute(env) };
    let item = unsafe { transmute(item) };
    let thunk = async move {
      match check(cpy, item, item.get_type(), item.get_value()).await {
        Ok(_) => {
          let inner = item.inner();
          inner.check_state = Some(CheckState::Ok);
        },
        Err(err) => {
          let inner = item.inner();
          inner.check_state = Some(CheckState::Bad);
          inner.issues.push(err);
        },
      };
    };
    thunks.push_back(ElabItem { repr: Box::new(thunk), start_decl: item_inner.scoped_decl.index })
  }
}

struct PollCtx {
  dep: Option<PollCtxDepencency>
}
impl PollCtx {
  fn put_dependency(&mut self, dep: PollCtxDepencency) {
    self.dep = Some(dep);
  }
}
enum PollCtxDepencency {
  UnfinishedDef(DefId),
}

fn run_elab(
  env: &ElabEnv,
  postponed: &mut VecDeque<ElabItem>,
) {
  let mut poll_ctx = PollCtx {
    dep: None
  };

  while let Some(mut thunk) = postponed.pop_front() {
    let pined = unsafe { core::pin::Pin::new_unchecked(thunk.repr.as_mut()) };
    match Future::poll(pined, unsafe { transmute(&mut poll_ctx) }) {
      Poll::Ready(()) => {
        let i = env.get_def(thunk.start_decl).inner();
        i.check_state = Some(CheckState::Ok);
        while let Some(dep) = i.dependants.pop() {
          postponed.push_front(dep)
        }
      },
      Poll::Pending => {
        match poll_ctx.dep.take() {
          Some(PollCtxDepencency::UnfinishedDef(id)) => {
            env.get_def(id).inner().dependants.push(thunk);
          },
          None => unreachable!(),
        }
      },
    }
  }
}

fn get_def<'a>(ctx: &'a ElabEnv, defid: DefId) -> impl Future<Output = Result<&'a CheckableDecl, ()>> + 'a {
  poll_fn(move |pctx| {
    let pctx: &mut PollCtx = unsafe { transmute(pctx) };
    let def = ctx.get_def(defid);
    let inner = def.inner();
    match inner.check_state.unwrap() {
      CheckState::Began => {
        pctx.put_dependency(PollCtxDepencency::UnfinishedDef(defid));
        return Poll::Pending;
      },
      CheckState::Ok => {
        return Poll::Ready(Ok(def))
      },
      CheckState::Bad => return Poll::Ready(Err(())),
    }
  })
}

struct OpenerCtx {
  items: Vec<Option<ThinPExpr>>
}
impl OpenerCtx {
  fn new() -> Self {
    Self { items: Vec::new() }
  }
  fn put(&mut self, bix: SubstIndex, pat: ThinPExpr) {
    let ix = bix.get_index();
    let len = self.items.len();
    if ix >= len {
      for _ in 0 .. (ix - len) + 1 {
        self.items.push(None);
      }
    }
    self.items[ix] = Some(pat);
  }
  fn get(&self, bix: SubstIndex) -> &ThinPExpr {
    self.items.get(bix.get_index()).unwrap().as_ref().unwrap()
  }
}

#[must_use]
async fn check(
  env: &ElabEnv,
  def: &CheckableDecl,
  ty: &ScopedTerm,
  val: &ScopedTerm
) -> Result<(), ElabIssue> {
  match ty.get_repr() {
    ScopedTermRepr::App(_, _) => todo!(),
    ScopedTermRepr::GlobalRef(_) => todo!(),
    ScopedTermRepr::SubstRef(_) => todo!(),
    ScopedTermRepr::Sigma { binder, head, tail } => {
      todo!()
    },
    ScopedTermRepr::Pi { .. } => {
      if let ScopedTermRepr::Lambda(clauses) = val.get_repr() {
        let mut octx = OpenerCtx::new();
        for clause in clauses {
          check_pi_lambda_clause(env, def, &mut octx, ty, clause).await?;
        }
        return Ok(());
      } else {
        return Err(ElabIssue::TypeMismatch {
          rep: format!("{} :! {}", render_term(&val), render_term(&ty))
        });
      }
    },
    ScopedTermRepr::Either(_, _) => todo!(),
    ScopedTermRepr::Pair(_, _) => todo!(),
    ScopedTermRepr::Arrow(_, _) => todo!(),
    ScopedTermRepr::Tuple(_, _) => todo!(),
    ScopedTermRepr::Inl(_) => todo!(),
    ScopedTermRepr::Inr(_) => todo!(),
    ScopedTermRepr::LetGroup(_, _) => todo!(),
    ScopedTermRepr::LambdaHead(_, _) => todo!(),
    ScopedTermRepr::Lambda(_) => todo!(),
    ScopedTermRepr::Void => {
      return Err(ElabIssue::TypeMismatch {
        rep: format!("{} :! {}", render_term(&val) ,render_term(&ty))
      });
    },
    ScopedTermRepr::Star => todo!(),
    ScopedTermRepr::USort => {
      match val.get_repr() {
        ScopedTermRepr::App(_, _) => todo!(),
        ScopedTermRepr::GlobalRef(_) => todo!(),
        ScopedTermRepr::SubstRef(_) => todo!(),
        ScopedTermRepr::Sigma { binder:_, head, tail } => todo!(),
        ScopedTermRepr::Pi { binder, head, tail } => todo!(),
        ScopedTermRepr::Either(_, _) => todo!(),
        ScopedTermRepr::Pair(_, _) => todo!(),
        ScopedTermRepr::Arrow(_, _) => todo!(),
        ScopedTermRepr::Void => todo!(),
        ScopedTermRepr::Pt => todo!(),
        ScopedTermRepr::USort => unreachable!(),
        _ => {
          if let ScopedTermRepr::Star = ty.get_repr() {
            return Err(ElabIssue::TypeMismatch {
              rep: format!("{} :! {}", render_term(&val) ,render_term(&ty))
            });
          } else {
            return Ok(());
          }
        },
      }
    },
    ScopedTermRepr::Pt => {
      if let ScopedTermRepr::Pt = val.get_repr() {
        return Ok(());
      } else {
        return Err(ElabIssue::TypeMismatch {
          rep: format!("{} :! {}", render_term(&val) ,render_term(&ty))
        });
      };
    },
  }
}

async fn eval(
  env: &ElabEnv,
  opener_context: &OpenerCtx,
  val: &ScopedTerm
) -> Result<(), ElabIssue> {
  match val.get_repr() {
    ScopedTermRepr::App(head, arg) => {
      match head.get_repr() {
        ScopedTermRepr::Lambda(cls) => todo!(),
        _ => {
          return Box::pin(eval(env, opener_context, head)).await;
        }
      }
    },
    ScopedTermRepr::GlobalRef(defid) => {
      let smth = match get_def(env, *defid).await {
        Ok(cdl) => cdl,
        Err(_) => return Err(ElabIssue::BadDef),
      };
      val.assign_from(&smth.inner().scoped_decl.value);
      return Ok(());
    },
    ScopedTermRepr::SubstRef(_) => {
      return Ok(());
    },
    ScopedTermRepr::LetGroup(_, _) => todo!(),
    _ => {
      return Ok(());
    }
  }
}

async fn check_pi_lambda_clause(
  env: &ElabEnv,
  def: &CheckableDecl,
  opener_context: &mut OpenerCtx,
  ty: &ScopedTerm,
  val: &ScopedTerm,
) -> Result<(), ElabIssue> {
  match ty.get_repr() {
    ScopedTermRepr::Pi { binder, head, tail } => {
      if let ScopedTermRepr::LambdaHead(b, rest) = val.get_repr() {
        let head = head.deep_lazy_clone();
        eval(env, opener_context, &head).await?;
        Box::pin(check(env, def, &ScopedTerm::new_from_repr(ScopedTermRepr::USort), &head)).await?;
        check_binder_aprop(env, opener_context, ty, &[b.clone()]).await?;
        match binder {
          ThinPExpr::Discard => (),
          ThinPExpr::Binder(bix) => {
            opener_context.put(*bix, b.clone());
          },
          _ => {
            return Err(ElabIssue::UnsupportedBinder);
          }
        }
        return Box::pin(check_pi_lambda_clause(env, def, opener_context, tail, rest)).await;
      } else {
        return Err(ElabIssue::TypeMismatch {
          rep: format!("{} :! {}", render_term(&ty), render_term(&val))
        });
      }
    },
    ScopedTermRepr::LetGroup(_, _) => todo!(),
    ScopedTermRepr::App(_, _) => todo!(),
    ScopedTermRepr::GlobalRef(_) => todo!(),
    ScopedTermRepr::SubstRef(_) => todo!(),
    ScopedTermRepr::Sigma { binder, head, tail } => todo!(),
    _ => {
      return Err(ElabIssue::TypeMismatch {
        rep: format!("{} :! {}", render_term(&ty), render_term(&val))
      });
    }
  }
}

async fn check_binder_aprop(
  env: &ElabEnv,
  opener_context: &mut OpenerCtx,
  ty: &ScopedTerm,
  pats: &[ThinPExpr]
) -> Result<(), ElabIssue> {
  if pats.is_empty() { return Ok(()) }
  match ty.get_repr() {
    ScopedTermRepr::App(_, _) => {
      return Err(ElabIssue::InvalidBinder);
    },
    ScopedTermRepr::GlobalRef(_) => {
      return Err(ElabIssue::InvalidBinder);
    },
    ScopedTermRepr::SubstRef(_) => {
      return Err(ElabIssue::InvalidBinder);
    },
    ScopedTermRepr::Sigma { binder, head, tail } => {
      let head = head.deep_lazy_clone();
      eval(env, opener_context, &head).await?;
      match &pats[0] {
        ThinPExpr::Discard => (),
        ThinPExpr::Binder(_) => todo!(),
        ThinPExpr::Group(Atom::TupleCtor, args) => {
          Box::pin(check_binder_aprop(env, opener_context, &head, &[args[0].clone()])).await?;
          match binder {
            ThinPExpr::Discard => (),
            ThinPExpr::Binder(bix) => {
              opener_context.put(*bix, pats[0].clone());
            },
            _ => {
              return Err(ElabIssue::UnsupportedBinder);
            }
          }
          Box::pin(check_binder_aprop(env, opener_context, tail, &args[1..])).await?;
        },
        _ => {
          return Err(ElabIssue::InvalidBinder);
        }
      }
      return Ok(());
    },
    ScopedTermRepr::Pi { binder:_, head:_, tail:_ } => {
      match &pats[0] {
        ThinPExpr::Discard => {
          return Ok(());
        },
        ThinPExpr::Binder(_) => {
          return Ok(());
        },
        _ => {
          return Err(ElabIssue::InvalidBinder);
        }
      }
    },
    ScopedTermRepr::Either(_, _) => todo!(),
    ScopedTermRepr::Pair(_, _) => todo!(),
    ScopedTermRepr::Arrow(_, _) => todo!(),
    ScopedTermRepr::Tuple(_, _) => todo!(),
    ScopedTermRepr::LetGroup(_, _) => todo!(),
    ScopedTermRepr::Void => todo!(),
    ScopedTermRepr::Pt => todo!(),

    ScopedTermRepr::Inl(_) |
    ScopedTermRepr::Inr(_) |
    ScopedTermRepr::LambdaHead(_, _) |
    ScopedTermRepr::Lambda(_) |
    ScopedTermRepr::Star |
    ScopedTermRepr::USort => {
      unreachable!();
    },
  }
}

#[test] #[ignore]
fn t0() {
  let mut text =
    "a : (m: () or ()) -> { inl () => (), inr () => () } m = { inl () => (), inr () => () }".to_string() +
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
  let mut postponed = VecDeque::new();
  begin_elab(&elab_env, &mut postponed);
  println!("{:#?}", elab_env);
}

#[test] #[ignore]
fn t1() {
  let mut text =
    "a : (T:*) -> T -> T = { _, i => i }".to_string() +
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
  let mut postponed = VecDeque::new();
  begin_elab(&elab_env, &mut postponed);
  run_elab(&elab_env, &mut postponed);
  println!("{:#?}", elab_env);

}

#[test] #[ignore]
fn t2() {
  let mut text =
    "a : (T:*) -> (d : (K:*) and ({ i, _ => i } T K)) -> { _ => () } d = { _, i => i }".to_string() +
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
  let mut postponed = VecDeque::new();
  begin_elab(&elab_env, &mut postponed);
  println!("{:#?}", elab_env);

}