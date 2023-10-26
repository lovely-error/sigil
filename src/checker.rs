use core::{fmt::Write, cell::UnsafeCell, sync::atomic::compiler_fence};
use std::{collections::VecDeque, iter::zip, rc::Rc, ptr::addr_of_mut};

use crate::{parser::{Atom, LiftKind, RefinedPExpr}, sema::{ScopedDecl, GenericError, DefId, ScopedTerm, ThinPExpr, Lambda, ScopeCheckCtx, scope_check_decls, RcBox, ScopedTermRepr, render_term, render_thin_pexpr_impl, render_lambda, render_thin_pexpr, render_args, render_decl_impl, LiftNode, render_global_ix, render_term_impl, render_lambda_impl, render_args_impl, SubstIndex}, utils::{Outcome, inside_out}, lexer::{pad_string, SourceTextParser}};

trait OutcomeType {
  type Value;
  type Failure;
  fn new_from_value(_: Self::Value) -> Self;
  fn new_from_failure(_: Self::Failure) -> Self;
}
impl <R, E> OutcomeType for ElabResult<Outcome<R, E>> {
    type Value = R;
    type Failure = E;
    fn new_from_value(val: <ElabResult<Outcome<R, E>> as OutcomeType>::Value) -> Self {
      return ElabResult::Value(Outcome::Result(val));
    }
    fn new_from_failure(err: Self::Failure) -> Self {
      return ElabResult::Value(Outcome::OneErr(err));
    }
}
macro_rules! emit {
    ($expr:expr) => {
        {
          OutcomeType::new_from_value($expr)
        }
    };
}
macro_rules! throw {
    ($expr:expr) => {
      {
        OutcomeType::new_from_failure($expr)
      }
    };
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum CheckState {
  Untouched,
  Began,
  Ok,
  Bad
}

#[derive(Debug)]
struct CheckableDecl(UnsafeCell<CheckableDeclInner>);
struct CheckableDeclInner {
  scoped_decl: ScopedDecl,
  check_state: CheckState,
  elab_trace: Option<String>
}
impl CheckableDecl {
  fn new(
    sd: ScopedDecl
  ) -> Self {
    Self(UnsafeCell::new(CheckableDeclInner {
      scoped_decl: sd, check_state: CheckState::Untouched, elab_trace: Some(String::new()) }))
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

struct ScopedEnv {
  decls: Vec<CheckableDecl>
}

struct ElabEnv {
  defs: ScopedEnv,
  postponed: VecDeque<StuckElab>,
}
impl ElabEnv {
  fn get_def(&self, gix: DefId) -> &CheckableDecl {
    &self.defs.decls[gix.get_def_index()]
  }
}
type StuckElab = Box<dyn FnOnce(*mut ElabEnv) -> ElabResult<Outcome<(), ElabProblem>>>;

fn build_elab_ctx_from_scoped_defs(decls: Vec<ScopedDecl>) -> ElabEnv {
  let checakbles =
    decls
    .into_iter()
    .map(CheckableDecl::new)
    .collect();
  ElabEnv { defs: ScopedEnv { decls: checakbles }, postponed: VecDeque::new() }
}

fn check_env(ctx: &mut ElabEnv) -> Result<(), Vec<ElabProblem>> {
  let addr = addr_of_mut!(*ctx);
  let mut found_errs = Vec::new();
  for decl in &mut unsafe{&mut*addr}.defs.decls {
    let decl_inner = unsafe {&mut*decl.0.get()};
    if decl_inner.check_state == CheckState::Untouched {
      let outcome = check_def(unsafe{&mut*addr}, decl_inner.scoped_decl.index);
      match outcome {
        ElabResult::Stuck => (),
        ElabResult::Value(value) => {
          match value {
            Outcome::OneErr(err) => {
              found_errs.push(err)
            },
            Outcome::ManyErrs(errs) => {
              found_errs.extend(errs)
            },
            Outcome::Result(()) => {

            },
          }
        },
      }
    }
  }
  while let Some(work) = unsafe{&mut*addr}.postponed.pop_front() {
    let outcome = work(unsafe{&mut*addr});
    match outcome {
      ElabResult::Stuck => (),
      ElabResult::Value(value) => {
        match value {
          Outcome::OneErr(err) => {
            found_errs.push(err)
          },
          Outcome::ManyErrs(errs) => {
            found_errs.extend(errs)
          },
          Outcome::Result(()) => (),
        }
      },
    }
  }
  if !found_errs.is_empty() {
    return Err(found_errs);
  }
  return Ok(());
}

fn check_def(
  ctx: &mut ElabEnv,
  def_ix: DefId
) -> ElabResult<Outcome<(), ElabProblem>> {
  let def_ = unsafe { &mut*ctx.defs.decls.as_mut_ptr().add(def_ix.get_def_index())};
  let def = unsafe { &mut*def_.0.get()};
  let log_done = |e|{
    def_.log_elab_if_requested(|log|{
      let ok = if e { "success" } else { "failure" };
      write!(log, "Checking of {} has finished with {}", def.scoped_decl.name, ok).unwrap();
    })
  };
  match def.check_state {
    CheckState::Untouched => {
      def_.log_elab_if_requested(|log| {
        write!(log,
          "When checking def {} aka ",def.scoped_decl.name).unwrap();
        render_global_ix(log, def.scoped_decl.index)
      });
      def.check_state = CheckState::Began
    },
    CheckState::Began => {
      let ix = def_ix;
      let cont = Box::new(move |ctx:*mut ElabEnv|{
        let ctx = unsafe {&mut*ctx};
        let _ = check_def(ctx, ix)??;
        return emit!(());
      });
      ctx.postponed.push_back(cont);
      return ElabResult::Stuck;
    },
    CheckState::Ok => {
      log_done(true);
      return emit!(())
    },
    CheckState::Bad => {
      log_done(false);
      return emit!(())
    },
  }
  let mut inners = TCtx::new();
  let ty_term = def.scoped_decl.type_.shallow_clone();
  let () = check_inhabitance(
    ctx,
    ScopedTerm::new_from_repr(ScopedTermRepr::USort),
    ty_term.shallow_clone(),
    &mut inners,
    &mut TCtx::new(),
    def_ix)??;
  let val_term = def.scoped_decl.value.shallow_clone();
  let () = check_inhabitance(
    ctx,
    ty_term,
    val_term,
    &mut TCtx::new(),
    &mut inners,
    def_ix)??;
  def.check_state = CheckState::Ok;
  log_done(true);
  return emit!(());
}

#[derive(Debug, Clone)]
enum ElabProblem {
  String(String)
}

enum ElabResult<V> {
  Stuck,
  Value(V)
}
impl<T> core::ops::FromResidual for ElabResult<T> {
    fn from_residual((): <Self as std::ops::Try>::Residual) -> Self {
      ElabResult::Stuck
    }
}
impl<T, E> core::ops::FromResidual<Vec<E>> for ElabResult<Outcome<T, E>> {
    fn from_residual(residual: Vec<E>) -> Self {
        Self::Value(Outcome::ManyErrs(residual))
    }
}
impl <T> core::ops::Try for ElabResult<T> {
    type Output = T;
    type Residual = ();
    fn from_output(output: Self::Output) -> Self {
      Self::Value(output)
    }
    fn branch(self) -> std::ops::ControlFlow<Self::Residual, Self::Output> {
      match self {
        ElabResult::Stuck => std::ops::ControlFlow::Break(()),
        ElabResult::Value(val) => std::ops::ControlFlow::Continue(val),
      }
    }
}

fn elim_ref_to_global_def(
  ctx: &mut ElabEnv,
  id: DefId
) -> ElabResult<Outcome<&CheckableDecl, ElabProblem>> {
  let def_ = unsafe {&*ctx.defs.decls.as_ptr().add(id.get_def_index())};
  let def = unsafe {&mut*def_.0.get()};
  match def.check_state {
    CheckState::Untouched => {
      let chk = Box::new(|ctx:*mut ElabEnv|{
        let () = check_def(unsafe{&mut*ctx}, def.scoped_decl.index)??;
        let msg = format!("def {} is malformed", def.scoped_decl.name);
        return throw!(ElabProblem::String(msg));
      });
      ctx.postponed.push_back(chk);
      return ElabResult::Stuck;
    },
    CheckState::Began => return ElabResult::Stuck,
    CheckState::Ok => {
      return emit!(def_);
    },
    CheckState::Bad => {
      let msg = format!("def {} is malformed", def.scoped_decl.name);
      return throw!(ElabProblem::String(msg));
    },
  }
}
struct TCtx {
  items: Vec<TCtxEntry>
}
impl TCtx {
  fn new() -> Self {
    Self { items: Vec::new() }
  }
  fn append(&mut self, item: TCtxEntry) {
    self.items.push(item)
  }
  fn get(&self, index: SubstIndex) -> &TCtxEntry {
    self.items.get(index.get_index()).unwrap()
  }
}
impl Clone for TCtx {
  fn clone(&self) -> Self {
      Self { items: self.items.clone() }
  }
}
struct TCtxEntry {
  type_: ScopedTerm
}
impl Clone for TCtxEntry {
  fn clone(&self) -> Self {
      Self { type_: self.type_.shallow_clone() }
  }
}

fn check_inhabitance(
  ctx: &mut ElabEnv,
  space: ScopedTerm,
  resident: ScopedTerm,
  inner_variable_ty_assocs: &mut TCtx,
  outer_variable_ty_assocs: &mut TCtx,
  def_ix: DefId
) -> ElabResult<Outcome<(), ElabProblem>> {
  let def = &ctx.defs.decls[def_ix.get_def_index()];
  def.log_elab_if_requested(|log|{
    write!(log, "When checking that\n  ").unwrap();
    render_term_impl(log, &resident);
    write!(log, "\nis valid inhabitant of\n  ").unwrap();
    render_term_impl(log, &space);
  });
  let inhab_err = || {
    let msg = format!(
      "{} is not valid inhabitant of {}",
      render_term(&resident), render_term(&space));
    def.log_elab_if_requested(|log| log.write_str(&msg).unwrap());
    return msg;
  };
  match space.get_repr() {
    ScopedTermRepr::GlobalRef(ix) => {
      let def = elim_ref_to_global_def(ctx, *ix)??;
      let def = unsafe {&mut*def.0.get()};
      let new_space = &def.scoped_decl.value;
      space.assign_from(&new_space);
      return check_inhabitance(
        ctx, space, resident, inner_variable_ty_assocs,outer_variable_ty_assocs, def_ix);
    },
    ScopedTermRepr::Eval(h, a) => {
      let evaled = h;
      let () = elim_eval(ctx, None, evaled.shallow_clone(), a, inner_variable_ty_assocs)??;
      space.assign_from(&evaled);
      return check_inhabitance(
        ctx, space, resident, inner_variable_ty_assocs, outer_variable_ty_assocs,def_ix);
    },
    ScopedTermRepr::TypeUnit => {
      let repr = resident.get_repr();
      if let ScopedTermRepr::SubstRef(ix) = repr {
        let val = &inner_variable_ty_assocs.get(*ix).type_;
        if let ScopedTermRepr::TypeUnit = val.get_repr() {
          return emit!(());
        }
      }
      if let ScopedTermRepr::ValueUnit = repr {
        return emit!(());
      }
      if let ScopedTermRepr::SomePt = repr {
        resident.set_repr(ScopedTermRepr::ValueUnit);
        return emit!(());
      }
      let msg = inhab_err();
      return  throw!(ElabProblem::String(msg));
    }
    ScopedTermRepr::LetGroup(_, _) => todo!(),
    ScopedTermRepr::SubstRef(tsr) => {
      match resident.get_repr() {
        ScopedTermRepr::Eval(sh, a) => {
          let codo = check_args_for_app(
            ctx,
            sh.shallow_clone(),
            a,
            inner_variable_ty_assocs,
            outer_variable_ty_assocs,
            def_ix)??;
          let ty = outer_variable_ty_assocs.get(*tsr);
          return check_types_compatible(
            ctx,
            ty.type_.shallow_clone(),
            codo,
            outer_variable_ty_assocs,
            inner_variable_ty_assocs,
            def_ix);
        },
        ScopedTermRepr::GlobalRef(_) => todo!(),
        ScopedTermRepr::SubstRef(vsr) => {
          let st = outer_variable_ty_assocs.get(*tsr);
          let rt = inner_variable_ty_assocs.get(*vsr);
          return check_types_compatible(
            ctx,
            st.type_.shallow_clone(),
            rt.type_.shallow_clone(),
            outer_variable_ty_assocs,
            inner_variable_ty_assocs, def_ix);
        },
        ScopedTermRepr::AtomRef(_) => todo!(),
        ScopedTermRepr::Lift(_) => todo!(),
        ScopedTermRepr::Star => todo!(),
        ScopedTermRepr::LetGroup(_, _) => todo!(),
        ScopedTermRepr::Lambda(_) => todo!(),
        ScopedTermRepr::SomePt => todo!(),
        ScopedTermRepr::Void => todo!(),
        ScopedTermRepr::AtomApp(_, _) => todo!(),
        ScopedTermRepr::USort => todo!(),
        ScopedTermRepr::TypeUnit => todo!(),
        ScopedTermRepr::ValueUnit => todo!(),
        ScopedTermRepr::Unknown => todo!(),
      }
      // return check_types_compatible(
      //   ctx, space, r_ty, l_variable_ty_assocs, r_variable_ty_assocs, def_ix);
    },
    ScopedTermRepr::Lift(LiftNode(k, _, _, _)) => {
      match (k, resident.get_repr()) {
        (LiftKind::Arrow, ScopedTermRepr::Lambda(lambda)) => {
          return check_lambda(
            ctx, space, lambda,outer_variable_ty_assocs, inner_variable_ty_assocs, def_ix);
        },
        (LiftKind::And, ScopedTermRepr::AtomApp(Atom::TupleCtor, val_args)) => {
          let part = val_args.len() != 2;
          if part {
            let msg = inhab_err();
            return throw!(ElabProblem::String(msg))
          }
          todo!("algo has hit missing impl")
        },
        _ => {
          let msg = inhab_err();
          return throw!(ElabProblem::String(msg));
        }
      }
    },
    ScopedTermRepr::USort | ScopedTermRepr::Star => {
      match resident.get_repr() {
        ScopedTermRepr::Lift(LiftNode(_, decon, hd, sp)) => {
          // check well formdness of this thing
          check_inhabitance(
            ctx, space.shallow_clone(), hd.shallow_clone(),
            inner_variable_ty_assocs, outer_variable_ty_assocs, def_ix);
          pattern_can_deconstruct_value_of_type(
            ctx,decon, hd.shallow_clone(), outer_variable_ty_assocs,
            inner_variable_ty_assocs, def_ix);
          return check_inhabitance(
            ctx, space, sp.shallow_clone(),
            inner_variable_ty_assocs, outer_variable_ty_assocs, def_ix);
        },
        ScopedTermRepr::SomePt => {
          resident.assign_from(&ScopedTerm::new_from_repr(ScopedTermRepr::TypeUnit));
          return emit!(());
        }
        ScopedTermRepr::Star => {
          if let ScopedTermRepr::Star = space.get_repr() {
            return throw!(ElabProblem::String(inhab_err()));
          } else {
            return emit!(());
          }
        }
        ScopedTermRepr::TypeUnit |
        ScopedTermRepr::Void => return emit!(()),
        ScopedTermRepr::AtomApp(atom, val_args) => {
          match atom {
            Atom::And |
            Atom::Or |
            Atom::Arrow |
            Atom::Tilda => {
              if val_args.len() != 2 {
                let msg = inhab_err();
                return throw!(ElabProblem::String(msg));
              }
              let mut checks = Vec::new();
              for val_arg in val_args {
                let outcome = check_inhabitance(
                  ctx,
                  space.shallow_clone(),
                  val_arg.shallow_clone(),
                  inner_variable_ty_assocs,
                  outer_variable_ty_assocs,
                  def_ix)?;
                checks.push(outcome);
              }
              let _ = inside_out(&checks)?;
              return emit!(());
            },
            Atom::TupleCtor |
            Atom::Inl |
            Atom::Inr => {
              let msg = inhab_err();
              return throw!(ElabProblem::String(msg));
            },
          }
        },
        ScopedTermRepr::Unknown |
        ScopedTermRepr::ValueUnit |
        ScopedTermRepr::AtomRef(_) |
        ScopedTermRepr::Lambda(_) => {
          let msg = inhab_err();
          return throw!(ElabProblem::String(msg));
        },
        ScopedTermRepr::SubstRef(ix) => {
          let ty = &inner_variable_ty_assocs.get(*ix).type_;
          if let ScopedTermRepr::Star = ty.get_repr_mut() {
            return emit!(())
          } else {
            return throw!(ElabProblem::String(inhab_err()));
          }
        }
        ScopedTermRepr::Eval(h, a) => {
          let codo = check_args_for_app(
            ctx, h.shallow_clone(), a,
            inner_variable_ty_assocs,outer_variable_ty_assocs, def_ix)??;
          return check_inhabitance(
            ctx, space, codo,inner_variable_ty_assocs,outer_variable_ty_assocs, def_ix);
        },
        ScopedTermRepr::GlobalRef(gix)  => {
          let def = elim_ref_to_global_def(ctx, *gix)??;
          let def = unsafe {&mut*def.0.get()};
          resident.assign_from(&def.scoped_decl.value);
          return check_inhabitance(
            ctx, space, resident, inner_variable_ty_assocs,outer_variable_ty_assocs, def_ix)
        },
        ScopedTermRepr::LetGroup(_, _) => todo!(),
        ScopedTermRepr::USort => panic!("this shouldnt happen"),
      }
    },
    ScopedTermRepr::SomePt => {
      if let ScopedTermRepr::SomePt = resident.get_repr() {
        resident.assign_from(&ScopedTerm::new_from_repr(ScopedTermRepr::TypeUnit));
        resident.assign_from(&ScopedTerm::new_from_repr(ScopedTermRepr::ValueUnit));
        return emit!(());
      } else {
        let msg = inhab_err();
        return throw!(ElabProblem::String(msg));
      }
    },
    ScopedTermRepr::Void => {
      let msg = inhab_err();
      return throw!(ElabProblem::String(msg));
    }
    ScopedTermRepr::AtomApp(ty_atom, ty_args) => {
      match resident.get_repr() {
        ScopedTermRepr::AtomApp(val_atom, val_args) => {
          match (ty_atom, val_atom) {
            (Atom::TupleCtor, Atom::And) => {
              let l_ty = ty_args[0].shallow_clone();
              let l_v = val_args[0].shallow_clone();
              let () = check_inhabitance(
                ctx, l_ty, l_v, inner_variable_ty_assocs,outer_variable_ty_assocs, def_ix)??;
              let r_ty = ty_args[1].shallow_clone();
              let r_v = val_args[1].shallow_clone();
              let () = check_inhabitance(
                ctx, r_ty, r_v, inner_variable_ty_assocs, outer_variable_ty_assocs, def_ix)??;
              return emit!(());
            },
            (Atom::Or, Atom::Inl) => {
              let l_ty = ty_args[0].shallow_clone();
              let l_v = val_args[0].shallow_clone();
              return check_inhabitance(
                ctx, l_ty, l_v, inner_variable_ty_assocs, outer_variable_ty_assocs,def_ix);
            },
            (Atom::Or, Atom::Inr) => {
              let r_ty = ty_args[1].shallow_clone();
              let r_v = val_args[0].shallow_clone();
              return check_inhabitance(
                ctx, r_ty, r_v, inner_variable_ty_assocs, outer_variable_ty_assocs,def_ix);
            },
            _ => {
              let msg = inhab_err();
              return throw!(ElabProblem::String(msg));
            }
          }
        },
        ScopedTermRepr::Lambda(lambda) => {
          return check_lambda(
            ctx, space.shallow_clone(), lambda,
            outer_variable_ty_assocs,inner_variable_ty_assocs, def_ix);
        }
        ScopedTermRepr::Unknown |
        ScopedTermRepr::TypeUnit |
        ScopedTermRepr::ValueUnit |
        ScopedTermRepr::Lift(_) |
        ScopedTermRepr::Star |
        ScopedTermRepr::SomePt |
        ScopedTermRepr::AtomRef(_) |
        ScopedTermRepr::Void => {
          let msg = inhab_err();
          return throw!(ElabProblem::String(msg));
        },
        ScopedTermRepr::SubstRef(ix) => {
          let ty = inner_variable_ty_assocs.get(*ix).type_.shallow_clone();
          return check_types_compatible(
            ctx, space, ty, outer_variable_ty_assocs, inner_variable_ty_assocs, def_ix);
        }
        ScopedTermRepr::GlobalRef(gix) => {
          let def = elim_ref_to_global_def(ctx, *gix)??;
          let def = unsafe {&mut*def.0.get()};
          resident.assign_from(&def.scoped_decl.value);
          return check_inhabitance(
            ctx, space, resident, inner_variable_ty_assocs, outer_variable_ty_assocs,def_ix);
        }
        ScopedTermRepr::Eval(h, a) => {
          let codo = check_args_for_app(
            ctx, h.shallow_clone(), a,
            inner_variable_ty_assocs,outer_variable_ty_assocs, def_ix)??;
          return check_types_compatible(
            ctx, space, codo, inner_variable_ty_assocs, outer_variable_ty_assocs, def_ix);
        }
        ScopedTermRepr::LetGroup(_, _) => todo!(),
        ScopedTermRepr::USort => panic!("this shouldnt happen"),
      }
    }
    ScopedTermRepr::Unknown |
    ScopedTermRepr::ValueUnit |
    ScopedTermRepr::AtomRef(_) |
    ScopedTermRepr::Lambda(_) => {
      let msg = inhab_err();
      return throw!(ElabProblem::String(msg));
    },
  }
}


fn check_decons_against_arrow(
  ctx: &mut ElabEnv,
  arrow_ty_term: ScopedTerm,
  patterns: &[ThinPExpr],
  variable_ty_assocs: &mut TCtx,
  def_ix: DefId,
  arrow_scope_binds: &mut TCtx
) -> ElabResult<Outcome<ScopedTerm, ElabProblem>> {
  if patterns.is_empty() {
    return emit!(arrow_ty_term);
  }
  let def = ctx.get_def(def_ix);
  let invalid_term_err = || {
    let msg = format!("expected type, got {}", render_term(&arrow_ty_term));
    def.log_elab_if_requested(|log| log.write_str(&msg).unwrap());
    return msg;
  };
  match arrow_ty_term.get_repr_mut() {
    ScopedTermRepr::AtomApp(atom, ty_args) => {
      match atom {
        Atom::Arrow => {
          let arg = ty_args[0].shallow_clone();
          let pat = &patterns[0];
          pattern_can_deconstruct_value_of_type(
            ctx,pat, arg, arrow_scope_binds,variable_ty_assocs, def_ix)??;
          let tail = &patterns[1..];
          return check_decons_against_arrow(
            ctx, ty_args[1].shallow_clone(), tail, variable_ty_assocs, def_ix, arrow_scope_binds);
        },
        Atom::And |
        Atom::Or |
        Atom::Tilda |
        Atom::TupleCtor |
        Atom::Inl |
        Atom::Inr => {
          let msg = invalid_term_err();
          return throw!(ElabProblem::String(msg));
        },
      }
    },
    ScopedTermRepr::Unknown |
    ScopedTermRepr::TypeUnit |
    ScopedTermRepr::ValueUnit |
    ScopedTermRepr::AtomRef(_) |
    ScopedTermRepr::Lambda(_) => {
      let msg = invalid_term_err();
      return throw!(ElabProblem::String(msg));
    },
    ScopedTermRepr::Lift(_) |
    ScopedTermRepr::Star |
    ScopedTermRepr::SomePt |
    ScopedTermRepr::Void => {
      let msg = format!(
        "expected arrow term, got {:?}",
        arrow_ty_term.get_repr_mut());
      return throw!(ElabProblem::String(msg));
    },
    ScopedTermRepr::Eval(head, args) => {
      let cloned = head.shallow_clone();
      elim_eval(ctx, None, cloned.shallow_clone(), args, variable_ty_assocs)??;
      arrow_ty_term.assign_from(&cloned);
      return check_decons_against_arrow(
        ctx, arrow_ty_term, patterns, variable_ty_assocs, def_ix, arrow_scope_binds);
    }
    ScopedTermRepr::GlobalRef(id) => {
      let def = elim_ref_to_global_def(ctx, *id)??;
      let def = unsafe {&mut*def.0.get()};
      let ty = &def.scoped_decl.value;
      arrow_ty_term.assign_from(&ty);
      return check_decons_against_arrow(
        ctx, arrow_ty_term, patterns, variable_ty_assocs, def_ix, arrow_scope_binds);
    },
    ScopedTermRepr::LetGroup(_, _) => todo!(),
    ScopedTermRepr::SubstRef(ix) => {
      let ty = arrow_scope_binds.get(*ix).type_.shallow_clone();
      return check_decons_against_arrow(
        ctx, ty, patterns, variable_ty_assocs, def_ix, arrow_scope_binds);
    },
    ScopedTermRepr::USort => panic!("this shouldnt happen"),
  }
}

fn pattern_can_deconstruct_value_of_type(
  ctx: &mut ElabEnv,
  pattern: &ThinPExpr,
  ty_term: ScopedTerm,
  outer_binds: &mut TCtx,
  inner_binds: &mut TCtx,
  def_ix: DefId
) -> ElabResult<Outcome<(), ElabProblem>> {
  let def = ctx.get_def(def_ix);
  let build_err = || {
    let msg = format!(
      "{} is not valid deconstructor for {}",
      render_thin_pexpr(pattern), render_term(&ty_term));
    def.log_elab_if_requested(|log| log.write_str(&msg).unwrap());
    return msg;
  };
  match pattern {
    ThinPExpr::Discard => {
      if let ScopedTermRepr::Void = ty_term.get_repr_mut() {
        let msg = format!("Void does not have deconstructors");
        return throw!(ElabProblem::String(msg));
      }
      return emit!(());
    },
    ThinPExpr::Binder(_) => {
      if let ScopedTermRepr::Void = ty_term.get_repr_mut() {
        let msg = format!("Void does not have deconstructors");
        return throw!(ElabProblem::String(msg));
      }
      let entry = TCtxEntry {
        type_: ty_term
      };
      inner_binds.append(entry);
      return emit!(());
    },
    ThinPExpr::Group(atom, sub_pats) => {
      match atom {
        Atom::Tilda | Atom::Arrow | Atom::And | Atom::Or => {
          if let ScopedTermRepr::Star = ty_term.get_repr_mut() {
            for sub_pat in sub_pats {
              let () = pattern_can_deconstruct_value_of_type(
                ctx,
                sub_pat,
                ty_term.shallow_clone(),
                outer_binds,
                inner_binds,
                def_ix)??;
            }
            return emit!(());
          } else {
            let msg = build_err();
            return throw!(ElabProblem::String(msg));
          }
        },
        Atom::TupleCtor => {
          if let ScopedTermRepr::AtomApp(Atom::And, ty_args) = ty_term.get_repr_mut() {
            for (sub_pat, ty_arg) in zip(sub_pats, ty_args) {
              let () = pattern_can_deconstruct_value_of_type(
                ctx,
                sub_pat,
                ty_arg.shallow_clone(),
                outer_binds,
                inner_binds,
                def_ix)??;
            }
            return emit!(());
          } else {
            let msg = build_err();
            return throw!(ElabProblem::String(msg));
          }
        },
        Atom::Inl => {
          if let ScopedTermRepr::AtomApp(Atom::Or, ty_args) = ty_term.get_repr_mut() {
            return pattern_can_deconstruct_value_of_type(
              ctx,
              &sub_pats[0],
              ty_args[0].shallow_clone(),
              outer_binds,
              inner_binds,
              def_ix);
          } else {
            let msg = build_err();
            return throw!(ElabProblem::String(msg));
          }
        },
        Atom::Inr => {
          if let ScopedTermRepr::AtomApp(Atom::Or, ty_args) = ty_term.get_repr_mut() {
            return pattern_can_deconstruct_value_of_type(
              ctx,
              &sub_pats[1],
              ty_args[1].shallow_clone(),
              outer_binds,
              inner_binds,
              def_ix);
          } else {
            let msg = build_err();
            return throw!(ElabProblem::String(msg));
          }
        },
      }
    },
    ThinPExpr::Pt => {
      if let ScopedTermRepr::SomePt = ty_term.get_repr_mut() {
        return emit!(());
      }
      let msg = build_err();
      return throw!(ElabProblem::String(msg));
    },
  }
}

fn elim_eval(
  ctx: &mut ElabEnv,
  dir_ty_term: Option<ScopedTerm>,
  head: ScopedTerm,
  args: &Vec<ScopedTerm>,
  variable_ty_assocs: &TCtx
) -> ElabResult<Outcome<(), ElabProblem>> {
  match head.get_repr_mut() {
    ScopedTermRepr::Eval(subhead, subargs) => {
      let cloned = subhead.shallow_clone();
      let () = elim_eval(ctx, None, cloned.shallow_clone(), subargs, variable_ty_assocs)??;
      head.assign_from(&cloned);
      return elim_eval(ctx, dir_ty_term, head, args, variable_ty_assocs);
    },
    ScopedTermRepr::GlobalRef(def_id) => {
      let def = unsafe {&mut*ctx.defs.decls.as_mut_ptr().add(def_id.get_def_index())};
      let def = unsafe {&mut*def.0.get()};
      match def.check_state {
        CheckState::Untouched => {
          // charge check of unchecked def
          let check = Box::new(move |ctx:*mut ElabEnv|{
            let () = check_def(unsafe{&mut*ctx}, def.scoped_decl.index)??;
            return emit!(());
          });
          ctx.postponed.push_back(check);
          // recheck
          let dir_ty = match dir_ty_term {
            Some(dir_ty) => Some(dir_ty.shallow_clone()),
            None => None,
          };
          let head = head.shallow_clone();
          let args: Vec<_> = args.iter().map(|e|e.shallow_clone()).collect();
          let c = variable_ty_assocs.clone();
          let continuation = Box::new(move |ctx:*mut ElabEnv| {
            elim_eval(unsafe{&mut*ctx}, dir_ty, head, &args, &c)
          });
          ctx.postponed.push_back(continuation);
          return ElabResult::Stuck;
        },
        CheckState::Began => return ElabResult::Stuck,
        CheckState::Ok => {
          let val = &def.scoped_decl.value;
          head.assign_from(&val);
          let ty = def.scoped_decl.type_.shallow_clone();
          return elim_eval(ctx, Some(ty), head, args, variable_ty_assocs);
        },
        CheckState::Bad => {
          let msg = format!("cant continue becase of bad def {}", def.scoped_decl.name);
          return throw!(ElabProblem::String(msg))
        },
      }
    },
    ScopedTermRepr::SubstRef(_) => {
      todo!("??")
    },
    ScopedTermRepr::AtomRef(atom) => {
      let arg_lim = atom.arg_limit();
      if args.len() > arg_lim {
        let msg = format!(
          "invalid app to\n  {}\n\n of\n\n  {}",
          render_term(&head), render_args(args));
        return throw!(ElabProblem::String(msg))
      }
      let repr = ScopedTermRepr::AtomApp(*atom, args.iter().map(|e|e.shallow_clone()).collect());
      head.set_repr(repr);
      return emit!(());
    },
    ScopedTermRepr::LetGroup(_, _) => {
      // need to get result from let block
      todo!()
    },
    ScopedTermRepr::Lambda(lambda) => {
      let dir_ty_term = match dir_ty_term {
        Some(dt) => dt,
        None => {
          // synth plain type from lambda def
          todo!()
        },
      };

      let thing = apply(ctx, lambda, args, variable_ty_assocs)??;
      head.assign_from(&thing);
      return emit!(());
    },
    ScopedTermRepr::Unknown |
    ScopedTermRepr::TypeUnit |
    ScopedTermRepr::ValueUnit |
    ScopedTermRepr::Void |
    ScopedTermRepr::Lift(_) |
    ScopedTermRepr::Star |
    ScopedTermRepr::SomePt => {
      let msg = format!("{:?} is not a valid head", head.get_repr_mut());
      return throw!(ElabProblem::String(msg));
    },
    ScopedTermRepr::AtomApp(atom, present_args) => {
      let arg_limit = atom.arg_limit();
      if present_args.len() + args.len() > arg_limit {
        let msg = format!("invalid app {:?} {:?}", head.get_repr_mut(), args);
        return throw!(ElabProblem::String(msg))
      }
      let mut args_:Vec<_> = present_args.iter().map(|e|e.shallow_clone()).collect();
      for arg in args {
        args_.push(arg.shallow_clone())
      }
      return emit!(());
    }
    ScopedTermRepr::USort => panic!("this shouldnt happen"),
  }
}

fn apply(
  ctx: &mut ElabEnv,
  lambda: &Lambda,
  args: &Vec<ScopedTerm>,
  variable_ty_assocs: &TCtx
) -> ElabResult<Outcome<ScopedTerm, ElabProblem>> {

  let Lambda(clauses) = lambda;
  let mut bind_store = Vec::new();
  let mut matched = None;
  'clause_matching:for (decontructors, rhs) in clauses {
    let mut ok = true;
    for (decon, arg) in zip(decontructors, args) {
      let () = bind_values(
        ctx, &mut ok, &mut bind_store, decon, arg.shallow_clone(), variable_ty_assocs)??;
      if !ok {
        bind_store.clear();
        continue 'clause_matching;
      }
    }
    matched = Some(rhs); break 'clause_matching;
  }
  let Some(rhs) = matched else {
    let msg = format!(
      "lambda did not match arguments!!\nLambda\n\n{}\nArgs\n\n{}",
      render_lambda(lambda), render_args(args));
    return throw!(ElabProblem::String(msg));
  };
  let mut clone = rhs.deep_lazy_clone();
  fill(&bind_store, &mut clone);
  return emit!(clone);
}

fn fill(
  bind_store: &Vec<ScopedTerm>,
  template_term: &mut ScopedTerm
) {
  match template_term.get_repr_mut() {
    ScopedTermRepr::Eval(h, args) => {
      fill(bind_store, h);
      for arg in args {
        fill(bind_store, arg);
      }
    },
    ScopedTermRepr::GlobalRef(_) => {
      ()
    },
    ScopedTermRepr::SubstRef(ix) => {
      let subst = &bind_store[ix.get_index()];
      *template_term = subst.shallow_clone();
    },
    ScopedTermRepr::AtomRef(_) => {
      ()
    },
    ScopedTermRepr::Lift(LiftNode(_, _, ty, spine)) => {
      fill(bind_store, ty);
      fill(bind_store, spine);
    },
    ScopedTermRepr::Star => {
      ()
    },
    ScopedTermRepr::LetGroup(l, r) => {
      for (_, ty, val) in l {
        fill(bind_store, ty);
        fill(bind_store, val);
      }
      fill(bind_store, r);
    },
    ScopedTermRepr::Lambda(Lambda(clauses)) => {
      for (_, rhs) in clauses {
        fill(bind_store, rhs);
      }
    },
    ScopedTermRepr::SomePt => {
      ()
    },
    ScopedTermRepr::Void => {
      ()
    },
    ScopedTermRepr::AtomApp(_, args) => {
      for arg in args {
        fill(bind_store, arg);
      }
    },
    ScopedTermRepr::TypeUnit => (),
    ScopedTermRepr::ValueUnit => (),
    ScopedTermRepr::USort => panic!("this shouldnt happen"),
    ScopedTermRepr::Unknown => (),
  }
}

fn bind_values(
  ctx: &mut ElabEnv,
  ok: &mut bool,
  bind_store: &mut Vec<ScopedTerm>,
  pattern: &ThinPExpr,
  arg: ScopedTerm,
  variable_ty_assocs: &TCtx
) -> ElabResult<Outcome<(), ElabProblem>> {
  if !*ok { return emit!(()) }
  match (pattern, arg.get_repr_mut()) {
    (ThinPExpr::Discard, _) => emit!(()),
    (ThinPExpr::Binder(_), _) => {
      bind_store.push(arg.shallow_clone());
      emit!(())
    },
    (_, ScopedTermRepr::Eval(head, args)) => {
      let evaled = head.shallow_clone();
      let () = elim_eval(ctx, None, evaled.shallow_clone(), args, variable_ty_assocs)??;
      arg.assign_from(&evaled);
      return bind_values(ctx, ok, bind_store, pattern, evaled.shallow_clone(), variable_ty_assocs);
    },
    (_, ScopedTermRepr::LetGroup(_, _)) => todo!(),
    (_, ScopedTermRepr::GlobalRef(id)) => {
      let def = elim_ref_to_global_def(ctx, *id)??;
      let def = unsafe {&mut*def.0.get()};
      let val = &def.scoped_decl.value;
      arg.assign_from(&val);
      return bind_values(ctx, ok, bind_store, pattern, arg, variable_ty_assocs);
    },
    (ThinPExpr::Group(_, _), ScopedTermRepr::Star) => {
      panic!("this shouldnt happen")
    }
    (ThinPExpr::Group(_, _), ScopedTermRepr::Lambda(_)) |
    (ThinPExpr::Group(_, _), ScopedTermRepr::SomePt) |
    (ThinPExpr::Group(_, _), ScopedTermRepr::Void) |
    (ThinPExpr::Group(_, _), ScopedTermRepr::SubstRef(_)) |
    (ThinPExpr::Group(_, _), ScopedTermRepr::Lift(_)) |
    (ThinPExpr::Group(_, _), ScopedTermRepr::AtomRef(_)) => {
      return emit!(());
    },
    (ThinPExpr::Group(pattern_atom, subpats), ScopedTermRepr::AtomApp(ctor_atom, subvals)) => {
      if pattern_atom != ctor_atom {
        *ok = false;
        return emit!(());
      }
      for (subpat, subval) in zip(subpats, subvals) {
        let () = bind_values(
          ctx, ok, bind_store, subpat, subval.shallow_clone(), variable_ty_assocs)??;
        if !*ok { return emit!(()) }
      }
      return emit!(());
    },
    (ThinPExpr::Pt, ScopedTermRepr::SomePt) => {
      return emit!(());
    },
    (ThinPExpr::Pt, ScopedTermRepr::SubstRef(_)) |
    (ThinPExpr::Pt, ScopedTermRepr::AtomRef(_)) |
    (ThinPExpr::Pt, ScopedTermRepr::Lift(_)) |
    (ThinPExpr::Pt, ScopedTermRepr::Star) => {
      panic!("this shouldnt happen")
    }
    (ThinPExpr::Pt, ScopedTermRepr::TypeUnit) |
    (ThinPExpr::Pt, ScopedTermRepr::ValueUnit) |
    (ThinPExpr::Pt, ScopedTermRepr::Lambda(_)) |
    (ThinPExpr::Pt, ScopedTermRepr::Void) |
    (ThinPExpr::Pt, ScopedTermRepr::AtomApp(_, _)) => {
      return emit!(());
    },
    (ThinPExpr::Group(_, _), ScopedTermRepr::TypeUnit) |
    (ThinPExpr::Group(_, _), ScopedTermRepr::ValueUnit) |
    (ThinPExpr::Group(_, _), ScopedTermRepr::Unknown) |
    (ThinPExpr::Pt, ScopedTermRepr::Unknown) |
    (ThinPExpr::Group(_, _), ScopedTermRepr::USort) |
    (ThinPExpr::Pt, ScopedTermRepr::USort) => panic!("this shouldnt happen"),

  }
}

fn check_args_for_app(
  ctx: &mut ElabEnv,
  head: ScopedTerm,
  args: &[ScopedTerm],
  inner_variable_ty_assocs: &mut TCtx,
  outer_variable_ty_assocs: &mut TCtx,
  def_ix: DefId,
) -> ElabResult<Outcome<ScopedTerm, ElabProblem>> {
  let def = ctx.get_def(def_ix);
  def.log_elab_if_requested(|log|{
    log.write_str("When checking application of\n  ").unwrap();
    render_args_impl(log, args);
    log.write_str("\nto head term\n  ").unwrap();
    render_term_impl(log, &head);
  });
  match head.get_repr() {
    ScopedTermRepr::Eval(sh, sa) => {
      let codo = check_args_for_app(
        ctx, sh.shallow_clone(), sa, inner_variable_ty_assocs, outer_variable_ty_assocs, def_ix)??;
      return check_args_for_app(
        ctx, codo, args, inner_variable_ty_assocs, outer_variable_ty_assocs, def_ix);
    },
    ScopedTermRepr::GlobalRef(ix) => {
      let def = elim_ref_to_global_def(ctx, *ix)??;
      let def = unsafe {&mut*def.0.get()};
      let ty = def.scoped_decl.type_.shallow_clone();
      return check_args_against_arrow_ty(
        ctx, ty, args, inner_variable_ty_assocs, outer_variable_ty_assocs,def_ix);
    },
    ScopedTermRepr::SubstRef(_) => todo!(),
    ScopedTermRepr::AtomRef(_) => todo!(),
    ScopedTermRepr::Lift(_) => todo!(),
    ScopedTermRepr::Star => todo!(),
    ScopedTermRepr::LetGroup(_, _) => todo!(),
    ScopedTermRepr::Lambda(_) => todo!(),
    ScopedTermRepr::SomePt => todo!(),
    ScopedTermRepr::Void => todo!(),
    ScopedTermRepr::AtomApp(_, _) => todo!(),
    ScopedTermRepr::USort => todo!(),
    ScopedTermRepr::TypeUnit => todo!(),
    ScopedTermRepr::ValueUnit => todo!(),
    ScopedTermRepr::Unknown => todo!(),
  }
}
/// returns codo type
fn check_args_against_arrow_ty(
  ctx: &mut ElabEnv,
  arrow_ty: ScopedTerm,
  args: &[ScopedTerm],
  value_bindings: &mut TCtx,
  arrow_level_binds: &mut TCtx,
  def_ix: DefId
) -> ElabResult<Outcome<ScopedTerm, ElabProblem>>{
  if args.is_empty() {
    return emit!(arrow_ty);
  }
  let def = ctx.get_def(def_ix);
  def.log_elab_if_requested(|log|{
    log.write_str("When checking application to\n  ").unwrap();
    render_term_impl(log,&arrow_ty);
    log.write_str("\nof args\n  ").unwrap();
    write!(log, "{:?}", args).unwrap();
  });
  match arrow_ty.get_repr_mut() {
    ScopedTermRepr::AtomApp(atom, aps) => {
      match atom {
        Atom::Arrow => {
          let ty = aps[0].shallow_clone();
          let arg = args[0].shallow_clone();
          let ty = if let ScopedTermRepr::Star = ty.get_repr_mut() {
            ScopedTerm::new_from_repr(ScopedTermRepr::USort)
          } else { ty };
          let () = check_inhabitance(
            ctx, ty, arg, value_bindings, arrow_level_binds, def_ix)??;
          let tys = aps[1].shallow_clone();
          let args = &args[1..];
          return check_args_against_arrow_ty(
            ctx, tys, args, value_bindings, arrow_level_binds, def_ix);
        },
        Atom::And |
        Atom::Or |
        Atom::Tilda |
        Atom::TupleCtor |
        Atom::Inl |
        Atom::Inr => todo!(),
      }
    },
    ScopedTermRepr::Lift(_) => {
      // instantiate types (we'd need lazy clone here)
      //
      todo!()
    },
    ScopedTermRepr::Eval(_, _) => todo!(),
    ScopedTermRepr::GlobalRef(_) => todo!(),
    ScopedTermRepr::SubstRef(_) => todo!(),
    ScopedTermRepr::AtomRef(_) => todo!(),
    ScopedTermRepr::Star => todo!(),
    ScopedTermRepr::LetGroup(_, _) => todo!(),
    ScopedTermRepr::Lambda(_) => todo!(),
    ScopedTermRepr::SomePt => todo!(),
    ScopedTermRepr::Void => todo!(),
    ScopedTermRepr::USort => todo!(),
    ScopedTermRepr::TypeUnit => todo!(),
    ScopedTermRepr::ValueUnit => todo!(),
    ScopedTermRepr::Unknown => todo!(),
  }
}
fn check_types_compatible(
  ctx: &mut ElabEnv,
  l_ty: ScopedTerm,
  r_ty: ScopedTerm,
  l_variable_ty_assocs: &mut TCtx,
  r_variable_ty_assocs: &mut TCtx,
  def_ix: DefId
) -> ElabResult<Outcome<(), ElabProblem>> {
  let def = ctx.get_def(def_ix);
  def.log_elab_if_requested(|log|{
    log.write_str("When checking compatibility of type\n  ").unwrap();
    render_term_impl(log, &l_ty);
    log.write_str("\nwith type\n  ").unwrap();
    render_term_impl(log, &r_ty);
  });
  let type_comp_error = || {
    let msg = format!("{} is not compatible with {}", render_term(&l_ty), render_term(&l_ty));
    def.log_elab_if_requested(|log| log.write_str(&msg).unwrap());
    return msg;
  };
  match (l_ty.get_repr(), r_ty.get_repr()) {
    (_, ScopedTermRepr::Eval(h, a)) => {
      let evaled = h;
      let () = elim_eval(ctx, None, h.shallow_clone(), a, l_variable_ty_assocs)??;
      r_ty.assign_from(&evaled);
      return check_types_compatible(
        ctx, l_ty, r_ty, l_variable_ty_assocs, r_variable_ty_assocs,def_ix)
    },
    (ScopedTermRepr::Eval(h, a), _) => {
      let evaled = h;
      let () = elim_eval(ctx, None, h.shallow_clone(), a, l_variable_ty_assocs)??;
      l_ty.assign_from(&evaled);
      return check_types_compatible(
        ctx, l_ty, r_ty, l_variable_ty_assocs, r_variable_ty_assocs, def_ix)
    },
    (_, ScopedTermRepr::GlobalRef(id)) => {
      let def = elim_ref_to_global_def(ctx, *id)??;
      let def = unsafe {&mut*def.0.get()};
      r_ty.assign_from(&def.scoped_decl.value);
      return check_types_compatible(
        ctx, l_ty, r_ty, l_variable_ty_assocs,r_variable_ty_assocs, def_ix);
    },
    (ScopedTermRepr::GlobalRef(id), _) => {
      let def = elim_ref_to_global_def(ctx, *id)??;
      let def = unsafe {&mut*def.0.get()};
      l_ty.assign_from(&def.scoped_decl.value);
      return check_types_compatible(
        ctx, l_ty, r_ty, l_variable_ty_assocs, r_variable_ty_assocs, def_ix);
    },
    (ScopedTermRepr::LetGroup(_, _), _) => todo!(),
    (_, ScopedTermRepr::LetGroup(_, _)) => todo!(),

    (_, ScopedTermRepr::SubstRef(rix)) => {
      let r_ty = &r_variable_ty_assocs.get(*rix).type_;
      return check_types_compatible(
        ctx, l_ty, r_ty.shallow_clone(), l_variable_ty_assocs, r_variable_ty_assocs, def_ix);
    },
    (ScopedTermRepr::SubstRef(lix), _) => {
      let l_ty = &l_variable_ty_assocs.get(*lix).type_;
      return check_types_compatible(
        ctx, l_ty.shallow_clone(), r_ty, l_variable_ty_assocs, r_variable_ty_assocs, def_ix);
    },
    (ScopedTermRepr::AtomRef(l), ScopedTermRepr::AtomRef(r)) => {
      if l != r {
        return throw!(ElabProblem::String(type_comp_error()));
      } else {
        return emit!(());
      }
    },
    (ScopedTermRepr::Lift(_), _) => {
      // I dont know how to guarantee if two lifts are compatible
      todo!()
    },
    (ScopedTermRepr::TypeUnit, ScopedTermRepr::TypeUnit) |
    (ScopedTermRepr::Void, ScopedTermRepr::Void) |
    (ScopedTermRepr::Star, ScopedTermRepr::Star) => {
      return emit!(());
    },
    (ScopedTermRepr::AtomApp(l, largs), ScopedTermRepr::AtomApp(r, rargs)) => {
      if l != r { return throw!(ElabProblem::String(type_comp_error())); }
      for (la, ra) in zip(largs, rargs) {
        check_types_compatible(
          ctx, la.shallow_clone(), ra.shallow_clone(),
          l_variable_ty_assocs, r_variable_ty_assocs, def_ix)??
      }
      return emit!(());
    },
    (ScopedTermRepr::Star, _) |
    (_, ScopedTermRepr::Lambda(_)) |
    (ScopedTermRepr::Lambda(_), _) |
    (ScopedTermRepr::AtomApp(_, _), _) |
    (ScopedTermRepr::Void, _) |
    (ScopedTermRepr::TypeUnit, _) |
    (ScopedTermRepr::AtomRef(_), _) => {
      let msg = type_comp_error();
      return throw!(ElabProblem::String(msg));
    },
    (ScopedTermRepr::SomePt, _) |
    (ScopedTermRepr::ValueUnit, _) |
    (ScopedTermRepr::USort, _) => unreachable!(),
    (ScopedTermRepr::Unknown, _) => todo!(),
  }
}

fn check_lambda(
  ctx: &mut ElabEnv,
  lift: ScopedTerm,
  lambda: &Lambda,
  outer_level_binds: &mut TCtx,
  inner_level_binds: &mut TCtx,
  def_ix: DefId
) -> ElabResult<Outcome<(), ElabProblem>> {
  let Lambda(clauses) = lambda;
  let clause_len = clauses[0].0.len();
  for (pexprs, rhs) in clauses {
    if clause_len != pexprs.len() {
      let mut str = String::new();
      for d in pexprs {
        render_thin_pexpr_impl(&mut str, d)
      }
      let msg = format!(
        "Different pattern count in clauses in lambda\n{}\nexpected {}, got {}\noffender clause\n{}",
        render_lambda(lambda), clause_len, pexprs.len(), str);
      return throw!(ElabProblem::String(msg));
    }
    let mut openers = Vec::new();
    let codo = recurse_dependent_clauses(
      ctx, lift.shallow_clone(), pexprs, &mut openers,
      outer_level_binds, inner_level_binds, def_ix)??;
    let repr = codo.get_repr();
    if let ScopedTermRepr::Star = repr {
      check_inhabitance(
          ctx,
          ScopedTerm::new_from_repr(ScopedTermRepr::USort),
          rhs.shallow_clone(),
          inner_level_binds,
          outer_level_binds,
          def_ix)??;
    } else {
      check_inhabitance(
          ctx,
          codo.shallow_clone(),
          rhs.shallow_clone(),
          inner_level_binds,
          outer_level_binds,
          def_ix)??;
    }
  }
  return emit!(());
}
fn recurse_dependent_clauses(
  ctx: &mut ElabEnv,
  dep_arrow_ty: ScopedTerm,
  patterns: &[ThinPExpr],
  openers: &mut Vec<ScopedTerm>,
  outer_bindings: &mut TCtx,
  inner_bindings: &mut TCtx,
  def_ix: DefId
) -> ElabResult<Outcome<ScopedTerm, ElabProblem>> {
  if patterns.is_empty() {
    return emit!(dep_arrow_ty);
  }
  let err_msg = || {
    let msg = format!("Invalid functional {:?}", dep_arrow_ty);
    return msg;
  };
  match dep_arrow_ty.get_repr() {
    ScopedTermRepr::Eval(h, a) => { // argument we need to try to open
      todo!()
    },
    ScopedTermRepr::GlobalRef(gix) => {
      let decl = elim_ref_to_global_def(ctx, *gix)??;
      let val = decl.get_value();
      dep_arrow_ty.assign_from(&val);
      return recurse_dependent_clauses(
        ctx, dep_arrow_ty, patterns, openers, outer_bindings, inner_bindings, def_ix);
    },
    ScopedTermRepr::Lift(LiftNode(_, p, ty, s)) => {
      check_inhabitance(
        ctx,
        ScopedTerm::new_from_repr(ScopedTermRepr::USort),
        ty.shallow_clone(),
        inner_bindings,
        outer_bindings,
        def_ix)??;
      pattern_can_deconstruct_value_of_type(
        ctx, p, ty.shallow_clone(), outer_bindings, inner_bindings, def_ix)??;
      let pattern = &patterns[0];
      pattern_can_deconstruct_value_of_type(
        ctx, pattern, ty.shallow_clone(), outer_bindings, inner_bindings, def_ix)??;

      let opener = build_term_from_pat(pattern);
      openers.push(opener);
      return recurse_dependent_clauses(
        ctx, s.shallow_clone(), &patterns[1..], openers, outer_bindings, inner_bindings, def_ix);
    },
    ScopedTermRepr::AtomApp(atom, args) => {
      match atom {
        Atom::Arrow => {
          let pattern = &patterns[0];
          let arg = args[0].shallow_clone();
          pattern_can_deconstruct_value_of_type(
            ctx, pattern, arg, outer_bindings,inner_bindings, def_ix)??;
          return recurse_dependent_clauses(
            ctx, args[1].shallow_clone(), &patterns[1..],
            openers, outer_bindings, inner_bindings, def_ix);
        }
        Atom::And |
        Atom::Or |
        Atom::Tilda |
        Atom::TupleCtor |
        Atom::Inl |
        Atom::Inr => {
          return throw!(ElabProblem::String(err_msg()));
        },
      }
    }
    ScopedTermRepr::AtomRef(_) |
    ScopedTermRepr::SubstRef(_) => todo!(),
    ScopedTermRepr::LetGroup(_, _) => todo!(),
    ScopedTermRepr::Star |
    ScopedTermRepr::Lambda(_) |
    ScopedTermRepr::SomePt |
    ScopedTermRepr::Void |
    ScopedTermRepr::USort |
    ScopedTermRepr::TypeUnit |
    ScopedTermRepr::ValueUnit |
    ScopedTermRepr::Unknown => {
      return throw!(ElabProblem::String(err_msg()));
    },
  }
}

fn build_term_from_pat(
  pattern: &ThinPExpr
) -> ScopedTerm {
  match pattern {
    ThinPExpr::Discard |
    ThinPExpr::Binder(_) => ScopedTerm::new_from_repr(ScopedTermRepr::Unknown),
    ThinPExpr::Group(atom, args) => {
      ScopedTerm::new_from_repr(
        ScopedTermRepr::AtomApp(*atom, args.iter().map(build_term_from_pat).collect()))
    },
    ThinPExpr::Pt => ScopedTerm::new_from_repr(ScopedTermRepr::SomePt),
  }
}

#[test] #[ignore]
fn checker_basic_sanch() {
  let mut str =
    "".to_string() +
    "B : * = () or ();" +
    "m : (T:*) -> T -> T = { _,v => v };" +
    "k1 : (T:*) -> T -> T = { T, v => m T v }" +
    ""
  ;
  pad_string(&mut str);
  let mut p = SourceTextParser::new(str.as_bytes());
  let defs = p.parse_to_end();
  match defs {
    Ok(defs) => {
      let mut ctx = ScopeCheckCtx::new(str.as_bytes());
      let decls = scope_check_decls(&mut ctx, &defs);
      match decls {
        Ok(decls) => {
          let mut ctx = build_elab_ctx_from_scoped_defs(decls);
          let outcome = check_env(&mut ctx);
          let def = unsafe{&*ctx.defs.decls[2].0.get()};
          let log = def.elab_trace.as_ref().unwrap();
          println!("{}", log);
          // println!("{} {}", def.scoped_decl.type_, def.scoped_decl.value);
          match outcome {
            Ok(( )) => println!("horaaayy!"),
            Err(errs) => {
              println!("ugh {:#?}", errs)
            },
        }
        },
        Err(err) => {
          println!("scoping failed\n{:#?}", err)
        },
      }
    },
    Err(err) => {
      println!("hell {:#?}", err)
    },
  }
}