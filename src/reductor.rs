use std::any::Any;

use crate::{parser::{AtomRef, LiftKind, RefinedPExpr}, lexer::CharsData};


#[derive(Debug, Clone)]
pub enum TypeCheckerTExpr {
  App(Box<Self>, Vec<Self>),
  Ref(CharsData),
  AtomRef(AtomRef),
  Lift(LiftKind, RefinedPExpr, Box<Self>, Box<Self>),
  Star,
  Let(Vec<(RefinedPExpr, Self)>, Box<Self>),
  Lambda(Vec<(Vec<RefinedPExpr>, Self)>),
  Pt,
  Void,

  Meta
}

enum ReductionError {
  InvalidRef(String)
}
struct ReductionCtx {

}
type Maybe<T> = Result<T, Box<dyn Any>>;
fn rewrite(
  ctx: &mut ReductionCtx,
  obj: &TypeCheckerTExpr
) -> TypeCheckerTExpr {
  match obj {
    TypeCheckerTExpr::App(_, _) => todo!(),
    TypeCheckerTExpr::Ref(_) => todo!(),
    TypeCheckerTExpr::AtomRef(_) => todo!(),
    TypeCheckerTExpr::Lift(_, _, _, _) => todo!(),
    TypeCheckerTExpr::Star => todo!(),
    TypeCheckerTExpr::Let(_, _) => todo!(),
    TypeCheckerTExpr::Lambda(_) => todo!(),
    TypeCheckerTExpr::Pt => todo!(),
    TypeCheckerTExpr::Void => todo!(),
    TypeCheckerTExpr::Meta => todo!(),
  }
}
fn substitute() -> Maybe<()> {
  todo!()
}
fn bind() -> Maybe<()> {
  todo!()
}