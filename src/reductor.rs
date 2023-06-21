use std::any::Any;

use crate::parser::PrecedenceResolvedTExpr;


enum ReductionError {
  InvalidRef(String)
}
struct ReductionCtx {

}
type Maybe<T> = Result<T, Box<dyn Any>>;
fn realise(
  ctx: &mut ReductionCtx,
  obj: &PrecedenceResolvedTExpr
) -> PrecedenceResolvedTExpr {
  match obj {
    PrecedenceResolvedTExpr::App(head, args) => {
      todo!()
    },
    PrecedenceResolvedTExpr::Ref(_) => {
      todo!()
    },
    PrecedenceResolvedTExpr::AtomRef(_) => todo!(),
    PrecedenceResolvedTExpr::Arrow(_, _) => todo!(),
    PrecedenceResolvedTExpr::DArrow(_, _, _) => todo!(),
    PrecedenceResolvedTExpr::And(_, _) => todo!(),
    PrecedenceResolvedTExpr::DAnd(_, _, _) => todo!(),
    PrecedenceResolvedTExpr::Or(_, _) => todo!(),
    PrecedenceResolvedTExpr::Star => todo!(),
    PrecedenceResolvedTExpr::Let(_, _) => todo!(),
    PrecedenceResolvedTExpr::Lambda(_) => todo!(),
    PrecedenceResolvedTExpr::Tilda(_, _) => todo!(),
    PrecedenceResolvedTExpr::Tuple(_, _) => todo!(),
    PrecedenceResolvedTExpr::Pt => todo!(),
    PrecedenceResolvedTExpr::Void => todo!(),
    PrecedenceResolvedTExpr::Inl(_) => todo!(),
    PrecedenceResolvedTExpr::Inr(_) => todo!(),
  }
}
fn substitute() -> Maybe<()> {
  todo!()
}