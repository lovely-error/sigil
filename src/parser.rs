use std::any::Any;

use crate::{lexer::{CharsData, RawPExpr, RawTExpr, Lift, LetGroup, Lambda, Clause, SourceTextParser, RawDecl}, root_alloc::RootAllocator, sema::get_name};



#[derive(Debug, Clone)]
pub enum RefinedPExpr {
  Discard,
  Ref(CharsData),
  And(Box<Self>, Box<Self>),
  Or(Box<Self>, Box<Self>),
  Inl(Box<Self>),
  Inr(Box<Self>),
  Tuple(Box<Self>, Box<Self>),
  Arrow(Box<Self>, Box<Self>),
  Tilda(Box<Self>, Box<Self>),
  AtomRef(AtomRef),
  Group(Box<Self>, Vec<Self>),
  Pt
}

struct NameResolutionError;
type Maybe<R> = Result<R, Box<dyn Any>>;
fn resolve_pexpr(inp: &String, pexpr: &RawPExpr) -> Maybe<RefinedPExpr> {
  match pexpr {
    RawPExpr::HeadTuple => Ok(RefinedPExpr::AtomRef(AtomRef::TupleCtor)),
    RawPExpr::Tuple(l, r) => {
      let l = resolve_pexpr(inp, l)?;
      let r = resolve_pexpr(inp, r)?;
      return Ok(RefinedPExpr::Tuple(Box::new(l), Box::new(r)))
    },
    RawPExpr::Discard => Ok(RefinedPExpr::Discard),
    RawPExpr::Chars(chars) => {
      Ok(RefinedPExpr::Ref(*chars))
    },
    RawPExpr::Seqv(toks) => {
      return resolve_pexprs(inp, toks)
    },
    RawPExpr::Arrow => Ok(RefinedPExpr::AtomRef(AtomRef::Arrow)),
    RawPExpr::Tilda => Ok(RefinedPExpr::AtomRef(AtomRef::Tilda)),
    RawPExpr::Or => Ok(RefinedPExpr::AtomRef(AtomRef::Or)),
    RawPExpr::And => Ok(RefinedPExpr::AtomRef(AtomRef::And)),
    RawPExpr::Pt => Ok(RefinedPExpr::Pt),
  }
}
fn resolve_pexprs(inp: &String, pexprs:&[RawPExpr]) -> Maybe<RefinedPExpr> {
  let len = pexprs.len();
  if len == 0 { return Err(Box::new(NameResolutionError)) }
  if len == 1 { return resolve_pexpr(inp, &pexprs[0]) }
  let mut ix = 0 ;
  while ix != len {
    let item = &pexprs[ix];
    if let RawPExpr::Arrow = item {
      let left = &pexprs[..ix];
      let right = &pexprs[ix + 1 ..];
      match (left.is_empty(), right.is_empty()) {
        (true, false) => return resolve_app_pexpr(inp, pexprs),
        (false, false) => {
          let left = resolve_pexprs(inp, left)?;
          let right = resolve_pexprs(inp, right)?;
          let box_ = |e| Box::new(e);
          return Ok(RefinedPExpr::Arrow(box_(left), box_(right)))
        },
        _ => return Err(Box::new(NameResolutionError))
      }
    }
    if let RawPExpr::Tilda = item {
      let left = &pexprs[..ix];
      let right = &pexprs[ix + 1 ..];
      match (left.is_empty(), right.is_empty()) {
        (true, false) => return resolve_app_pexpr(inp, pexprs),
        (false, false) => {
          let left = resolve_pexprs(inp, left)?;
          let right = resolve_pexprs(inp, right)?;
          let box_ = |e| Box::new(e);
          return Ok(RefinedPExpr::Tilda(box_(left), box_(right)))
        },
        _ => return Err(Box::new(NameResolutionError))
      }
    }
    if let RawPExpr::Or = item {
      let left = &pexprs[..ix];
      let right = &pexprs[ix + 1 ..];
      match (left.is_empty(), right.is_empty()) {
        (true, false) => return resolve_app_pexpr(inp, pexprs),
        (false, false) => {
          let left = resolve_pexprs(inp, left)?;
          let right = resolve_pexprs(inp, right)?;
          let box_ = |e| Box::new(e);
          return Ok(RefinedPExpr::Or(box_(left), box_(right)))
        },
        _ => return Err(Box::new(NameResolutionError))
      }
    }
    if let RawPExpr::And = item {
      let left = &pexprs[..ix];
      let right = &pexprs[ix + 1 ..];
      match (left.is_empty(), right.is_empty()) {
        (true, false) => return resolve_app_pexpr(inp, pexprs),
        (false, false) => {
          let left = resolve_pexprs(inp, left)?;
          let right = resolve_pexprs(inp, right)?;
          let box_ = |e| Box::new(e);
          return Ok(RefinedPExpr::And(box_(left), box_(right)))
        },
        _ => return Err(Box::new(NameResolutionError))
      }
    }
    ix += 1;
  };
  return resolve_app_pexpr(inp, pexprs)
}
fn resolve_app_pexpr(inp: &String,pexpr: &[RawPExpr]) -> Maybe<RefinedPExpr> {
  let head = resolve_pexpr(inp, &pexpr[0])?;
  let mut args = Vec::new();
  for item in &pexpr[1..] {
    args.push(resolve_pexpr(inp, item)?)
  }
  return Ok(RefinedPExpr::Group(Box::new(head), args))
}

#[derive(Debug)]
pub enum PrecedenceResolvedTExpr {
  App(Box<Self>, Vec<Self>),
  Ref(CharsData),
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
  Tuple(Box<Self>, Box<Self>),
  Pt,
  Void,
  Inl(Box<Self>),
  Inr(Box<Self>)
}
#[derive(Debug, Clone, Copy)]
pub enum AtomRef { And, Or, Arrow, Tilda, TupleCtor, Inl, Inr }

pub fn resolve_precendece(
  inp: &String,
  texpr: &RawTExpr
) -> Maybe<PrecedenceResolvedTExpr> {
  return resolve_singular(inp,texpr)
}
pub struct PrecedenceResolutionError;
fn split_tokens(
  inp: &String,
  tokens: &[RawTExpr]
) -> Maybe<PrecedenceResolvedTExpr> {
  let end_index = tokens.len();
  if end_index == 0 { return Err(Box::new(PrecedenceResolutionError)) }
  if end_index == 1 {
    return resolve_singular(inp,&tokens[0])
  }
  let mut index = 0;
  while index != end_index {
    let item = &tokens[index];
    // lifts has highest precedence
    if let RawTExpr::Lift(lift) = item {
      let Some(next_item) = tokens.get(index + 1) else {
        return Err(Box::new(PrecedenceResolutionError))
      };
      match next_item {
        arm@(RawTExpr::And | RawTExpr::Arrow) => {
          let Lift(pexpr, texpr) = lift.as_ref();
          let head = resolve_precendece(inp, texpr)?;
          let tail = split_tokens(inp, &tokens[index + 2 ..])?;
          let rpexpr = resolve_pexpr(inp, pexpr)?;
          match arm {
            RawTExpr::And => {
              return Ok(
                PrecedenceResolvedTExpr::DAnd(
                  rpexpr, Box::new(head), Box::new(tail)))
            },
            RawTExpr::Arrow => {
              return Ok(
                PrecedenceResolvedTExpr::DArrow(
                  rpexpr, Box::new(head), Box::new(tail)))
            },
            _ => unreachable!()
          }
        },
        _ => {
          return Err(Box::new(PrecedenceResolutionError));
        }
      }
    }
    // then go regular arrows
    if let RawTExpr::Arrow = item {
      let left_tokens = &tokens[..index];
      let right_tokens = &tokens[index + 1 ..];
      match (left_tokens.is_empty(), right_tokens.is_empty()) {
        (false, false) => {
          let left_part = split_tokens(inp, left_tokens)?;
          let right_part = split_tokens(inp, right_tokens)?;
          return Ok(PrecedenceResolvedTExpr::Arrow(Box::new(left_part), Box::new(right_part)))
        },
        (true, false) => {
          return resolve_app(inp,tokens)
        },
        (true, true) => {
          return resolve_singular(inp,item)
        },
        _ => return Err(Box::new(PrecedenceResolutionError))
      }
    }
    // then equiv
    if let RawTExpr::Tilda = item {
      let left_tokens = &tokens[..index];
      let right_tokens = &tokens[index + 1 ..];
      match (left_tokens.is_empty(), right_tokens.is_empty()) {
        (false, false) => {
          let left_part = split_tokens(inp, left_tokens)?;
          let right_part = split_tokens(inp, right_tokens)?;
          return Ok(PrecedenceResolvedTExpr::Tilda(Box::new(left_part), Box::new(right_part)))
        },
        (true, false) => {
          return resolve_app(inp,tokens)
        },
        (true, true) => {
          return resolve_singular(inp, item)
        },
        _ => return Err(Box::new(PrecedenceResolutionError))
      }
    }
    // then ors
    if let RawTExpr::Or = item {
      let left_tokens = &tokens[..index];
      let right_tokens = &tokens[index + 1 ..];
      match (left_tokens.is_empty(), right_tokens.is_empty()) {
        (false, false) => {
          let left_part = split_tokens(inp, left_tokens)?;
          let right_part = split_tokens(inp, right_tokens)?;
          return Ok(PrecedenceResolvedTExpr::Or(Box::new(left_part), Box::new(right_part)))
        },
        (true, false) => {
          return resolve_app(inp,tokens)
        },
        (true, true) => {
          return resolve_singular(inp,item)
        },
        _ => return Err(Box::new(PrecedenceResolutionError))
      }
    }
    // then ands
    if let RawTExpr::And = item {
      let left_tokens = &tokens[..index];
      let right_tokens = &tokens[index + 1 ..];
      match (left_tokens.is_empty(), right_tokens.is_empty()) {
        (false, false) => {
          let left_part = split_tokens(inp, left_tokens)?;
          let right_part = split_tokens(inp, right_tokens)?;
          return Ok(PrecedenceResolvedTExpr::And(Box::new(left_part), Box::new(right_part)))
        },
        (true, false) => {
          return resolve_app(inp,tokens)
        },
        (true, true) => {
          return resolve_singular(inp,item)
        },
        _ => return Err(Box::new(PrecedenceResolutionError))
      }
    }
    index += 1
  }
  // the computation should have diverged by this point if it has matched any builtins operators.
  // if it didnt then this tokens seqv is an application
  return resolve_app(inp, tokens)
}
fn resolve_app(
  inp: &String,
  tokens: &[RawTExpr]
) -> Maybe<PrecedenceResolvedTExpr> {
  let head = resolve_precendece(inp,&tokens[0])?;
  let mut args = Vec::new();
  for token in &tokens[1..] {
    let checked = resolve_singular(inp, token)?;
    args.push(checked)
  }
  return Ok(PrecedenceResolvedTExpr::App(Box::new(head), args));
}
fn resolve_singular(
  inp: &String,
  texpr: &RawTExpr
) -> Maybe<PrecedenceResolvedTExpr> {
  match texpr {
    RawTExpr::Tuple(l,r) => {
      let l = resolve_singular(inp, l.as_ref())?;
      let r = resolve_singular(inp, r.as_ref())?;
      return Ok(PrecedenceResolvedTExpr::Tuple(Box::new(l), Box::new(r)))
    }
    RawTExpr::TupleCtor => {
      return Ok(PrecedenceResolvedTExpr::AtomRef(AtomRef::TupleCtor))
    }
    RawTExpr::Chars(chars) => {
      let name = get_name(inp, chars);
      match name {
        "inl" => {
          return Ok(PrecedenceResolvedTExpr::AtomRef(AtomRef::Inl));
        }
        _ => return Ok(PrecedenceResolvedTExpr::Ref(*chars))
      }
    },
    RawTExpr::Tokens(tokens) => return split_tokens(inp, tokens),
    RawTExpr::Lift(_) => return Err(Box::new(PrecedenceResolutionError)),
    RawTExpr::Let(let_) => {
      let LetGroup(items, focus) = let_.as_ref();
      let mut items_ = Vec::new();
      for (pexpr, texpr) in items {
        let texpr = resolve_precendece(inp,texpr)?;
        let pexpr = resolve_pexpr(inp, pexpr)?;
        items_.push((pexpr, texpr));
      }
      let focus = resolve_precendece(inp,focus)?;
      return Ok(PrecedenceResolvedTExpr::Let(items_, Box::new(focus)))
    },
    RawTExpr::Lambda(Lambda(clauses)) => {
      let mut vec = Vec::new();
      for Clause(patterns, rhs) in clauses {
        let rhs = resolve_precendece(inp,rhs)?;
        let mut rpats = Vec::new();
        for item in patterns {
          let pexpr = resolve_pexpr(inp, item)?;
          rpats.push(pexpr)
        }
        vec.push((rpats, rhs));
      }
      return Ok(PrecedenceResolvedTExpr::Lambda(vec))
    },
    RawTExpr::Arrow => return Ok(PrecedenceResolvedTExpr::AtomRef(AtomRef::Arrow)),
    RawTExpr::Tilda => return Ok(PrecedenceResolvedTExpr::AtomRef(AtomRef::Tilda)),
    RawTExpr::Star => return Ok(PrecedenceResolvedTExpr::Star),
    RawTExpr::Or => return Ok(PrecedenceResolvedTExpr::AtomRef(AtomRef::Or)),
    RawTExpr::And =>  return Ok(PrecedenceResolvedTExpr::AtomRef(AtomRef::And)),
    RawTExpr::Pt => return Ok(PrecedenceResolvedTExpr::Pt),
    RawTExpr::QMark => return Ok(PrecedenceResolvedTExpr::Void),
  }
}


#[test] #[ignore]
fn precedenter_tests() {
  let s =
    "".to_string() +
    "k : () -> ! = k (->) (-> * *) (* *) (,) (and b) ~ d ({ -> a b => (a,b), (,) a b => a and b } a)"
    ;
  let mut parser = SourceTextParser::new(&s);
  let expr = parser.parse_top_level_decl();
  match expr {
    Err(err) => println!("{:?}", err),
    Ok(RawDecl(name, tyexpr, oexpr)) => {
      let pred_tyexpr = resolve_precendece(&parser.chars,&tyexpr);
      match pred_tyexpr {
        Err(_) => println!("fuck"),
        Ok(expr) => {
          println!("{:#?}", expr)
        }
      }
    }
  }
}

#[test] #[ignore]
fn precedenter_tests2() {
  let s =
    "".to_string() +
    "k : * -> * = { (,) a b, () => a (a,b) }"
    ;
  let mut parser = SourceTextParser::new(&s);
  let expr = parser.parse_top_level_decl();
  match expr {
    Err(err) => println!("{:?}", err),
    Ok(RawDecl(name, tyexpr, oexpr)) => {
      let pred_tyexpr = resolve_precendece(&parser.chars,&oexpr);
      match pred_tyexpr {
        Err(_) => println!("fuck"),
        Ok(expr) => {
          println!("{:#?}", expr)
        }
      }
    }
  }
}