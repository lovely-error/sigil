use std::{any::Any, mem::size_of, simd::u8x4};

use crate::{lexer::{CharsData, RawPExpr, RawTExpr, Lift, LetGroup, Lambda, Clause, SourceTextParser, RawDecl, Letters}, root_alloc::RootAllocator, sema::get_name};



#[derive(Debug, Clone)]
pub enum RefinedPExpr {
  Discard,
  Ref(CharsData),
  AtomRef(AtomRef),
  Group(Box<Self>, Vec<Self>),
  Pt
}
#[derive(Debug, Clone, Copy)]
pub enum PrecedenceResolutionError {
  OrderError
}

type Maybe<R> = Result<R, PrecedenceResolutionError>;
fn resolve_pexpr(inp: &[u8], pexpr: &RawPExpr) -> Maybe<RefinedPExpr> {
  match pexpr {
    RawPExpr::HeadTuple => Ok(RefinedPExpr::AtomRef(AtomRef::TupleCtor)),
    RawPExpr::Tuple(l, r) => {
      let l = resolve_pexpr(inp, l)?;
      let r = resolve_pexpr(inp, r)?;
      let expr = RefinedPExpr::Group(
        Box::new(RefinedPExpr::AtomRef(AtomRef::TupleCtor)),
        [l,r].to_vec());
      return Ok(expr)
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
fn resolve_pexprs(inp: &[u8], pexprs:&[RawPExpr]) -> Maybe<RefinedPExpr> {
  let len = pexprs.len();
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
          let expr = RefinedPExpr::Group(
            Box::new(RefinedPExpr::AtomRef(AtomRef::Arrow)),
            [left, right].to_vec());
          return Ok(expr)
        },
        _ => return Err(PrecedenceResolutionError::OrderError)
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
          let expr = RefinedPExpr::Group(
            Box::new(RefinedPExpr::AtomRef(AtomRef::Tilda)),
            [left, right].to_vec());
          return Ok(expr)
        },
        _ => return Err(PrecedenceResolutionError::OrderError)
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
          let expr = RefinedPExpr::Group(
            Box::new(RefinedPExpr::AtomRef(AtomRef::Or)),
            [left, right].to_vec());
          return Ok(expr)
        },
        _ => return Err(PrecedenceResolutionError::OrderError)
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
          let expr = RefinedPExpr::Group(
            Box::new(RefinedPExpr::AtomRef(AtomRef::And)),
            [left, right].to_vec());
          return Ok(expr)
        },
        _ => return Err(PrecedenceResolutionError::OrderError)
      }
    }
    ix += 1;
  };
  return resolve_app_pexpr(inp, pexprs)
}
fn resolve_app_pexpr(inp: &[u8], pexpr: &[RawPExpr]) -> Maybe<RefinedPExpr> {
  let head = resolve_pexpr(inp, &pexpr[0])?;
  let mut args = Vec::new();
  for item in &pexpr[1..] {
    args.push(resolve_pexpr(inp, item)?)
  }
  return Ok(RefinedPExpr::Group(Box::new(head), args))
}
#[derive(Debug, Clone, Copy)]
pub enum LiftKind {
  Arrow, And
}
#[derive(Debug, Clone)]
pub enum PrecedenceResolvedTExpr {
  App(Box<Self>, Vec<Self>),
  Ref(CharsData),
  AtomRef(AtomRef),
  Lift(LiftKind, RefinedPExpr, Box<Self>, Box<Self>),
  Star,
  Let(Vec<(RefinedPExpr, Self, Self)>, Box<Self>),
  Lambda(Vec<(Vec<RefinedPExpr>, Self)>),
  Pt,
  Void,
}
#[derive(Debug, Clone, Copy)]
pub enum AtomRef { And, Or, Arrow, Tilda, TupleCtor, Inl, Inr }

pub fn resolve_precendece(
  inp: &[u8],
  texpr: &RawTExpr
) -> Maybe<PrecedenceResolvedTExpr> {
  return resolve_singular(inp,texpr)
}

fn split_tokens(
  inp: &[u8],
  tokens: &[RawTExpr]
) -> Maybe<PrecedenceResolvedTExpr> {
  let end_index = tokens.len();
  if end_index == 0 {
    return Err(PrecedenceResolutionError::OrderError);
  }
  if end_index == 1 {
    return resolve_singular(inp,&tokens[0])
  }
  let mut index = 0;
  while index != end_index {
    let item = &tokens[index];
    // lifts has highest precedence
    if let RawTExpr::Lift(lift) = item {
      let Some(next_item) = tokens.get(index + 1) else {
        return Err(PrecedenceResolutionError::OrderError)
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
                PrecedenceResolvedTExpr::Lift(
                  LiftKind::And, rpexpr, Box::new(head), Box::new(tail)))
            },
            RawTExpr::Arrow => {
              return Ok(
                PrecedenceResolvedTExpr::Lift(
                  LiftKind::Arrow, rpexpr, Box::new(head), Box::new(tail)))
            },
            _ => unreachable!()
          }
        },
        _ => {
          return Err(PrecedenceResolutionError::OrderError);
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
          let expr = PrecedenceResolvedTExpr::App(
            Box::new(PrecedenceResolvedTExpr::AtomRef(AtomRef::Arrow)),
            [left_part, right_part].to_vec());
          return Ok(expr)
        },
        (true, false) => {
          return resolve_app(inp,tokens)
        },
        (true, true) => {
          return resolve_singular(inp,item)
        },
        _ => return Err(PrecedenceResolutionError::OrderError)
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
          let expr = PrecedenceResolvedTExpr::App(
            Box::new(PrecedenceResolvedTExpr::AtomRef(AtomRef::Tilda)),
            [left_part, right_part].to_vec());
          return Ok(expr)
        },
        (true, false) => {
          return resolve_app(inp,tokens)
        },
        (true, true) => {
          return resolve_singular(inp, item)
        },
        _ => return Err(PrecedenceResolutionError::OrderError)
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
          let expr = PrecedenceResolvedTExpr::App(
            Box::new(PrecedenceResolvedTExpr::AtomRef(AtomRef::Or)),
            [left_part, right_part].to_vec());
          return Ok(expr)
        },
        (true, false) => {
          return resolve_app(inp,tokens)
        },
        (true, true) => {
          return resolve_singular(inp,item)
        },
        _ => return Err(PrecedenceResolutionError::OrderError)
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
          let expr = PrecedenceResolvedTExpr::App(
            Box::new(PrecedenceResolvedTExpr::AtomRef(AtomRef::And)),
            [left_part, right_part].to_vec());
          return Ok(expr)
        },
        (true, false) => {
          return resolve_app(inp,tokens)
        },
        (true, true) => {
          return resolve_singular(inp,item)
        },
        _ => return Err(PrecedenceResolutionError::OrderError)
      }
    }
    index += 1
  }
  // the computation should have diverged by this point if it has matched any builtins operators.
  // if it didnt then this tokens seqv is an application
  return resolve_app(inp, tokens)
}
fn resolve_app(
  inp: &[u8],
  tokens: &[RawTExpr]
) -> Maybe<PrecedenceResolvedTExpr> {
  let head = resolve_singular(inp,&tokens[0])?;
  let mut args = Vec::new();
  for token in &tokens[1..] {
    let checked = resolve_singular(inp, token)?;
    args.push(checked)
  }
  return Ok(PrecedenceResolvedTExpr::App(Box::new(head), args));
}
fn resolve_singular(
  inp: &[u8],
  texpr: &RawTExpr
) -> Maybe<PrecedenceResolvedTExpr> {
  match texpr {
    RawTExpr::Tuple(l,r) => {
      let l = resolve_singular(inp, l.as_ref())?;
      let r = resolve_singular(inp, r.as_ref())?;
      let expr =
        PrecedenceResolvedTExpr::App(
          Box::new(PrecedenceResolvedTExpr::AtomRef(AtomRef::TupleCtor)),
          [l,r].to_vec());
      return Ok(expr)
    }
    RawTExpr::TupleCtor => {
      return Ok(PrecedenceResolvedTExpr::AtomRef(AtomRef::TupleCtor))
    }
    RawTExpr::Chars(chars) => {
      let name = get_name(inp, chars);
      match name {
        "inl" => {
          return Ok(PrecedenceResolvedTExpr::AtomRef(AtomRef::Inl));
        },
        "inr" => {
          return Ok(PrecedenceResolvedTExpr::AtomRef(AtomRef::Inr));
        },
        _ => return Ok(PrecedenceResolvedTExpr::Ref(*chars))
      }
    },
    RawTExpr::Tokens(tokens) => return split_tokens(inp, tokens),
    RawTExpr::Lift(_) => return Err(PrecedenceResolutionError::OrderError),
    RawTExpr::Let(let_) => {
      let LetGroup(items, focus) = let_.as_ref();
      let mut items_ = Vec::new();
      for (pexpr, texpr, oexpr) in items {
        let pexpr = resolve_pexpr(inp, pexpr)?;
        let texpr = resolve_precendece(inp, texpr)?;
        let oexpr = resolve_precendece(inp,oexpr)?;
        items_.push((pexpr, texpr, oexpr));
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
    RawTExpr::EMark => return Ok(PrecedenceResolvedTExpr::Void),
  }
}


#[test] #[ignore]
fn precedenter_tests() {
  let s =
    "".to_string() +
    "k : () -> ! = k (->) (-> * *) (* *) (,) (and b) ~ d ({ -> a b => (a,b), (,) a b => a and b } a)"
    ;
  let mut parser = SourceTextParser::new(s.as_bytes());
  let expr = parser.parse_top_level_decl();
  match expr {
    Err(err) => println!("{:?}", err),
    Ok(RawDecl(name, tyexpr, oexpr)) => {
      let pred_tyexpr = resolve_precendece(s.as_bytes(),&tyexpr);
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
    "k : * -> * = { (,) a b, () => -> a b }"
    ;
  let mut parser = SourceTextParser::new(s.as_bytes());
  let expr = parser.parse_top_level_decl();
  match expr {
    Err(err) => println!("{:?}", err),
    Ok(RawDecl(name, tyexpr, oexpr)) => {
      let pred_tyexpr = resolve_precendece(s.as_bytes(),&oexpr);
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
fn precedenter_tests3() {
  let s =
    "".to_string() +
    "k : * = (a : * = (->) a => (a : *) -> p a)"
    ;
  let mut parser = SourceTextParser::new(s.as_bytes());
  let expr = parser.parse_top_level_decl();
  match expr {
    Err(err) => println!("{:?}", err),
    Ok(RawDecl(name, tyexpr, oexpr)) => {
      let pred_tyexpr = resolve_precendece(s.as_bytes(),&oexpr);
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
fn precedenter_tests4() {
  let s =
    "".to_string() +
    "N : * = () or N"
    ;
  let mut parser = SourceTextParser::new(s.as_bytes());
  let expr = parser.parse_top_level_decl();
  match expr {
    Err(err) => println!("{:?}", err),
    Ok(RawDecl(name, tyexpr, oexpr)) => {
      let pred_tyexpr = resolve_precendece(s.as_bytes(),&oexpr);
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
fn top_decls() {
  let mut s =
    "".to_string() +
    "N : * = () or N" +
    ""
    ;
  for _ in s.len() .. (s.len().next_multiple_of(size_of::<u8x4>())) {
    s.push(Letters::EOT as char)
  }
  let mut parser = SourceTextParser::new(s.as_bytes());
  let decl1 = parser.parse_to_end();
  match decl1 {
    Ok(val) => println!("{:#?}", val),
    Err(err) => println!("{:#?}", err),
}
}