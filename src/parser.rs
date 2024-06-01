use std::{any::Any, mem::size_of, simd::u8x4, collections::HashMap};

use crate::{lexer::{CharsData, RawPExpr, RawTExpr, Lift, LetGroup, Lambda, Clause, SourceTextParser, RawDecl, Letters, pad_string, InfixOp}, root_alloc::RootAllocator, sema::get_name};



#[derive(Debug, Clone)]
pub enum RefinedPExpr {
  Discard,
  Binder(CharsData),
  Group(Atom, Vec<Self>),
  Pt
}
#[derive(Debug, Clone, Copy)]
pub enum PrecedenceResolutionFailure {
  OrderError, InfixOpSplitFailed
}
type Maybe<R> = Result<R, PrecedenceResolutionFailure>;
fn resolve_pexpr(
  inp: &[u8],
  pexpr: &RawPExpr,
) -> Maybe<RefinedPExpr> {
  match pexpr {
    RawPExpr::Tuple(l, r) => {
      let l = resolve_pexpr(inp, l)?;
      let r = resolve_pexpr(inp, r)?;
      let expr = RefinedPExpr::Group(
        Atom::TupleCtor,
        [l,r].to_vec());
      return Ok(expr)
    },
    RawPExpr::Discard => Ok(RefinedPExpr::Discard),
    RawPExpr::Chars(chars) => {
      Ok(RefinedPExpr::Binder(*chars))
    },
    RawPExpr::Seqv(toks) => {
      return resolve_pexprs(inp, toks)
    },
    RawPExpr::Pt => Ok(RefinedPExpr::Pt),
    RawPExpr::HeadTuple |
    RawPExpr::Arrow |
    RawPExpr::Tilda |
    RawPExpr::Or |
    RawPExpr::And => return Err(PrecedenceResolutionFailure::OrderError),
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
            Atom::Arrow,
            [left, right].to_vec());
          return Ok(expr)
        },
        _ => return Err(PrecedenceResolutionFailure::OrderError)
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
            Atom::Tilda,
            [left, right].to_vec());
          return Ok(expr)
        },
        _ => return Err(PrecedenceResolutionFailure::OrderError)
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
            Atom::Or,
            [left, right].to_vec());
          return Ok(expr)
        },
        _ => return Err(PrecedenceResolutionFailure::OrderError)
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
            Atom::And,
            [left, right].to_vec());
          return Ok(expr)
        },
        _ => return Err(PrecedenceResolutionFailure::OrderError)
      }
    }
    ix += 1;
  };
  return resolve_app_pexpr(inp, pexprs)
}
fn resolve_app_pexpr(inp: &[u8], pexpr: &[RawPExpr]) -> Maybe<RefinedPExpr> {
  let mut args = Vec::new();
  for item in &pexpr[1..] {
    args.push(resolve_pexpr(inp, item)?)
  }
  let head = &pexpr[0];
  let head = match head {
    RawPExpr::Arrow => Atom::Arrow,
    RawPExpr::Tilda => Atom::Tilda,
    RawPExpr::Or => Atom::Or,
    RawPExpr::And => Atom::And,
    RawPExpr::HeadTuple => Atom::TupleCtor,
    RawPExpr::Chars(cd) => {
      let name = get_name(inp, cd);
      match name {
        "inl" => Atom::Inl,
        "inr" => Atom::Inr,
        _ => return Err(PrecedenceResolutionFailure::OrderError)
      }
    },
    _ => return Err(PrecedenceResolutionFailure::OrderError)
  };
  return Ok(RefinedPExpr::Group(head, args))
}

#[derive(Debug, Clone)]
pub enum PrecedenceResolvedTExpr {
  App(Box<Self>, Vec<Self>),
  Ref(CharsData),
  AtomRef(Atom),
  Sigma {
    binder: RefinedPExpr,
    head: Box<Self>,
    tail: Box<Self>
  },
  Pi {
    binder: RefinedPExpr,
    head: Box<Self>,
    tail: Box<Self>
  },
  Star,
  Let(Vec<(RefinedPExpr, Self, Self)>, Box<Self>),
  Lambda(Vec<(Vec<RefinedPExpr>, Self)>),
  Pt,
  Void,
}
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Atom { And, Or, Arrow, Tilda, TupleCtor, Inl, Inr }
impl Atom {
  pub fn arg_limit(&self) -> usize {
    match self {
        Atom::And |
        Atom::Or |
        Atom::Arrow |
        Atom::Tilda |
        Atom::TupleCtor => 2,
        Atom::Inl |
        Atom::Inr => 1,
      }
  }
}

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
    return Err(PrecedenceResolutionFailure::OrderError);
  }
  if end_index == 1 {
    return resolve_singular(inp,&tokens[0])
  }
  let mut index = 0;
  let item = tokens.get(index);
  loop {
    if let RawTExpr::Lift(lift) = item.unwrap() {
      let Lift(pexpr, texpr) = lift.as_ref();
      let head = resolve_precendece(inp, texpr)?;
      let tail = split_tokens(inp, &tokens[index + 2 ..])?;
      let rpexpr = resolve_pexpr(inp, pexpr)?;
      let Some(next_item) = tokens.get(index + 1) else {
        return Err(PrecedenceResolutionFailure::OrderError)
      };
      match next_item {
        RawTExpr::InfixOp(infop) => {
          match infop {
            InfixOp::And => return Ok(
              PrecedenceResolvedTExpr::Sigma {
                binder: rpexpr,
                head: Box::new(head),
                tail: Box::new(tail),
              }),
            InfixOp::Arrow => return Ok(
              PrecedenceResolvedTExpr::Pi {
                binder: rpexpr,
                head: Box::new(head),
                tail: Box::new(tail),
            }),
            InfixOp::Or |
            InfixOp::Tilda => return Err(PrecedenceResolutionFailure::OrderError),
          }
        },
        _ => {
          return Err(PrecedenceResolutionFailure::OrderError);
        }
      }
    }
    index += 1;
    if index == end_index { break }
  }
  for op in [
    (InfixOp::Arrow, Atom::Arrow),
    (InfixOp::Or, Atom::Or),
    (InfixOp::And, Atom::And),
    (InfixOp::Tilda, Atom::Tilda),
  ] {
    let outcome = traverse_token_seqv(inp, op.0, op.1, tokens);
    match &outcome {
      Ok(_) => return outcome,
      Err(err) => {
        match err {
          PrecedenceResolutionFailure::OrderError => return outcome,
          PrecedenceResolutionFailure::InfixOpSplitFailed => (),
        }
      },
    }
  };
  // the computation should have diverged by this point if it has matched any builtins operators.
  // if it didnt then this tokens seqv is an application
  return resolve_app(inp, tokens)
}
fn traverse_token_seqv(
  inp: &[u8],
  infop: InfixOp,
  atom: Atom,
  tokens: &[RawTExpr],
) -> Maybe<PrecedenceResolvedTExpr> {
  let mut pivot_index = 0;
  loop {
    let Some(item) = tokens.get(pivot_index) else { break };
    if let RawTExpr::InfixOp(infop_) = item {
      if *infop_ != infop { pivot_index += 1; continue; }
      let left_tokens = &tokens[.. pivot_index];
      let right_tokens = &tokens[pivot_index + 1 ..];
      match (left_tokens.is_empty(), right_tokens.is_empty()) {
        (false, false) => {
          let left_part = split_tokens(inp, left_tokens)?;
          let right_part = split_tokens(inp, right_tokens)?;
          let expr = PrecedenceResolvedTExpr::App(
            Box::new(PrecedenceResolvedTExpr::AtomRef(atom)),
            [left_part, right_part].to_vec());
          return Ok(expr)
        },
        (true, false) => {
          return resolve_app(inp,tokens)
        },
        (true, true) => {
          return resolve_singular(inp,item)
        },
        _ => return Err(PrecedenceResolutionFailure::OrderError)
      }
    }
    pivot_index += 1;
  };
  return Err(PrecedenceResolutionFailure::InfixOpSplitFailed);
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
          Box::new(PrecedenceResolvedTExpr::AtomRef(Atom::TupleCtor)),
          [l,r].to_vec());
      return Ok(expr)
    }
    RawTExpr::TupleCtor => {
      return Ok(PrecedenceResolvedTExpr::AtomRef(Atom::TupleCtor))
    }
    RawTExpr::Chars(chars) => {
      let name = get_name(inp, chars);
      match name {
        "inl" => {
          return Ok(PrecedenceResolvedTExpr::AtomRef(Atom::Inl));
        },
        "inr" => {
          return Ok(PrecedenceResolvedTExpr::AtomRef(Atom::Inr));
        },
        _ => return Ok(PrecedenceResolvedTExpr::Ref(*chars))
      }
    },
    RawTExpr::Tokens(tokens) => return split_tokens(inp, tokens),
    RawTExpr::Lift(_) => return Err(PrecedenceResolutionFailure::OrderError),
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
    RawTExpr::InfixOp(infop) => {
      let atom = match infop {
        InfixOp::Arrow => Atom::Arrow,
        InfixOp::And => Atom::And,
        InfixOp::Or => Atom::Or,
        InfixOp::Tilda => Atom::Tilda,
      };
      return Ok(PrecedenceResolvedTExpr::AtomRef(atom));
    },
    RawTExpr::Star => return Ok(PrecedenceResolvedTExpr::Star),
    RawTExpr::Pt => return Ok(PrecedenceResolvedTExpr::Pt),
  }
}


#[test] #[ignore]
fn precedenter_tests() {
  let mut s =
    "".to_string() +
    "k : () -> ! = k (->) (-> * *) (* *) (,) (and b) ~ d ({ -> a b => (a,b), (,) a b => a and b } a)"
    ;
  pad_string(&mut s);
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
  let mut s =
    "".to_string() +
    "k : * -> * = { (,) a b, () => -> a b }"
    ;
  pad_string(&mut s);
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
  let mut s =
    "".to_string() +
    "k : * = (a : * = (->) a => (a : *) -> p a)"
    ;
  pad_string(&mut s);
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
  let mut s =
    "".to_string() +
    "T : * = ((and) *) T"
    ;
  pad_string(&mut s);
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
fn precedenter_tests5() {
  let mut s =
    "".to_string() +
    "d : * = (T:*) -> (K:*) -> T and K or ()"
    ;
  pad_string(&mut s);
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
