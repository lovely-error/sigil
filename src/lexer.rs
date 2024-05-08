

use core::mem::{align_of, transmute, size_of};
use core::simd::prelude::{SimdPartialEq as _, SimdPartialOrd as _};
use core::simd::{u8x4, Mask, Simd, u32x4};

use crate::{garbage, utils::{aligned_for, offset_to_higher_multiple, PageSource}, root_alloc::{Block4KPtr, RootAllocator}, interlacing_alloc::{InterlaceAllocator, SeqvRef, InterlacedSeqvItemRef, SeqvReader}, parser::resolve_precendece};

pub enum Letters {}
impl Letters {
  pub const A : u8 = 'A' as u8;
  pub const Z : u8 = 'Z' as u8;
  pub const a : u8 = 'a' as u8;
  pub const z : u8 = 'z' as u8;
  pub const Underscore : u8 = '_' as u8;
  pub const Whitespace: u8 = ' ' as u8;
  pub const NewLine: u8 = '\n' as u8;
  pub const LParen: u8 = '(' as u8;
  pub const RParen: u8 = ')' as u8;
  pub const EOT: u8 = '\u{3}' as u8;
  pub const ARROW: u16 = '-' as u16 | (('>' as u16) << 8);
  pub const COLON: u8 = ':' as u8;
  pub const LBrace: u8 = '{' as u8;
  pub const RBrace : u8 = '}' as u8;
  pub const Comma: u8 = ',' as u8;
  pub const FatArrow : u16 = '=' as u16 | (('>' as u16) << 8);
  pub const STAR: u8 =  '*' as u8;
  pub const EQUALS: u8 = '=' as u8;
  pub const OR : u16 = 'o' as u16 | (('r' as u16) << 8);
  pub const AND : u32 = 'a' as u32 | (('n' as u32) << 8) | (('d' as u32) << 16);
  pub const TILDA: u8 = '~' as u8;
  pub const EMARK: u8 = '!' as u8;
  pub const SEMICOLON : u8 = ';' as u8;
  pub const ZERO : u8 = 48 ;
  pub const NINE : u8 = 57;
}

pub fn pad_string(str:&mut String) {
  for _ in str.len() .. (str.len().next_multiple_of(size_of::<u8x4>())) {
    str.push(Letters::EOT as char);
  }
}

#[derive(Clone, Copy)]
struct ParseState {
  current_char_ptr:*const u8,
}
pub struct SourceTextParser<'i> {
  pub chars: &'i [u8],
  state:ParseState,
  end_ptr: *const u8
}
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum InfixOp { Arrow, And, Or, Tilda }

#[derive(Debug, Clone, Copy)]
pub struct ParseFailure;
pub type Maybe<T> = Result<T, ParseFailure>;
impl <'i> SourceTextParser<'i> {
  pub fn new(
    chars: &'i [u8]
  ) -> Self {
    let len = chars.len();
    if len % size_of::<u8x4>() != 0 {
      panic!("unpadded data")
    }
    let start_ptr = chars.as_ptr();
    Self {
      chars:chars,
      state:ParseState {
        current_char_ptr: start_ptr,
      },
      end_ptr: unsafe{start_ptr.add(len)}
    }
  }
  fn no_more_chars(&self) -> bool {
    if self.state.current_char_ptr == self.end_ptr {
      return true
    }
    if self.current_char() == Letters::EOT {
      return true
    }
    return false;
  }
  fn checkpoint(&self) -> ParseState {
    self.state
  }
  fn backtrack(&mut self, state:ParseState) {
    self.state = state;
  }
  fn current_char(&self) -> u8 {
    unsafe { *self.state.current_char_ptr }
  }
  fn skip(&mut self, count: u8) {
    unsafe {self.state.current_char_ptr =
     self.state.current_char_ptr.add(count as usize)}
  }
  fn skip_trivia(&mut self) { unsafe {
    let delimiters = u8x4::from_array([
      Letters::Whitespace, Letters::NewLine, 0, 0
    ]);
    let mut char_ptr = self.state.current_char_ptr;
    loop {
      if self.no_more_chars() { return; }
      let char = *char_ptr;
      let mask = u8x4::splat(char).simd_eq(delimiters);
      if !mask.any() { break }
      char_ptr = char_ptr.add(1);
    }
    self.state.current_char_ptr = char_ptr;
  } }
  fn parse_infix_op(&mut self) -> Option<InfixOp> { unsafe {
    let char_ptr = self.state.current_char_ptr;
    let chars4 =
      transmute::<_, u32>(*char_ptr.cast::<[u8;4]>());
    let quad = u32x4::splat(chars4);
    let filtered_quad = quad & Simd::from_array([
      0xff_ff, 0xff_ff, 0xff_ff_ff, 0xff
    ]);
    let patterns = u32x4::from_array([
      Letters::ARROW as u32, Letters::OR as u32, Letters::AND, Letters::TILDA as u32
    ]);
    let matches = filtered_quad.simd_eq(patterns);
    if matches == Mask::from_array([false, false, false, false]) { return None }
    let index = transmute::<_, u128>(matches).trailing_zeros() >> 5;
    let (infix, skip) = match index {
      0 => (InfixOp::Arrow, 2),
      1 => (InfixOp::Or, 2),
      2 => (InfixOp::And, 3),
      3 => (InfixOp::Tilda, 1),
      _ => unreachable!()
    };
    self.skip(skip);
    return Some(infix)
  }; }
  // fn probe_depth(&mut self) -> u32 { unsafe {
  //   let mut char_ptr = self.state.current_char_ptr;
  //   let mut current_depth = 0;
  //   let mut encountered_newline = false;
  //   let mut slow_iters_until_aligned = char_ptr.align_offset(align_of::<u8x4>());
  //   'outer:loop {
  //     loop {
  //       if self.no_more_chars() { break 'outer }
  //       if slow_iters_until_aligned == 0 { break }
  //       let byte = *char_ptr;
  //       match byte {
  //         Letters::NewLine => {
  //           current_depth = 0;
  //           encountered_newline = true;
  //         },
  //         Letters::Whitespace => current_depth += 1,
  //         _ => break 'outer
  //       }
  //       char_ptr = char_ptr.add(1);
  //       slow_iters_until_aligned -= 1;
  //     }
  //     loop {
  //       if self.no_more_chars() { break 'outer }
  //       let quad = *char_ptr.cast::<u8x4>();
  //       let ws_matches = quad.simd_eq(Simd::splat(Letters::Whitespace));
  //       if ws_matches != Mask::splat(true) {
  //         // we have encountered something other than whispace
  //         let remaining =
  //           transmute::<_, u32>(ws_matches)
  //           .trailing_ones()
  //           >> 3;
  //         current_depth += remaining;
  //         char_ptr = char_ptr.add(remaining as usize);

  //         if *char_ptr == Letters::NewLine {
  //           encountered_newline = true;
  //           current_depth = 0;
  //           char_ptr = char_ptr.add(1);
  //           slow_iters_until_aligned = char_ptr.align_offset(align_of::<u8x4>());
  //           continue 'outer;
  //         }
  //         break 'outer
  //       }
  //       // just four whitespaces. align is okay
  //       current_depth += 4;
  //       char_ptr = char_ptr.add(4);
  //     }
  //   }
  //   self.state.current_char_ptr = char_ptr;
  //   return if encountered_newline { current_depth } else { 0 }
  // } }
  fn parse_identifier(&mut self) -> Option<CharsData> { unsafe {
    let start_ptr = self.state.current_char_ptr;
    let mut char_ptr = start_ptr;
    let mut slow_iters_until_aligned = char_ptr.align_offset(align_of::<u8x4>());
    'main:loop {
      'slow:loop {
        if self.no_more_chars() { break 'main }
        if slow_iters_until_aligned == 0 { break 'slow }
        let byte = *char_ptr;
        let ok =
          byte >= Letters::a &&
          byte <= Letters::z ||
          byte >= Letters::A &&
          byte <= Letters::Z ||
          byte >= Letters::ZERO &&
          byte <= Letters::NINE ||
          byte == Letters::Underscore ;
        if !ok { break 'main }
        char_ptr = char_ptr.add(1);
        slow_iters_until_aligned -= 1;
      }
      'fast:loop {
        let quad = *char_ptr.cast::<u8x4>();
        let mut check1 = Mask::splat(false);
        check1 |= quad.simd_le(Simd::splat(Letters::z));
        check1 &= quad.simd_ge(Simd::splat(Letters::a));
        let mut check2 = Mask::splat(false);
        check2 |= quad.simd_le(Simd::splat(Letters::Z));
        check2 &= quad.simd_ge(Simd::splat(Letters::A));
        let mut check3 = Mask::splat(false);
        check3 |= quad.simd_le(Simd::splat(Letters::NINE));
        check3 &= quad.simd_ge(Simd::splat(Letters::ZERO));
        let outcome =
          check1 | check2 | check3 | quad.simd_eq(Simd::splat(Letters::Underscore));
        if outcome == Mask::splat(true) {
          char_ptr = char_ptr.add(4);
          continue 'fast
        }
        let mut remainder = 0 ;
        for i in outcome.to_array() {
          if i { remainder += 1 } else { break }
        }
        char_ptr = char_ptr.add(remainder);
        break 'main;
      }
    }
    self.state.current_char_ptr = char_ptr;
    let offset_from_head = (char_ptr as usize - start_ptr as usize) as u16;
    let empty_ident = offset_from_head == 0;
    if empty_ident { return None }
    let offset_from_start = (start_ptr as usize - self.chars.as_ptr() as usize) as u32;
    let result = CharsData { off2: offset_from_head, off1: offset_from_start };
    return Some(result)
  }; }
  fn parse_pattern_expr(
    &mut self,
  ) -> Maybe<RawPExpr> {
    let mut items = Vec::new();
    loop {
      self.skip_trivia();
      match self.current_char() {
        Letters::Underscore => {
          self.skip(1);
          items.push(RawPExpr::Discard);
          continue;
        },
        Letters::LParen => {
          if self.next_is_tuple_in_head_pos() {
            items.push(RawPExpr::HeadTuple);
            continue;
          }
          if self.next_is_unit() {
            items.push(RawPExpr::Pt);
            continue;
          }
          self.skip(1);
          let expr1 = self.parse_pattern_expr()?;
          self.skip_trivia();
          let char = self.current_char();
          if char == Letters::Comma {
            self.skip(1);
            self.skip_trivia();
            let expr2 = self.parse_pattern_expr()?;
            self.skip_trivia();
            if self.current_char() != Letters::RParen {
              return Err(ParseFailure)
            }
            self.skip(1);
            items.push(RawPExpr::Tuple(Box::new(expr1), Box::new(expr2)));
            continue;
          }
          if char != Letters::RParen {
            return Err(ParseFailure)
          }
          self.skip(1);
          items.push(expr1);
          continue;
        },
        _ => {
          if let Some(infixop) = self.parse_infix_op() {
            match infixop {
              InfixOp::Arrow => items.push(RawPExpr::Arrow),
              InfixOp::And => items.push(RawPExpr::And),
              InfixOp::Or => items.push(RawPExpr::Or),
              InfixOp::Tilda => items.push(RawPExpr::Tilda),
            };
            continue
          }
          if let Some(item) = self.parse_identifier() {
            items.push(RawPExpr::Chars(item));
            continue;
          } else { break }
        }
      }
    }
    if items.is_empty() { return Err(ParseFailure) }
    return Ok(RawPExpr::Seqv(items))
  }
  fn parse_lambda(&mut self) -> Maybe<Lambda> {
    assert!(self.current_char() == Letters::LBrace);
    self.skip(1);
    let mut clauses = Vec::new();
    loop {
      self.skip_trivia();
      let clause = self.parse_clause()?;
      clauses.push(clause);
      self.skip_trivia();
      let char = self.current_char();
      if char == Letters::RBrace { break }
      if char == Letters::Comma { self.skip(1); continue }
      return Err(ParseFailure)
    }
    self.skip(1);
    return Ok(Lambda(clauses))
  }
  fn parse_clause(&mut self,) -> Maybe<Clause> {
    let mut decons = Vec::new();
    loop {
      if let Ok(pexpr) = self.parse_pattern_expr() {
        decons.push(pexpr);
        self.skip_trivia();
        if self.current_char() == Letters::Comma {
          self.skip(1); self.skip_trivia();  continue;
        }
        if unsafe {transmute::<_, u16>(*self.state.current_char_ptr.cast::<[u8;2]>())}
          != Letters::FatArrow {
            return Err(ParseFailure)
        }
        self.skip(2);
        let rhs = self.parse_expr()?;
        return Ok(Clause(decons, rhs))
      } else { return Err(ParseFailure) }
    }
  }
  fn parse_lift(
    &mut self,
  ) -> Maybe<Lift> {
    assert!(self.current_char() == Letters::LParen);
    self.skip(1);
    let binder ;
    if let Ok(b) = self.parse_pattern_expr() { binder = b } else {
      return Err(ParseFailure)
    };
    self.skip_trivia();
    if self.current_char() != Letters::COLON { return Err(ParseFailure) }
    self.skip(1);
    let expr = self.parse_expr()?;
    if self.current_char() != Letters::RParen { return Err(ParseFailure) }
    self.skip(1);
    return Ok(Lift(binder, expr))
  }
  fn next_is_tuple_in_head_pos(&mut self) -> bool {
    let chkpt = self.checkpoint();
    assert!(self.current_char() == Letters::LParen);
    self.skip(1);
    self.skip_trivia();
    if self.current_char() != Letters::Comma {
      self.backtrack(chkpt);
      return false
    }
    self.skip(1);
    self.skip_trivia();
    if self.current_char() != Letters::RParen {
      self.backtrack(chkpt);
      return false
    }
    self.skip(1);
    return true
  }
  fn next_is_unit(&mut self) -> bool {
    let chkpt = self.checkpoint();
    assert!(self.current_char() == Letters::LParen);
    self.skip_trivia();
    self.skip(1);
    if self.current_char() != Letters::RParen {
      self.backtrack(chkpt);
      return false
    }
    self.skip(1);
    return true
  }
  fn parse_expr(
    &mut self,
  ) -> Maybe<RawTExpr> {
    let mut components = Vec::new();
    loop {
      self.skip_trivia();
      let chkpt = self.checkpoint();
      if let Ok(let_) = self.parse_let() {
        components.push(RawTExpr::Let(Box::new(let_)));
        continue;
      } else { self.backtrack(chkpt) }
      match self.current_char() {
        Letters::STAR => {
          self.skip(1);
          components.push(RawTExpr::Star);
          continue;
        }
        Letters::LParen => {
          let chkpt = self.checkpoint();
          if let Ok(lift) = self.parse_lift() {
            components.push(RawTExpr::Lift(Box::new(lift)));
            continue;
          } else { self.backtrack(chkpt) }
          if let Ok(tuple) = self.parse_tuple() {
            components.push(tuple);
            continue;
          } else { self.backtrack(chkpt) }
          if self.next_is_tuple_in_head_pos() {
            components.push(RawTExpr::TupleCtor);
            continue;
          }
          if self.next_is_unit() {
            components.push(RawTExpr::Pt);
            continue;
          }
          self.skip(1);
          let subexpr = self.parse_expr()?;
          components.push(subexpr);
          self.skip_trivia();
          if self.current_char() != Letters::RParen {
            return Err(ParseFailure)
          }
          self.skip(1);
          continue;
        },
        Letters::LBrace => {
          let lambda = self.parse_lambda()?;
          components.push(RawTExpr::Lambda(lambda));
          self.skip_trivia();
          continue;
        },
        Letters::EMARK => {
          self.skip(1);
          components.push(RawTExpr::EMark);
          continue;
        }
        _ => {
          if let Some(infix) = self.parse_infix_op() {
            let node = RawTExpr::InfixOp(infix);
            components.push(node);
            continue;
          }
          if let Some(chars) = self.parse_identifier() {
            components.push(RawTExpr::Chars(chars));
            continue;
          }
          break
        }
      }
    }
    if components.is_empty() { return Err(ParseFailure) }
    return Ok(RawTExpr::Tokens(components))
  }
  fn parse_tuple(&mut self) -> Maybe<RawTExpr> {
    assert!(self.current_char() == Letters::LParen);
    self.skip(1);
    let expr1 = self.parse_expr()?;
    self.skip_trivia();
    if self.current_char() != Letters::Comma {
      return Err(ParseFailure)
    }
    self.skip(1);
    let expr2 = self.parse_expr()?;
    self.skip_trivia();
    if self.current_char() != Letters::RParen {
      return Err(ParseFailure)
    }
    self.skip(1);
    return Ok(RawTExpr::Tuple(Box::new(expr1), Box::new(expr2)))
  }
  fn parse_let(&mut self) -> Maybe<LetGroup> {
    let mut defs = Vec::new();
    loop {
      self.skip_trivia();
      let pexpr = self.parse_pattern_expr()?;
      self.skip_trivia();
      if self.current_char() != Letters::COLON { return Err(ParseFailure) }
      self.skip(1);
      let texpr = self.parse_expr()?;
      if self.current_char() != Letters::EQUALS { return Err(ParseFailure) }
      self.skip(1);
      let oexpr = self.parse_expr()?;
      defs.push((pexpr, texpr, oexpr));
      self.skip_trivia();
      if self.current_char() == Letters::Comma { self.skip(1); continue }
      if unsafe{*self.state.current_char_ptr.cast::<[u8;2]>()} == ['=' as u8, '>' as u8] {
        self.skip(2); break;
      };
      return Err(ParseFailure)
    };
    let tail_expr = self.parse_expr()?;
    return Ok(LetGroup(defs, tail_expr))
  }
  pub fn parse_top_level_decl(&mut self) -> Maybe<RawDecl> {
    if let Some(name) = self.parse_identifier() {
      self.skip_trivia();
      if self.current_char() != Letters::COLON { return Err(ParseFailure) }
      self.skip(1);
      let texpr = self.parse_expr()?;
      self.skip_trivia();
      if self.current_char() != Letters::EQUALS { return Err(ParseFailure) }
      self.skip(1);
      let oexpr = self.parse_expr()?;
      return Ok(RawDecl(name, texpr, oexpr))
    } else { return Err(ParseFailure) }
  }
  pub fn parse_to_end(&mut self) -> Maybe<Vec<RawDecl>> {
    let mut items = Vec::new();
    loop {
      self.skip_trivia();
      if self.no_more_chars() { break }
      if self.current_char() == Letters::SEMICOLON {
        self.skip(1);
        self.skip_trivia();
      }
      match self.parse_top_level_decl() {
        Ok(decl) => items.push(decl),
        Err(err) => return Err(err)
      }
    }
    return Ok(items)
  }
}




#[derive(Debug)]
pub struct RawDecl(pub CharsData, pub RawTExpr, pub RawTExpr);
#[derive(Debug)]
pub struct Lift(pub RawPExpr, pub RawTExpr);
#[derive(Debug)]
pub struct LetGroup(pub Vec<(RawPExpr, RawTExpr, RawTExpr)>, pub RawTExpr);
#[derive(Debug)]
pub struct Lambda(pub Vec<Clause>);
#[derive(Debug)]
pub struct Clause(pub Vec<RawPExpr>, pub RawTExpr);

#[derive(Clone, Debug)]
pub enum RawPExpr {
  Discard,
  Chars(CharsData),
  Seqv(Vec<RawPExpr>),
  Arrow,
  Tilda,
  Or,
  And,
  Tuple(Box<Self>, Box<Self>),
  HeadTuple,
  Pt
}


#[derive(Debug, Clone, Copy)]
pub struct CharsData { pub off1: u32, pub off2: u16 }

trait Indirect<Item> {
  fn deref(&self) -> &Item;
}
trait TraversableSeqv<Item> {
  type Traverser: Iterator<Item = Item>;
  fn make_traverser(&self) -> Self::Traverser;
}
#[derive(Debug)]
pub enum RawTExpr {
  Chars(CharsData),
  Tokens(Vec<Self>),
  Lift(Box<Lift>),
  Let(Box<LetGroup>),
  Lambda(Lambda),
  Tuple(Box<Self>, Box<Self>),
  TupleCtor,
  InfixOp(InfixOp),
  Star,
  Pt,
  EMark
}

fn render_raw_texpr(texpr: &RawTExpr, chars_ptr: *const u8, write_target: &mut String) {
  match texpr {
    RawTExpr::TupleCtor => {
      write_target.push_str("(,)")
    }
    RawTExpr::Tuple(l, r) => {
      write_target.push('(');
      render_raw_texpr(&l, chars_ptr, write_target);
      write_target.push(',');
      render_raw_texpr(&r, chars_ptr, write_target);
      write_target.push(')');
    }
    RawTExpr::Chars(CharsData { off1: offset_from_start, off2: offset_from_head }) => {
      let substr = unsafe {
        let ptr = chars_ptr.add(*offset_from_start as usize);
        std::str::from_utf8_unchecked(
          std::slice::from_raw_parts(ptr, *offset_from_head as usize))
      };
      write_target.push_str(substr);
      // println!("{}", write_target);
    },
    RawTExpr::Tokens(exprs) => {
      for expr in exprs {
        render_raw_texpr(expr, chars_ptr, write_target);
      }
    },
    RawTExpr::Lift(lift) => {
      let Lift(binder, texpr) = lift.as_ref();
      write_target.push('(');
      render_raw_pexpr(binder, chars_ptr, write_target);
      write_target.push_str(" : ");
      // println!("{}", write_target);
      render_raw_texpr(texpr, chars_ptr, write_target);
      write_target.push(')')
    },
    RawTExpr::InfixOp(infop) => {
      match infop {
        InfixOp::Arrow => write_target.push_str("->"),
        InfixOp::And => write_target.push_str("and") ,
        InfixOp::Or => write_target.push_str("or"),
        InfixOp::Tilda => write_target.push('~'),
      }
    }
    RawTExpr::Star => {
      write_target.push('*');
    },
    RawTExpr::Let(let_) => {
      let LetGroup(lhs, rhs) = let_.as_ref();
      for (bind, texpr, val) in lhs {
        render_raw_pexpr(bind, chars_ptr, write_target);
        write_target.push_str(" : ");
        render_raw_texpr(texpr, chars_ptr, write_target);
        write_target.push_str(" = ");
        render_raw_texpr(val, chars_ptr, write_target);
        write_target.push(',')
      }
      write_target.push_str("=>");
      render_raw_texpr(rhs, chars_ptr, write_target)
    },
    RawTExpr::Lambda(Lambda(clauses)) => {
      write_target.push_str("{");
      for Clause(patterns, rhs) in clauses {
        for pattern in patterns {
          render_raw_pexpr(pattern, chars_ptr, write_target);
          write_target.push_str(",")
        }
        write_target.push_str("=>");
        render_raw_texpr(rhs, chars_ptr, write_target)
      }
      write_target.push_str("}")
    },
    RawTExpr::Pt => write_target.push_str("()"),
    RawTExpr::EMark => write_target.push('!')
  }
}
fn render_raw_pexpr(pexpr: &RawPExpr, chars_ptr: *const u8, write_target: &mut String) {
  match pexpr {
    RawPExpr::HeadTuple => write_target.push_str("(,)"),
    RawPExpr::Tuple(l, r) => {
      write_target.push('(');
      render_raw_pexpr(l, chars_ptr, write_target);
      write_target.push(',');
      render_raw_pexpr(r, chars_ptr, write_target);
      write_target.push(')');
    }
    RawPExpr::Discard => write_target.push('_'),
    RawPExpr::Chars(CharsData { off1: offset_from_start, off2: offset_from_head }) => {
      let substr = unsafe {
        let ptr = chars_ptr.add(*offset_from_start as usize);
        std::str::from_utf8_unchecked(
          std::slice::from_raw_parts(ptr, *offset_from_head as usize))
      };
      write_target.push_str(substr);
    },
    RawPExpr::Seqv(seqv) => {
      for expr in seqv {
        render_raw_pexpr(expr, chars_ptr, write_target)
      }
    },
    RawPExpr::Arrow => write_target.push_str("->"),
    RawPExpr::Tilda => write_target.push_str("~"),
    RawPExpr::Or => write_target.push_str("or"),
    RawPExpr::And => write_target.push_str("and"),
    RawPExpr::Pt => write_target.push_str("()"),
  }
}


#[test] #[ignore]
fn align_simd() {
  println!("{} {}", align_of::<core::simd::u8x8>(), align_of::<Simd<u64, 32>>())
}

#[test] #[ignore]
fn letter_distance() {
  let a = 'a' as u8;
  let z = 'z' as u8;
  for i in a ..= z {
    print!("{} {},",i, i as char)
  }
  println!("{}", 'ё' as u16)
}

#[test] #[ignore]
fn ident_parser1() {
  let s = " \nazZ_Z_ZZ_:a_Z_A_z__";
  let mut str = <String as core::str::FromStr>::from_str(s).unwrap();
  pad_string(&mut str);
  let mut parser = SourceTextParser::new(str.as_bytes());
  parser.skip_trivia();
  let CharsData { off1:offset_from_start, off2: offset_from_head } =
    parser.parse_identifier().unwrap();
  let str = unsafe {
    let data_ptr = parser.chars.as_ptr().add(offset_from_start as usize);
    std::str::from_utf8_unchecked(std::slice::from_raw_parts(data_ptr, offset_from_head as usize))
  };
  println!("{}", str);
  parser.state.current_char_ptr = unsafe {parser.state.current_char_ptr.add(1)};
  let CharsData { off1:offset_from_start, off2: offset_from_head } = parser.parse_identifier().unwrap();
  let str = unsafe {
    let data_ptr = parser.chars.as_ptr().add(offset_from_start as usize);
    std::str::from_utf8_unchecked(std::slice::from_raw_parts(data_ptr, offset_from_head as usize))
  };
  println!("{}", str)
}

#[test]
fn ident_parser2() {
  let mut s =
    "   \n ZazA09 zAZa90".to_string();
  pad_string(&mut s);
  let mut parser = SourceTextParser::new(s.as_bytes());
  parser.skip_trivia();
  let cd = parser.parse_identifier().unwrap();
  println!("{:?}", cd);
  parser.skip_trivia();
  let _ = parser.parse_identifier().unwrap();
}
#[test]
fn ident_parser3() {
  let mut s =
    "ZazA0990".to_string();
  pad_string(&mut s);
  let mut parser = SourceTextParser::new(s.as_bytes());
  parser.skip_trivia();
  let cd = parser.parse_identifier().unwrap();
  println!("{:?}", cd);
}

#[test] #[ignore]
fn decl_parse() {
  let mut s =
    "".to_string() +
    "idT1 : () -> () = { i => i }"
    ;
  pad_string(&mut s);
  let mut parser = SourceTextParser::new(s.as_bytes());
  // let depth = parser.probe_depth();
  let expr = parser.parse_to_end();
  match expr {
    Err(err) => println!("{:?}", err),
    Ok(r) => {
      println!("{:#?}", r);
      // let mut str = String::new();
      // let chars = parser.chars.as_ptr();
      // render_raw_texpr(&tyexpr, chars, &mut str);
      // str.push_str(" = ");
      // render_raw_texpr(&oexpr, chars, &mut str);
      // println!("{}", str)
      println!("{:#?}", r[0].2)
    }
  }
}
#[test] #[ignore]
fn expr_parse() {
  let mut s =
    "".to_string() +
    "{ (,) a b => a (a,b) ((,) a b) }"
    ;
  pad_string(&mut s);
  let mut parser = SourceTextParser::new(s.as_bytes());
  let expr = parser.parse_expr();
  match expr {
    Err(err) => println!("{:?}", err),
    Ok(expr) => {
      println!("{:#?}", expr)
    }
  }
}
