
use std::{str::{FromStr}, mem::{align_of, MaybeUninit, transmute, size_of, ManuallyDrop}, ptr::{addr_of_mut, copy_nonoverlapping, null_mut, addr_of}, simd::{self, u8x8, SimdPartialEq, SimdPartialOrd, u8x4, Mask, Simd, u32x4}, marker::PhantomData, any::Any};

use regex::{RegexSet, Regex};

use crate::{garbage, utils::{aligned_for, offset_to_higher_multiple, PageSource}, root_alloc::{Block4KPtr, RootAllocator}, interlacing_alloc::{InterlaceAllocator, SeqvRef, InterlacedSeqvItemRef, SeqvReader}, parser::resolve_precendece};

enum Letters {}
impl Letters {
  const A : u8 = 'A' as u8;
  const Z : u8 = 'Z' as u8;
  const a : u8 = 'a' as u8;
  const z : u8 = 'z' as u8;
  const Underscore : u8 = '_' as u8;
  const Whitespace: u8 = ' ' as u8;
  const NewLine: u8 = '\n' as u8;
  const LParen: u8 = '(' as u8;
  const RParen: u8 = ')' as u8;
  const EOT: u8 = '\u{3}' as u8;
  const ARROW: u16 = '-' as u16 | (('>' as u16) << 8);
  const COLON: u8 = ':' as u8;
  const LBrace: u8 = '{' as u8;
  const RBrace : u8 = '}' as u8;
  const Comma: u8 = ',' as u8;
  const FatArrow : u16 = '=' as u16 | (('>' as u16) << 8);
  const STAR: u8 =  '*' as u8;
  const EQUALS: u8 = '=' as u8;
  const OR : u16 = 'o' as u16 | (('r' as u16) << 8);
  const AND : u32 = 'a' as u32 | (('n' as u32) << 8) | (('d' as u32) << 16);
  const TILDA: u8 = '~' as u8;
  const QMARK: u8 = '!' as u8;
}


#[derive(Clone, Copy)]
struct ParseState {
  current_char_ptr:*const u8,
  line:u32,
  decl_end: *const u8
}
pub struct SourceTextParser<'i> {
  pub chars: &'i String,
  state:ParseState,
  end_ptr: *const u8,
}
#[derive(Debug, Clone, Copy)]
enum InfixOp { Arrow, And, Or, Tilda }

#[derive(Debug)]
pub struct ParseFailure;
pub type Maybe<T> = Result<T, Box<dyn Any>>;
impl <'i> SourceTextParser<'i> {
  pub fn new(
    chars: &'i String
  ) -> Self {
    let start_ptr = chars.as_ptr();
    let end_ptr = unsafe{start_ptr.add(chars.len())};
    Self {
      chars,
      end_ptr,
      state:ParseState {
        line: 1,
        current_char_ptr: start_ptr,
        decl_end: end_ptr
      },
    }
  }
  fn checkpoint(&self) -> ParseState {
    self.state
  }
  fn backtrack(&mut self, state:ParseState) {
    self.state = state;
  }
  fn current_char(&self) -> u8 {
    if self.state.current_char_ptr >= self.state.decl_end {
      return Letters::EOT
    }
    unsafe { *self.state.current_char_ptr }
  }
  fn skip(&mut self, count: u8) {
    unsafe {self.state.current_char_ptr =
     self.state.current_char_ptr.add(count as usize)}
  }
  fn skip_delimiters(&mut self) { unsafe {
    let delimiters = u8x4::from_array([
      Letters::Whitespace, Letters::NewLine, 0, 0
    ]);
    let end_ptr = self.state.decl_end;
    let mut char_ptr = self.state.current_char_ptr;
    loop {
      if char_ptr >= end_ptr { return }
      let char = *char_ptr;
      let mask = u8x4::splat(char).simd_eq(delimiters);
      if mask == Mask::splat(false) { break }
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
  fn probe_depth(&mut self) -> u32 { unsafe {
    let mut char_ptr = self.state.current_char_ptr;
    let mut current_depth = 0;
    let end_ptr = self.state.decl_end;
    let mut encountered_newline = false;
    let mut slow_iters_until_aligned = char_ptr.align_offset(align_of::<u8x4>());
    'outer:loop {
      loop {
        if char_ptr >= end_ptr { break 'outer }
        if slow_iters_until_aligned == 0 { break }
        let byte = *char_ptr;
        match byte {
          Letters::NewLine => {
            current_depth = 0;
            encountered_newline = true;
          },
          Letters::Whitespace => current_depth += 1,
          _ => break 'outer
        }
        char_ptr = char_ptr.add(1);
        slow_iters_until_aligned -= 1;
      }
      loop {
        if char_ptr >= end_ptr { break 'outer }
        let quad = *char_ptr.cast::<u8x4>();
        let ws_matches = quad.simd_eq(Simd::splat(Letters::Whitespace));
        if ws_matches != Mask::splat(true) {
          // we have encountered something other than whispace
          let remaining =
            transmute::<_, u32>(ws_matches)
            .trailing_ones()
            >> 3;
          current_depth += remaining;
          char_ptr = char_ptr.add(remaining as usize);

          if *char_ptr == Letters::NewLine {
            encountered_newline = true;
            current_depth = 0;
            char_ptr = char_ptr.add(1);
            slow_iters_until_aligned = char_ptr.align_offset(align_of::<u8x4>());
            continue 'outer;
          }

          break 'outer
        }
        // just four whitespaces. align is okay
        current_depth += 4;
        char_ptr = char_ptr.add(4);
      }
    }
    self.state.current_char_ptr = char_ptr;
    return if encountered_newline { current_depth } else { 0 }
  } }
  fn parse_identifier(&mut self) -> Option<CharsData> { unsafe {
    let end_ptr = self.state.decl_end;
    let start_ptr = self.state.current_char_ptr;
    let mut char_ptr = start_ptr;
    let mut slow_iters_until_aligned = char_ptr.align_offset(align_of::<u8x4>());
    'main:loop {
      'slow:loop {
        if char_ptr >= end_ptr { break 'main }
        if slow_iters_until_aligned == 0 { break 'slow }
        let byte = *char_ptr;
        let ok =
          byte >= Letters::a &&
          byte <= Letters::z ||
          byte >= Letters::A &&
          byte <= Letters::Z ||
          byte == Letters::Underscore ;
        if !ok { break 'main }
        char_ptr = char_ptr.add(1);
        slow_iters_until_aligned -= 1;
      }
      let mut char_ptr_ = char_ptr;
      loop {
        // the code bellow relies on the fact that
        // A > a && A > z
        // this is fragile as f
        let quad = *char_ptr_.cast::<u8x4>();
        let mut outcomes = Mask::splat(false);
        outcomes |= quad.simd_le(Simd::splat(Letters::z));
        outcomes &= quad.simd_ge(Simd::splat(Letters::a));
        outcomes |= quad.simd_eq(Simd::splat(Letters::Underscore));
        let resolved = Mask::splat(true);
        if outcomes == resolved {
          char_ptr_ = char_ptr_.add(4);
          if char_ptr_ >= end_ptr { break }
          continue
        }
        outcomes |= quad.simd_le(Simd::splat(Letters::Z));
        outcomes &= quad.simd_ge(Simd::splat(Letters::A));
        outcomes |= quad.simd_eq(Simd::splat(Letters::Underscore));
        if outcomes == resolved {
          char_ptr_ = char_ptr_.add(4);
          if char_ptr_ >= end_ptr { break }
          continue
        }
        // we have encountered some chars which are not
        // valid for an identifier
        let excess = (transmute::<_, u32>(outcomes).trailing_ones() >> 3) as usize;
        char_ptr = char_ptr_.add(excess);
        break 'main;
      }
      char_ptr = char_ptr_;
    }
    self.state.current_char_ptr = char_ptr;
    let offset_from_head = (char_ptr as usize - start_ptr as usize) as u16;
    let empty_ident = offset_from_head == 0;
    if empty_ident { return None }
    let offset_from_start = (start_ptr as usize - self.chars.as_ptr() as usize) as u32;
    let result = CharsData { offset_from_head, offset_from_start };
    return Some(result)
  }; }
  fn parse_pattern_expr(
    &mut self,
  ) -> Maybe<RawPExpr> {
    let mut items = Vec::new();
    loop {
      self.skip_delimiters();
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
          self.skip_delimiters();
          let char = self.current_char();
          if char == Letters::Comma {
            self.skip(1);
            self.skip_delimiters();
            let expr2 = self.parse_pattern_expr()?;
            self.skip_delimiters();
            if self.current_char() != Letters::RParen {
              return Err(Box::new(ParseFailure))
            }
            self.skip(1);
            items.push(RawPExpr::Tuple(Box::new(expr1), Box::new(expr2)));
            continue;
          }
          if char != Letters::RParen {
            return Err(Box::new(ParseFailure))
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
    if items.is_empty() { return Err(Box::new(ParseFailure)) }
    return Ok(RawPExpr::Seqv(items))
  }
  fn parse_lambda(&mut self) -> Maybe<Lambda> {
    assert!(self.current_char() == Letters::LBrace);
    self.skip(1);
    let mut clauses = Vec::new();
    loop {
      self.skip_delimiters();
      let clause = self.parse_clause()?;
      clauses.push(clause);
      self.skip_delimiters();
      let char = self.current_char();
      if char == Letters::RBrace { break }
      if char == Letters::Comma { self.skip(1); continue }
      return Err(Box::new(ParseFailure))
    }
    self.skip(1);
    return Ok(Lambda(clauses))
  }
  fn parse_clause(&mut self,) -> Maybe<Clause> {
    let mut decons = Vec::new();
    loop {
      if let Ok(pexpr) = self.parse_pattern_expr() {
        decons.push(pexpr);
        self.skip_delimiters();
        if self.current_char() == Letters::Comma {
          self.skip(1); self.skip_delimiters();  continue;
        }
        if unsafe {transmute::<_, u16>(*self.state.current_char_ptr.cast::<[u8;2]>())}
          != Letters::FatArrow {
            return Err(Box::new(ParseFailure))
        }
        self.skip(2);
        let depth = self.probe_depth();
        let rhs = self.parse_expr(depth)?;
        return Ok(Clause(decons, rhs))
      } else { return Err(Box::new(ParseFailure)) }
    }
  }
  fn parse_lift(
    &mut self,
  ) -> Maybe<Lift> {
    assert!(self.current_char() == Letters::LParen);
    self.skip(1);
    let binder ;
    if let Ok(b) = self.parse_pattern_expr() { binder = b } else {
      return Err(Box::new(ParseFailure))
    };
    self.skip_delimiters();
    if self.current_char() != Letters::COLON { return Err(Box::new(ParseFailure)) }
    self.skip(1);
    let depth = self.probe_depth();
    let expr = self.parse_expr(depth)?;
    if self.current_char() != Letters::RParen { return Err(Box::new(ParseFailure)) }
    self.skip(1);
    return Ok(Lift(binder, expr))
  }
  fn next_is_tuple_in_head_pos(&mut self) -> bool {
    let chkpt = self.checkpoint();
    assert!(self.current_char() == Letters::LParen);
    self.skip(1);
    self.skip_delimiters();
    if self.current_char() != Letters::Comma {
      self.backtrack(chkpt);
      return false
    }
    self.skip(1);
    self.skip_delimiters();
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
    self.skip(1);
    self.skip_delimiters();
    if self.current_char() != Letters::RParen {
      self.backtrack(chkpt);
      return false
    }
    self.skip(1);
    return true
  }
  fn parse_expr(
    &mut self,
    anchor_depth: u32,
  ) -> Maybe<RawTExpr> {
    let mut components = Vec::new();
    loop {
      self.skip_delimiters();
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
          let subexpr = self.parse_expr(anchor_depth)?;
          components.push(subexpr);
          self.skip_delimiters();
          if self.current_char() != Letters::RParen {
            return Err(Box::new(ParseFailure))
          }
          self.skip(1);
          continue;
        },
        Letters::LBrace => {
          let lambda = self.parse_lambda()?;
          components.push(RawTExpr::Lambda(lambda));
          self.skip_delimiters();
          continue;
        },
        Letters::QMARK => {
          self.skip(1);
          components.push(RawTExpr::QMark);
          continue;
        }
        _ => {
          if let Some(infix) = self.parse_infix_op() {
            let infix = match infix {
              InfixOp::Arrow => RawTExpr::Arrow,
              InfixOp::And => RawTExpr::And,
              InfixOp::Or => RawTExpr::Or,
              InfixOp::Tilda => RawTExpr::Tilda
            };
            components.push(infix);
            continue;
          }
          let chkpt = self.checkpoint();
          if let Ok(let_) = self.parse_let() {
            components.push(RawTExpr::Let(Box::new(let_)));
            continue;
          } else { self.backtrack(chkpt) }
          if let Some(chars) = self.parse_identifier() {
            components.push(RawTExpr::Chars(chars));
            continue;
          }
          break
        }
      }
    }
    if components.is_empty() { return Err(Box::new(ParseFailure)) }
    return Ok(RawTExpr::Tokens(components))
  }
  fn parse_tuple(&mut self) -> Maybe<RawTExpr> {
    assert!(self.current_char() == Letters::LParen);
    self.skip(1);
    let depth = self.probe_depth();
    let expr1 = self.parse_expr(depth)?;
    self.skip_delimiters();
    if self.current_char() != Letters::Comma {
      return Err(Box::new(ParseFailure))
    }
    self.skip(1);
    let depth = self.probe_depth();
    let expr2 = self.parse_expr(depth)?;
    self.skip_delimiters();
    if self.current_char() != Letters::RParen {
      return Err(Box::new(ParseFailure))
    }
    self.skip(1);
    return Ok(RawTExpr::Tuple(Box::new(expr1), Box::new(expr2)))
  }
  fn parse_let(&mut self) -> Maybe<LetGroup> {
    let mut defs = Vec::new();
    loop {
      self.skip_delimiters();
      let pexpr = self.parse_pattern_expr()?;
      self.skip_delimiters();
      if self.current_char() != Letters::EQUALS { return Err(Box::new(ParseFailure)) }
      self.skip(1);
      let depth = self.probe_depth();
      let oexpr = self.parse_expr(depth)?;
      defs.push((pexpr, oexpr));
      self.skip_delimiters();
      if self.current_char() == Letters::Comma { self.skip(1); continue }
      if unsafe{*self.state.current_char_ptr.cast::<[u8;2]>()} == ['=' as u8, '>' as u8] {
        self.skip(2); break;
      };
      return Err(Box::new(ParseFailure))
    };
    let depth = self.probe_depth();
    let tail_expr = self.parse_expr(depth, )?;
    return Ok(LetGroup(defs, tail_expr))
  }
  fn traversed_all_chars(&self) -> bool {
    self.state.current_char_ptr >= self.end_ptr
  }
  pub fn parse_top_level_decl(&mut self) -> Maybe<RawDecl> {
    let anchor_depth = self.probe_depth();
    if let Some(name) = self.parse_identifier() {
      self.skip_delimiters();
      if self.current_char() != Letters::COLON { return Err(Box::new(ParseFailure)) }
      self.skip(1);
      let depth = self.probe_depth().max(anchor_depth);
      let texpr = self.parse_expr(depth)?;
      self.skip_delimiters();
      if self.current_char() != Letters::EQUALS { return Err(Box::new(ParseFailure)) }
      self.skip(1);
      let depth = self.probe_depth().max(anchor_depth);
      let oexpr = self.parse_expr(depth)?;
      return Ok(RawDecl(name, texpr, oexpr))
    } else { return Err(Box::new(ParseFailure)) }
  }
  pub fn find_decl_boundry(&mut self) -> (u32, u32) {
    let start_ptr = self.state.current_char_ptr;
    let end_ptr = self.state.decl_end;

    todo!()
  }
  pub fn parse_to_end(&mut self) -> Maybe<Vec<RawDecl>> {
    let mut items = Vec::new();
    loop {
      if self.traversed_all_chars() { break }
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
pub struct LetGroup(pub Vec<(RawPExpr, RawTExpr)>, pub RawTExpr);
#[derive(Debug)]
pub struct Lambda(pub Vec<Clause>);
#[derive(Debug)]
pub struct Clause(pub Vec<RawPExpr>, pub RawTExpr);

#[derive(Clone, Debug)]
pub enum RawPExpr {
  Discard, Chars(CharsData), Seqv(Vec<RawPExpr>),
  Arrow, Tilda, Or, And,
  Tuple(Box<Self>, Box<Self>),
  HeadTuple,
  Pt
}


#[derive(Debug, Clone, Copy)]
pub struct CharsData { pub offset_from_start: u32, pub offset_from_head: u16 }

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
  Arrow, Tilda, Star, Or, And,
  Pt, QMark
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
    RawTExpr::Chars(CharsData { offset_from_start, offset_from_head }) => {
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
    RawTExpr::Arrow => {
      write_target.push_str("->");
    },
    RawTExpr::Tilda => write_target.push('~'),
    RawTExpr::Star => {
      write_target.push('*');
      // println!("{}", write_target);
    },
    RawTExpr::Or => {
      write_target.push_str("or");
      // println!("{}", write_target);
    },
    RawTExpr::And => {
      write_target.push_str("and")
    },
    RawTExpr::Let(let_) => {
      let LetGroup(lhs, rhs) = let_.as_ref();
      for (bind, val) in lhs {
        render_raw_pexpr(bind, chars_ptr, write_target);
        write_target.push_str("=");
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
    RawTExpr::QMark => write_target.push('!')
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
    RawPExpr::Chars(CharsData { offset_from_start, offset_from_head }) => {
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
  println!("{} {}", align_of::<u8x8>(), align_of::<Simd<u64, 32>>())
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
fn ident_parser() {
  let s = " \nazZ_Z_ZZ_:a_Z_A_z__";
  let str = String::from_str(s).unwrap();
  let mut parser = SourceTextParser::new(&str);
  parser.skip_delimiters();
  let CharsData { offset_from_start, offset_from_head } =
    parser.parse_identifier().unwrap();
  let str = unsafe {
    let data_ptr = parser.chars.as_ptr().add(offset_from_start as usize);
    std::str::from_utf8_unchecked(std::slice::from_raw_parts(data_ptr, offset_from_head as usize))
  };
  println!("{}", str);
  parser.state.current_char_ptr = unsafe {parser.state.current_char_ptr.add(1)};
  let CharsData { offset_from_start, offset_from_head } = parser.parse_identifier().unwrap();
  let str = unsafe {
    let data_ptr = parser.chars.as_ptr().add(offset_from_start as usize);
    std::str::from_utf8_unchecked(std::slice::from_raw_parts(data_ptr, offset_from_head as usize))
  };
  println!("{}", str)
}

#[test]
fn ident_parser_() {
  let s =
    "   \n ZazA zAZa";
  let str = String::from_str(s).unwrap();
  let mut parser = SourceTextParser::new(&str);
  let depth = parser.probe_depth();
  assert!(depth == 1);
  let _ = parser.parse_identifier().unwrap();
  let depth = parser.probe_depth();
  assert!(depth == 0);
  let _ = parser.parse_identifier().unwrap();
}

#[test] #[ignore]
fn decl_parse() {
  let s =
    "".to_string() +
    "k : i = k => (* -> *) = (cons a _: expr a b) \nand pt { -> => and }"
    ;
  let mut parser = SourceTextParser::new(&s);
  // let depth = parser.probe_depth();
  let expr = parser.parse_top_level_decl();
  match expr {
    Err(err) => println!("{:?}", err),
    Ok(RawDecl(name, tyexpr, oexpr)) => {
      // let mut str = String::new();
      // let chars = parser.chars.as_ptr();
      // render_raw_texpr(&tyexpr, chars, &mut str);
      // str.push_str(" = ");
      // render_raw_texpr(&oexpr, chars, &mut str);
      // println!("{}", str)
      println!("{:#?}", oexpr)
    }
  }
}
#[test] #[ignore]
fn expr_parse() {
  let s =
    "".to_string() +
    "{ (,) a b => a (a,b) ((,) a b) }"
    ;
  let mut parser = SourceTextParser::new(&s);
  let depth = parser.probe_depth();
  let expr = parser.parse_expr(depth);
  match expr {
    Err(err) => println!("{:?}", err),
    Ok(expr) => {
      println!("{:#?}", expr)
    }
  }
}
#[test] #[ignore]
fn depth_test() {
  let s =
    "".to_string() +
    "k : () = (() = (a = b => c) => ())"
    ;
  let mut parser = SourceTextParser::new(&s);
  // let depth = parser.probe_depth();
  let expr = parser.parse_to_end();
  match expr {
    Err(err) => println!("{:?}", err),
    Ok(decls) => {
      // let mut str = String::new();
      // let chars = parser.chars.as_ptr();
      // render_raw_texpr(&tyexpr, chars, &mut str);
      // str.push_str(" = ");
      // render_raw_texpr(&oexpr, chars, &mut str);
      // println!("{}", str)
      println!("{:#?}", decls)
    }
  }
}