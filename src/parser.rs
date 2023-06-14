
use std::{str::{FromStr}, mem::{align_of, MaybeUninit, transmute, size_of, ManuallyDrop}, ptr::{addr_of_mut, copy_nonoverlapping, null_mut, addr_of}, simd::{self, u8x8, SimdPartialEq, SimdPartialOrd, u8x4, Mask, Simd, u32x4}, marker::PhantomData};

use crate::{garbage, utils::{aligned_for, offset_to_higher_multiple, DrainablePageHolder}, root_alloc::{Block4KPtr, RootAllocator}, interlacing_alloc::{InterlaceAllocator, SeqvRef, InterlacedSeqvItemRef, SeqvReader}};

struct Letters;
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
}


#[derive(Clone, Copy)]
struct ParseState {
  current_char_ptr:*const u8,
  line:u32,
}
struct SourceTextParser {
  chars: String,
  limit: usize,
  state:ParseState,
  end_ptr: *const u8,
}
#[derive(Debug, Clone, Copy)]
enum InfixOp { Arrow, And, Or, Tilda }

#[derive(Debug)]
struct ParseFailure;
type Maybe<T> = Result<T, ParseFailure>;
impl SourceTextParser {
  fn new(
    mut chars: String
  ) -> Self {
    let limit = chars.len();
    // pad string to not cause misaligned simd loads at the end
    let padding = offset_to_higher_multiple(limit as u64, align_of::<u8x4>()) as usize;
    chars.reserve(padding);
    for _ in 0 .. padding {
      chars.push(0 as char)
    }
    let chptr = chars.as_mut_ptr();
    assert!(chptr as u64 % 8 == 0, "improperly aligned ptr to chars");
    let end_ptr = unsafe { chptr.add(limit) };
    Self {
      chars:chars,
      limit: limit,
      end_ptr,
      state:ParseState {
        line: 1,
        current_char_ptr: chptr
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
    if self.state.current_char_ptr >= self.end_ptr {
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
    let end_ptr = self.end_ptr;
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
    let end_ptr = self.end_ptr;
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
    let end_ptr = self.end_ptr;
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
    page_source: &mut dyn DrainablePageHolder
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
          self.skip(1);
          let subexpr = self.parse_pattern_expr(page_source)?;
          self.skip_delimiters();
          if self.current_char() != Letters::RParen {
            return Err(ParseFailure)
          }
          self.skip(1);
          items.push(subexpr);
          continue;
        },
        _ => {
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
  fn parse_lambda(&mut self, page_source: &mut dyn DrainablePageHolder) -> Maybe<Lambda> {
    assert!(self.current_char() == Letters::LBrace);
    self.skip(1);
    let mut clauses = Vec::new();
    loop {
      self.skip_delimiters();
      let clause = self.parse_clause(page_source)?;
      clauses.push(clause);
      self.skip_delimiters();
      let char = self.current_char();
      if char == Letters::RBrace { break }
      if char == Letters::Comma { continue }
      return Err(ParseFailure)
    }
    self.skip(1);
    return Ok(Lambda(clauses))
  }
  fn parse_clause(&mut self, page_source: &mut dyn DrainablePageHolder) -> Maybe<Clause> {
    let mut decons = Vec::new();
    loop {
      if let Ok(pexpr) = self.parse_pattern_expr(page_source) {
        decons.push(pexpr);
        self.skip_delimiters();
        if self.current_char() == Letters::Comma {
          self.skip(1); self.skip_delimiters();  continue;
        }
        if unsafe {transmute::<_, u16>(*self.state.current_char_ptr.cast::<[u8;2]>())}
          != Letters::FatArrow {
            return Err(ParseFailure)
        }
        self.skip(2);
        let depth = self.probe_depth();
        let rhs = self.parse_expr(depth, page_source)?;
        return Ok(Clause(decons, rhs))
      } else { return Err(ParseFailure) }
    }
  }
  fn parse_lift(
    &mut self,
    page_source: &mut dyn DrainablePageHolder
  ) -> Maybe<Lift> {
    assert!(self.current_char() == Letters::LParen);
    self.skip(1);
    // this should be pattern expr
    let binder ;
    if let Ok(b) = self.parse_pattern_expr(page_source) { binder = b } else {
      return Err(ParseFailure)
    };
    self.skip_delimiters();
    if self.current_char() != Letters::COLON { return Err(ParseFailure) }
    self.skip(1);
    let depth = self.probe_depth();
    let expr = self.parse_expr(depth, page_source)?;
    if self.current_char() != Letters::RParen { return Err(ParseFailure) }
    self.skip(1);
    return Ok(Lift(binder, expr))
  }
  fn fscan_for_hint(&self) -> Option<()> {
    todo!()
  }
  fn parse_expr(
    &mut self,
    depth: u32,
    page_source: &mut dyn DrainablePageHolder
  ) -> Maybe<RawTExpr> {
    let mut components = Vec::new();
    loop {
      self.skip_delimiters();
      match self.current_char() {
        Letters::STAR => {
          self.skip(1);
          components.push(RawTExpr::Star);
          continue;
        }
        Letters::LParen => {
          let chkpt = self.checkpoint();
          if let Ok(lift) = self.parse_lift(page_source) {
            components.push(RawTExpr::Lift(Box::new(lift)));
            continue;
          } else { self.backtrack(chkpt) };
          self.skip(1);
          let depth = self.probe_depth().max(depth);
          let subexpr = self.parse_expr(depth, page_source)?;
          components.push(subexpr);
          self.skip_delimiters();
          if self.current_char() != Letters::RParen {
            return Err(ParseFailure)
          }
          self.skip(1);
          continue;
        },
        Letters::LBrace => {
          let lambda = self.parse_lambda(page_source)?;
          components.push(RawTExpr::Lambda(lambda));
          self.skip_delimiters();
          continue;
        },
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
          if let Ok(let_) = self.parse_let(page_source) {
            components.push(RawTExpr::Let(Box::new(let_)));
            self.skip_delimiters();
            continue
          } else { self.backtrack(chkpt) }
          self.skip_delimiters();
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
  fn parse_let(&mut self, page_source: &mut dyn DrainablePageHolder) -> Maybe<LetGroup> {
    let mut defs = Vec::new();
    loop {
      self.skip_delimiters();
      let pexpr = self.parse_pattern_expr(page_source)?;
      self.skip_delimiters();
      if self.current_char() != Letters::EQUALS { return Err(ParseFailure) }
      self.skip(1);
      let depth = self.probe_depth();
      let oexpr = self.parse_expr(depth, page_source)?;
      defs.push((pexpr, oexpr));
      self.skip_delimiters();
      if self.current_char() == Letters::Comma { self.skip(1); continue }
      if unsafe{*self.state.current_char_ptr.cast::<[u8;2]>()} == ['=' as u8, '>' as u8] {
        self.skip(2); break;
      };
      return Err(ParseFailure)
    };
    let depth = self.probe_depth();
    let tail_expr = self.parse_expr(depth, page_source)?;
    return Ok(LetGroup(defs, tail_expr))
  }
  fn parse_top_level_decl(&mut self, page_source: &mut dyn DrainablePageHolder) -> Maybe<Decl> {
    let depth = self.probe_depth();
    if let Some(name) = self.parse_identifier() {
      self.skip_delimiters();
      if self.current_char() != Letters::COLON { return Err(ParseFailure) }
      self.skip(1);
      let depth = self.probe_depth().max(depth);
      let texpr = self.parse_expr(depth, page_source)?;
      self.skip_delimiters();
      if self.current_char() != Letters::EQUALS { return Err(ParseFailure) }
      self.skip(1);
      let depth = self.probe_depth().max(depth);
      let oexpr = self.parse_expr(depth, page_source)?;
      return Ok(Decl(name, texpr, oexpr))
    } else { return Err(ParseFailure) }
  }
}

struct Decl(CharsData, RawTExpr, RawTExpr);
struct Lift(RawPExpr, RawTExpr);
struct LetGroup(Vec<(RawPExpr, RawTExpr)>, RawTExpr);
struct Lambda(Vec<Clause>);
struct Clause(Vec<RawPExpr>, RawTExpr);

#[derive(Clone, Debug)]
enum RawPExpr {
  Discard, Chars(CharsData), Seqv(Vec<RawPExpr>)
}

#[derive(Debug, Clone, Copy)]
struct CharsData { offset_from_start: u32, offset_from_head: u16 }

trait SomeBoxer<Item> {
  fn deref(&self) -> &Item;
}
trait TraversableSeqv<Item> {
  type Traverser: Iterator<Item = Item>;
  fn make_traverser(&self) -> Self::Traverser;
}

enum RawTExpr {
  Chars(CharsData),
  Tokens(Vec<Self>),
  Lift(Box<Lift>),
  Let(Box<LetGroup>),
  Lambda(Lambda),
  Arrow, Tilda, Star, Or, And
}
#[derive(Debug)]
enum PrecedenceResolvedRawTExpr {
  App(Box<Self>, Vec<Self>),
  Ref(CharsData),
  AtomRef(AtomRef),
  Arrow(Box<Self>, Box<Self>),
  DArrow(RawPExpr, Box<Self>, Box<Self>),
  And(Box<Self>, Box<Self>),
  DAnd(RawPExpr, Box<Self>, Box<Self>),
  Or(Box<Self>, Box<Self>),
  Star,
  Let(Vec<(RawPExpr, Self)>, Box<Self>),
  Lambda(Vec<(Vec<RawPExpr>, Self)>),
  Tilda(Box<Self>, Box<Self>)
}
#[derive(Debug, Clone, Copy)]
enum AtomRef { And, Or, Arrow, Tilda }

fn render_raw_texpr(texpr: &RawTExpr, chars_ptr: *const u8, write_target: &mut String) {
  match texpr {
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
  }
}
fn render_raw_pexpr(pexpr: &RawPExpr, chars_ptr: *const u8, write_target: &mut String) {
  match pexpr {
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
  }
}


fn resolve_precendece(
  texpr: &RawTExpr
) -> Result<PrecedenceResolvedRawTExpr, PrecedenceResolutionError> {
  return resolve_singular(texpr)
}
struct PrecedenceResolutionError;
fn split_tokens(
  tokens: &[RawTExpr]
) -> Result<PrecedenceResolvedRawTExpr, PrecedenceResolutionError> {
  let end_index = tokens.len();
  if end_index == 0 { return Err(PrecedenceResolutionError) }
  if end_index == 1 {
    return resolve_singular(&tokens[0])
  }
  let mut index = 0;
  while index != end_index {
    let item = &tokens[index];
    // lifts has highest precedence
    if let RawTExpr::Lift(lift) = item {
      let Some(next_item) = tokens.get(index + 1) else {
        return Err(PrecedenceResolutionError)
      };
      match next_item {
        arm@(RawTExpr::And | RawTExpr::Arrow) => {
          let Lift(pexpr, texpr) = lift.as_ref();
          let head = resolve_precendece(texpr)?;
          let tail = split_tokens(&tokens[index + 2 ..])?;
          match arm {
            RawTExpr::And => {
              return Ok(
                PrecedenceResolvedRawTExpr::DAnd(
                  pexpr.clone(), Box::new(head), Box::new(tail)))
            },
            RawTExpr::Arrow => {
              return Ok(
                PrecedenceResolvedRawTExpr::DArrow(
                  pexpr.clone(), Box::new(head), Box::new(tail)))
            },
            _ => unreachable!()
          }
        },
        _ => {
          return Err(PrecedenceResolutionError);
        }
      }
    }
    // then go regular arrows
    if let RawTExpr::Arrow = item {
      let left_tokens = &tokens[..index];
      let right_tokens = &tokens[index + 1 ..];
      match (left_tokens.is_empty(), right_tokens.is_empty()) {
        (false, false) => {
          let left_part = split_tokens(left_tokens)?;
          let right_part = split_tokens(right_tokens)?;
          return Ok(PrecedenceResolvedRawTExpr::Arrow(Box::new(left_part), Box::new(right_part)))
        },
        (true, false) => {
          return resolve_app(tokens)
        },
        (true, true) => {
          return resolve_singular(item)
        },
        _ => return Err(PrecedenceResolutionError)
      }
    }
    // then equiv
    if let RawTExpr::Tilda = item {
      let left_tokens = &tokens[..index];
      let right_tokens = &tokens[index + 1 ..];
      match (left_tokens.is_empty(), right_tokens.is_empty()) {
        (false, false) => {
          let left_part = split_tokens(left_tokens)?;
          let right_part = split_tokens(right_tokens)?;
          return Ok(PrecedenceResolvedRawTExpr::Tilda(Box::new(left_part), Box::new(right_part)))
        },
        (true, false) => {
          return resolve_app(tokens)
        },
        (true, true) => {
          return resolve_singular(item)
        },
        _ => return Err(PrecedenceResolutionError)
      }
    }
    // then ors
    if let RawTExpr::Or = item {
      let left_tokens = &tokens[..index];
      let right_tokens = &tokens[index + 1 ..];
      match (left_tokens.is_empty(), right_tokens.is_empty()) {
        (false, false) => {
          let left_part = split_tokens(left_tokens)?;
          let right_part = split_tokens(right_tokens)?;
          return Ok(PrecedenceResolvedRawTExpr::Or(Box::new(left_part), Box::new(right_part)))
        },
        (true, false) => {
          return resolve_app(tokens)
        },
        (true, true) => {
          return resolve_singular(item)
        },
        _ => return Err(PrecedenceResolutionError)
      }
    }
    // then ands
    if let RawTExpr::And = item {
      let left_tokens = &tokens[..index];
      let right_tokens = &tokens[index + 1 ..];
      match (left_tokens.is_empty(), right_tokens.is_empty()) {
        (false, false) => {
          let left_part = split_tokens(left_tokens)?;
          let right_part = split_tokens(right_tokens)?;
          return Ok(PrecedenceResolvedRawTExpr::And(Box::new(left_part), Box::new(right_part)))
        },
        (true, false) => {
          return resolve_app(tokens)
        },
        (true, true) => {
          return resolve_singular(item)
        },
        _ => return Err(PrecedenceResolutionError)
      }
    }
    index += 1
  }
  // the computation should have diverged by this point if it has matched any builtins operators.
  // if it didnt then this tokens seqv is an application
  return resolve_app(tokens)
}
fn resolve_app(
  tokens: &[RawTExpr]
) -> Result<PrecedenceResolvedRawTExpr, PrecedenceResolutionError> {
  let head = resolve_precendece(&tokens[0])?;
  let mut args = Vec::new();
  for token in &tokens[1..] {
    match token {
      RawTExpr::Chars(chars) => {
        args.push(PrecedenceResolvedRawTExpr::Ref(*chars))
      },
      RawTExpr::Tokens(tokens) => {
        let subexpr = split_tokens(&tokens)?;
        args.push(subexpr)
      },
      RawTExpr::Let(let_) => {
        let LetGroup(items, focus) = let_.as_ref();
        let mut items_ = Vec::new();
        for (pexpr, texpr) in items {
          let texpr = resolve_precendece(texpr)?;
          items_.push((pexpr.clone(), texpr));
        }
        let focus = resolve_precendece(focus)?;
        return Ok(PrecedenceResolvedRawTExpr::Let(items_, Box::new(focus)))
      },
      RawTExpr::Lambda(Lambda(clauses)) => {
        let mut vec = Vec::new();
        for Clause(patterns, rhs) in clauses {
          let rhs = resolve_precendece(rhs)?;
          vec.push((patterns.clone(), rhs));
        }
        return Ok(PrecedenceResolvedRawTExpr::Lambda(vec))
      },
      RawTExpr::Star => args.push(PrecedenceResolvedRawTExpr::Star),
      _ => unreachable!()
    };
  }
  return Ok(PrecedenceResolvedRawTExpr::App(Box::new(head), args));
}
fn resolve_singular(
  texpr: &RawTExpr
) -> Result<PrecedenceResolvedRawTExpr, PrecedenceResolutionError> {
  match texpr {
    RawTExpr::Chars(chars) => return Ok(PrecedenceResolvedRawTExpr::Ref(*chars)),
    RawTExpr::Tokens(tokens) => return split_tokens(tokens),
    RawTExpr::Lift(_) => return Err(PrecedenceResolutionError),
    RawTExpr::Let(let_) => {
      let LetGroup(items, focus) = let_.as_ref();
      let mut items_ = Vec::new();
      for (pexpr, texpr) in items {
        let texpr = resolve_precendece(texpr)?;
        items_.push((pexpr.clone(), texpr));
      }
      let focus = resolve_precendece(focus)?;
      return Ok(PrecedenceResolvedRawTExpr::Let(items_, Box::new(focus)))
    },
    RawTExpr::Lambda(Lambda(clauses)) => {
      let mut vec = Vec::new();
      for Clause(patterns, rhs) in clauses {
        let rhs = resolve_precendece(rhs)?;
        vec.push((patterns.clone(), rhs));
      }
      return Ok(PrecedenceResolvedRawTExpr::Lambda(vec))
    },
    RawTExpr::Arrow => return Ok(PrecedenceResolvedRawTExpr::AtomRef(AtomRef::Arrow)),
    RawTExpr::Tilda => return Ok(PrecedenceResolvedRawTExpr::AtomRef(AtomRef::Tilda)),
    RawTExpr::Star => return Ok(PrecedenceResolvedRawTExpr::Star),
    RawTExpr::Or => return Ok(PrecedenceResolvedRawTExpr::AtomRef(AtomRef::Or)),
    RawTExpr::And =>  return Ok(PrecedenceResolvedRawTExpr::AtomRef(AtomRef::And)),
  }
}

struct PrecedentedExprRendererCtx {
  glyphs: String,
  chars: *const u8
}
impl PrecedentedExprRendererCtx {
  fn new(chars_ptr: *const u8) -> Self {
    Self { glyphs: String::new(), chars: chars_ptr }
  }
  fn render_precendented_expr(mut self, pr_expr: &PrecedenceResolvedRawTExpr) -> String {
    self.render_precedented_expr_impl(pr_expr);
    return self.glyphs
  }
  fn render_precedented_expr_impl(&mut self, pr_expr: &PrecedenceResolvedRawTExpr) {
    match pr_expr {
      PrecedenceResolvedRawTExpr::App(head, args) => {
        self.render_precedented_expr_impl(head);
        for arg in args {
          self.render_precedented_expr_impl(arg)
        }
      },
      PrecedenceResolvedRawTExpr::Ref(CharsData { offset_from_start, offset_from_head }) => unsafe {
        let ptr = self.chars.add(*offset_from_start as usize) ;
        let str = std::str::from_utf8_unchecked(
          std::slice::from_raw_parts(ptr, *offset_from_head as usize));
        self.glyphs.push_str(str)
      },
      PrecedenceResolvedRawTExpr::AtomRef(atom) => {
        let str = match atom {
          AtomRef::And => "and",
          AtomRef::Or => "or",
          AtomRef::Arrow => "->",
          AtomRef::Tilda => "~",
        };
        self.glyphs.push_str(str)
      },
      PrecedenceResolvedRawTExpr::Arrow(head, spine) => {
        self.render_precedented_expr_impl(head);
        self.glyphs.push_str(" -> ");
        self.render_precedented_expr_impl(spine)
      },
      pat@(PrecedenceResolvedRawTExpr::DArrow(pexpr, head, spine) |
      PrecedenceResolvedRawTExpr::DAnd(pexpr, head, spine)) => {
        self.glyphs.push('(');
        render_raw_pexpr(pexpr, self.chars, &mut self.glyphs);
        self.glyphs.push(':');
        self.render_precedented_expr_impl(head);
        match pat {
          PrecedenceResolvedRawTExpr::DArrow(..) => self.glyphs.push_str(") -> "),
          PrecedenceResolvedRawTExpr::DAnd(..) => self.glyphs.push_str(") and "),
          _ => unreachable!()
        }
        self.render_precedented_expr_impl(spine)
      },
      pat@(PrecedenceResolvedRawTExpr::And(l, r) |
      PrecedenceResolvedRawTExpr::Or(l, r)) => {
        self.render_precedented_expr_impl(l);
        match pat {
          PrecedenceResolvedRawTExpr::And(..) => self.glyphs.push_str("and"),
          PrecedenceResolvedRawTExpr::Or(..) => self.glyphs.push_str("or"),
          _ => unreachable!()
        }
        self.render_precedented_expr_impl(r)
      },
      PrecedenceResolvedRawTExpr::Star => self.glyphs.push('*'),
      PrecedenceResolvedRawTExpr::DArrow(_, _, _) => todo!(),
      PrecedenceResolvedRawTExpr::And(_, _) => todo!(),
      PrecedenceResolvedRawTExpr::DAnd(_, _, _) => todo!(),
      PrecedenceResolvedRawTExpr::Or(_, _) => todo!(),
      PrecedenceResolvedRawTExpr::Let(_, _) => todo!(),
      PrecedenceResolvedRawTExpr::Lambda(_) => todo!(),
      PrecedenceResolvedRawTExpr::Tilda(..) => todo!()
    }
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
  let mut parser = SourceTextParser::new(
    String::from_str(s).unwrap());
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
  let mut parser = SourceTextParser::new(
    String::from_str(s).unwrap());
  let depth = parser.probe_depth();
  assert!(depth == 1);
  let _ = parser.parse_identifier().unwrap();
  let depth = parser.probe_depth();
  assert!(depth == 0);
  let _ = parser.parse_identifier().unwrap();
}

#[test] #[ignore]
fn expr_parse() {
  let s =
    "".to_string() +
    "k : i = k => (* -> *) = (cons a _: expr a b) and jopa { govno => jopa } { govno => jopa }"
    ;
  let mut parser = SourceTextParser::new(s);
  let mut pager = RootAllocator::new();
  // let depth = parser.probe_depth();
  let expr = parser.parse_top_level_decl(&mut pager);
  match expr {
    Err(err) => println!("{:?}", err),
    Ok(Decl(name, tyexpr, oexpr)) => {
      let mut str = String::new();
      let chars = parser.chars.as_ptr();
      render_raw_texpr(&tyexpr, chars, &mut str);
      str.push_str(" = ");
      render_raw_texpr(&oexpr, chars, &mut str);
      println!("{}", str)
    }
  }
}

#[test] #[ignore]
fn precedenter_tests() {
  let s =
    "".to_string() +
    "k : * -> * = k (->) (-> * *) (* *) (and b) ~ d ({ a => a } a)"
    ;
  let mut parser = SourceTextParser::new(s);
  let mut pager = RootAllocator::new();
  let expr = parser.parse_top_level_decl(&mut pager);
  match expr {
    Err(err) => println!("{:?}", err),
    Ok(Decl(name, tyexpr, oexpr)) => {
      let chars = parser.chars.as_ptr();
      // let mut str = String::new();
      // render_raw_texpr(&tyexpr, chars, &mut str);
      // println!("{}", str);
      let pred_tyexpr = resolve_precendece(&oexpr);
      match pred_tyexpr {
        Err(_) => println!("fuck"),
        Ok(expr) => {
          println!("{:#?}", expr)
          // let ren = PrecedentedExprRendererCtx::new(chars);
          // let str = ren.render_precendented_expr(&expr);
          // println!("{}", str)
        }
      }
    }
  }
}