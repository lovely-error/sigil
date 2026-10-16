//! Safe, span-carrying lexer. No `unsafe`, no SIMD, no padding tricks.
//!
//! Tokens borrow from the input (`&str` slices); everything is total and the
//! lexer never panics on any UTF-8 input.
//!
//! Sorts: `*` (impredicative bottom) and `Type` levels — bare `Type` is an
//! ambiguous level (fresh variable per occurrence, generalized per def),
//! `Type0`, `Type1`, ... are concrete levels. `#` is gone (lex error).

use std::fmt;

/// Byte-offset span into the source.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

impl Span {
    pub fn new(start: usize, end: usize) -> Self {
        Self { start, end }
    }
    pub fn empty(at: usize) -> Self {
        Self { start: at, end: at }
    }
    /// Human-readable `line:col-line:col` for error messages.
    #[allow(dead_code)]
    pub fn display(&self, src: &str) -> String {
        let (l1, c1) = line_col(src, self.start);
        let (l2, c2) = line_col(src, self.end);
        format!("{l1}:{c1}-{l2}:{c2}")
    }
}

pub fn line_col(src: &str, off: usize) -> (usize, usize) {
    let off = off.min(src.len());
    let upto = &src[..off];
    let line = upto.bytes().filter(|&b| b == b'\n').count() + 1;
    // Character columns (not byte offsets): a multibyte character before the
    // offset must not shift the reported column.
    let col = upto.rfind('\n').map(|i| upto[i + 1..].chars().count() + 1).unwrap_or(upto.chars().count() + 1);
    (line, col)
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TokKind {
    Ident,
    Underscore,
    Star, // `*` (impredicative bottom)
    Type, // bare `Type` (ambiguous level: fresh variable per occurrence)
    TypeLevel(u32), // `Type0`, `Type1`, ... (concrete levels)
    Void, // `Void` (empty type; fully reserved keyword)
    Absurd, // `absurd` (vacuous eliminator; fully reserved keyword)
    Unit, // `Unit` (one-element type; fully reserved keyword)
    UnitRect, // `unit_rect` (unit eliminator; fully reserved keyword)
    W, // `W` (well-founded trees; fully reserved keyword)
    Sup, // `sup` (W introduction; fully reserved keyword)
    WRect, // `w_rect` (W eliminator; fully reserved keyword)
    Match, // `match` (dependent case analysis; fully reserved keyword)
    Return, // `return` (motive introducer in `match`; fully reserved keyword)
    Pipe, // `|` (match-clause separator)
    LBrace, // `{` (match-block open)
    RBrace, // `}` (match-block close)
    And, // `and` (dependent pair type former; fully reserved keyword)
    Fst, // `fst` (first projection; fully reserved keyword)
    Snd, // `snd` (second projection; fully reserved keyword)
    SigRect, // `sig_rect` (dependent eliminator; fully reserved keyword)
    Or, // `or` (binary sum type former; fully reserved keyword)
    Inl, // `inl` (left injection; fully reserved keyword)
    Inr, // `inr` (right injection; fully reserved keyword)
    EitherRect, // `either_rect` (sum eliminator; fully reserved keyword)
    Quot, // `Quot` (quotient type former; fully reserved keyword)
    QuotMk, // `quot_mk` (quotient introduction; fully reserved keyword)
    QuotLift, // `quot_lift` (quotient eliminator; fully reserved keyword)
    QuotInd, // `quot_ind` (dependent quotient eliminator; fully reserved keyword)
    QuotSound, // `quot_sound` (soundness axiom; fully reserved keyword)
    Def,
    Let,
    In,
    Fun,
    Arrow,    // `->`
    Backslash, // `\`
    Dot,      // `.`
    FatArrow, // `=>`
    Colon,
    Equals,
    Semi,
    Comma, // `,` (binary tuple `(a, b)` only; longer tuples deferred)
    LParen,
    RParen,
}

#[derive(Debug, Clone)]
pub struct Tok<'a> {
    pub kind: TokKind,
    pub text: &'a str,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct LexError {
    pub span: Span,
    pub msg: String,
}

impl fmt::Display for LexError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "lex error at {}: {}", self.span.start, self.msg)
    }
}

impl std::error::Error for LexError {}

fn is_ident_start(c: char) -> bool {
    c.is_alphabetic() || c == '_'
}

fn is_ident_cont(c: char) -> bool {
    c.is_alphanumeric() || c == '_' || c == '\''
}

pub fn lex(src: &str) -> Result<Vec<Tok<'_>>, LexError> {
    let mut toks: Vec<Tok<'_>> = Vec::new();
    let mut i = 0usize;
    while i < src.len() {
        let c = src[i..].chars().next().expect("non-empty");
        let clen = c.len_utf8();
        // whitespace
        if c.is_whitespace() {
            i += clen;
            continue;
        }
        // line comments: `--...` and `//...`
        if src[i..].starts_with("--") || src[i..].starts_with("//") {
            while i < src.len() && !src[i..].starts_with('\n') {
                let ch = src[i..].chars().next().expect("non-empty");
                i += ch.len_utf8();
            }
            continue;
        }
        let start = i;
        match c {
            '(' => {
                toks.push(Tok { kind: TokKind::LParen, text: &src[i..i + 1], span: Span::new(start, start + 1) });
                i += 1;
            }
            ')' => {
                toks.push(Tok { kind: TokKind::RParen, text: &src[i..i + 1], span: Span::new(start, start + 1) });
                i += 1;
            }
            ':' => {
                toks.push(Tok { kind: TokKind::Colon, text: &src[i..i + 1], span: Span::new(start, start + 1) });
                i += 1;
            }
            ';' => {
                toks.push(Tok { kind: TokKind::Semi, text: &src[i..i + 1], span: Span::new(start, start + 1) });
                i += 1;
            }
            ',' => {
                toks.push(Tok { kind: TokKind::Comma, text: &src[i..i + 1], span: Span::new(start, start + 1) });
                i += 1;
            }
            '.' => {
                toks.push(Tok { kind: TokKind::Dot, text: &src[i..i + 1], span: Span::new(start, start + 1) });
                i += 1;
            }
            '\\' => {
                toks.push(Tok { kind: TokKind::Backslash, text: &src[i..i + 1], span: Span::new(start, start + 1) });
                i += 1;
            }
            '*' => {
                toks.push(Tok { kind: TokKind::Star, text: &src[i..i + 1], span: Span::new(start, start + 1) });
                i += 1;
            }
            '#' => {
                return Err(LexError {
                    span: Span::new(start, start + 1),
                    msg: "`#` was removed: write `Type` (ambiguous level) or `Type0`, `Type1`, ... (concrete levels)".to_string(),
                });
            }
            '|' => {
                toks.push(Tok { kind: TokKind::Pipe, text: &src[i..i + 1], span: Span::new(start, start + 1) });
                i += 1;
            }
            '{' => {
                toks.push(Tok { kind: TokKind::LBrace, text: &src[i..i + 1], span: Span::new(start, start + 1) });
                i += 1;
            }
            '}' => {
                toks.push(Tok { kind: TokKind::RBrace, text: &src[i..i + 1], span: Span::new(start, start + 1) });
                i += 1;
            }
            '=' => {
                if src[i..].starts_with("=>") {
                    toks.push(Tok { kind: TokKind::FatArrow, text: &src[i..i + 2], span: Span::new(start, start + 2) });
                    i += 2;
                } else {
                    toks.push(Tok { kind: TokKind::Equals, text: &src[i..i + 1], span: Span::new(start, start + 1) });
                    i += 1;
                }
            }
            '-' => {
                if src[i..].starts_with("->") {
                    toks.push(Tok { kind: TokKind::Arrow, text: &src[i..i + 2], span: Span::new(start, start + 2) });
                    i += 2;
                } else {
                    return Err(LexError {
                        span: Span::new(start, start + 1),
                        msg: "unexpected character '-' (did you mean '->' or '--' comment?)".to_string(),
                    });
                }
            }
            _ if is_ident_start(c) => {
                let mut j = i + clen;
                while j < src.len() {
                    let d = src[j..].chars().next().expect("non-empty");
                    if is_ident_cont(d) {
                        j += d.len_utf8();
                    } else {
                        break;
                    }
                }
                let word = &src[i..j];
                let span = Span::new(i, j);
                // Bare `Type` is an ambiguous level; `Type<n>` is concrete.
                if word == "Type" {
                    toks.push(Tok { kind: TokKind::Type, text: word, span });
                } else if word.starts_with("Type")
                    && word.len() > 4
                    && word["Type".len()..].chars().all(|d| d.is_ascii_digit())
                {
                    let digits = &word["Type".len()..];
                    match digits.parse::<u32>() {
                        Ok(n) => toks.push(Tok { kind: TokKind::TypeLevel(n), text: word, span }),
                        Err(_) => {
                            return Err(LexError {
                                span,
                                msg: format!("universe level '{word}' overflows u32"),
                            });
                        }
                    }
                } else {
                    let kind = match word {
                        "_" => TokKind::Underscore,
                        "def" => TokKind::Def,
                        "let" => TokKind::Let,
                        "in" => TokKind::In,
                        "fun" => TokKind::Fun,
                        "Void" => TokKind::Void,
                        "absurd" => TokKind::Absurd,
                        "Unit" => TokKind::Unit,
                        "unit_rect" => TokKind::UnitRect,
                        "W" => TokKind::W,
                        "sup" => TokKind::Sup,
                        "w_rect" => TokKind::WRect,
                        "match" => TokKind::Match,
                        "return" => TokKind::Return,
                        "and" => TokKind::And,
                        "fst" => TokKind::Fst,
                        "snd" => TokKind::Snd,
                        "sig_rect" => TokKind::SigRect,
                        "or" => TokKind::Or,
                        "inl" => TokKind::Inl,
                        "inr" => TokKind::Inr,
                        "either_rect" => TokKind::EitherRect,
                        "Quot" => TokKind::Quot,
                        "quot_mk" => TokKind::QuotMk,
                        "quot_lift" => TokKind::QuotLift,
                        "quot_ind" => TokKind::QuotInd,
                        "quot_sound" => TokKind::QuotSound,
                        _ => TokKind::Ident,
                    };
                    toks.push(Tok { kind, text: word, span });
                }
                i = j;
            }
            _ => {
                return Err(LexError {
                    span: Span::new(start, start + clen),
                    msg: format!("unexpected character '{c}'"),
                });
            }
        }
    }
    Ok(toks)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lex_basic() {
        let toks = lex("def id : (T : *) -> T -> T = \\T x. x;").unwrap();
        assert!(toks.iter().any(|t| t.kind == TokKind::Def));
        assert!(toks.iter().any(|t| t.kind == TokKind::Arrow));
        assert!(toks.iter().any(|t| t.kind == TokKind::Backslash));
    }

    #[test]
    fn lex_sorts() {
        let toks = lex("* Type Type0 Type3").unwrap();
        let kinds: Vec<TokKind> = toks.iter().map(|t| t.kind.clone()).collect();
        assert_eq!(
            kinds,
            vec![
                TokKind::Star,
                TokKind::Type,
                TokKind::TypeLevel(0),
                TokKind::TypeLevel(3)
            ]
        );
        // `Type`-prefixed idents stay identifiers; `#` is gone with a hint.
        let toks = lex("Typefoo").unwrap();
        assert_eq!(toks[0].kind, TokKind::Ident);
        let err = lex("#").unwrap_err();
        assert!(err.msg.contains("Type"));
    }

    #[test]
    fn lex_void_absurd_keywords() {
        let toks = lex("Void absurd void Absurd").unwrap();
        let kinds: Vec<TokKind> = toks.iter().map(|t| t.kind.clone()).collect();
        assert_eq!(
            kinds,
            vec![TokKind::Void, TokKind::Absurd, TokKind::Ident, TokKind::Ident]
        );
    }

    #[test]
    fn lex_unit_keywords() {
        let toks = lex("Unit unit_rect unit ()").unwrap();
        let kinds: Vec<TokKind> = toks.iter().map(|t| t.kind.clone()).collect();
        assert_eq!(
            kinds,
            vec![
                TokKind::Unit,
                TokKind::UnitRect,
                TokKind::Ident,
                TokKind::LParen,
                TokKind::RParen,
            ]
        );
    }

    #[test]
    fn lex_w_keywords() {
        let toks = lex("W sup w_rect w Sup").unwrap();
        let kinds: Vec<TokKind> = toks.iter().map(|t| t.kind.clone()).collect();
        assert_eq!(
            kinds,
            vec![
                TokKind::W,
                TokKind::Sup,
                TokKind::WRect,
                TokKind::Ident,
                TokKind::Ident,
            ]
        );
    }

    #[test]
    fn lex_quot_keywords() {
        let toks = lex("Quot quot_mk quot_lift quot_ind quot_sound Quotx quot_m").unwrap();
        let kinds: Vec<TokKind> = toks.iter().map(|t| t.kind.clone()).collect();
        assert_eq!(
            kinds,
            vec![
                TokKind::Quot,
                TokKind::QuotMk,
                TokKind::QuotLift,
                TokKind::QuotInd,
                TokKind::QuotSound,
                TokKind::Ident,
                TokKind::Ident,
            ]
        );
    }
    #[test]
    fn lex_match_keywords() {
        let toks = lex("match e return P { inl a => b | inr c => d }").unwrap();
        let kinds: Vec<TokKind> = toks.iter().map(|t| t.kind.clone()).collect();
        assert_eq!(
            kinds,
            vec![
                TokKind::Match,
                TokKind::Ident,
                TokKind::Return,
                TokKind::Ident,
                TokKind::LBrace,
                TokKind::Inl,
                TokKind::Ident,
                TokKind::FatArrow,
                TokKind::Ident,
                TokKind::Pipe,
                TokKind::Inr,
                TokKind::Ident,
                TokKind::FatArrow,
                TokKind::Ident,
                TokKind::RBrace,
            ]
        );
    }

    #[test]
    fn lex_pair_keywords() {
        let toks = lex("and fst snd sig_rect (a, b)").unwrap();
        let kinds: Vec<TokKind> = toks.iter().map(|t| t.kind.clone()).collect();
        assert_eq!(
            kinds,
            vec![
                TokKind::And,
                TokKind::Fst,
                TokKind::Snd,
                TokKind::SigRect,
                TokKind::LParen,
                TokKind::Ident,
                TokKind::Comma,
                TokKind::Ident,
                TokKind::RParen,
            ]
        );
    }

    #[test]
    fn lex_sum_keywords() {
        let toks = lex("or inl inr either_rect orx inl_").unwrap();
        let kinds: Vec<TokKind> = toks.iter().map(|t| t.kind.clone()).collect();
        assert_eq!(
            kinds,
            vec![
                TokKind::Or,
                TokKind::Inl,
                TokKind::Inr,
                TokKind::EitherRect,
                TokKind::Ident,
                TokKind::Ident,
            ]
        );
    }

    #[test]
    fn lex_levels_accepted() {
        // Concrete levels lex (overflow is a clean error, not a panic).
        let toks = lex("Type1 Type42").unwrap();
        let kinds: Vec<TokKind> = toks.iter().map(|t| t.kind.clone()).collect();
        assert_eq!(kinds, vec![TokKind::TypeLevel(1), TokKind::TypeLevel(42)]);
        assert!(lex("Type99999999999999999999").is_err());
    }

    #[test]
    fn lex_comments() {
        let toks = lex("def -- comment\nid // comment\n: *").unwrap();
        assert!(toks.iter().any(|t| t.kind == TokKind::Def));
        assert!(toks.iter().any(|t| t.kind == TokKind::Colon));
    }

    #[test]
    fn lex_bad_char() {
        assert!(lex("@").is_err());
        assert!(lex("- x").is_err());
    }
}
