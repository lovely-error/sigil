//! Recursive-descent parser producing a surface AST with spans.
//!
//! Grammar (all safe, total, with backtracking only for the
//! `(x : A) -> B` vs `(e : T)` paren ambiguity):
//! ```text
//! program := decl* EOF
//! decl    := "def" name ":" expr "=" expr ";"?
//! expr    := let_expr | pi_expr
//! let_expr:= "let" name (":" expr)? "=" expr "in" expr
//! pi_expr := or_expr ("->" pi_expr)?               // right assoc
//!          | "(" name ":" expr ")" ("->" | "and") pi_expr
//! or_expr := and_expr ("or" or_expr)?              // right assoc, loosest
//! and_expr:= app_chain ("and" and_expr)?           // right assoc, tighter
//! atom    := app_chain
//! app_chain := simple+
//! simple  := var | "_" | sort | void | absurd | fst simple | snd simple
//!          | sig_rect | inl simple | inr simple | either_rect
//!          | Unit | unit_rect | "()" | W | sup | w_rect | match_expr
//!          | lambda | paren | tuple
//! match_expr := "match" expr "return" expr "{"
//!                 ("inl" binder "=>" expr "|" "inr" binder "=>" expr
//!                 |"inr" binder "=>" expr "|" "inl" binder "=>" expr) "}"
//!          (exactly one `inl` and one `inr` clause; binders are idents or `_`;
//!           no nesting — deferred with general patterns)
//! lambda  := "\" name* "." expr | "fun" name* "=>" expr
//! paren   := "(" expr ")" | "(" expr ":" expr ")"
//! tuple   := "(" expr "," expr ")"                 // binary only
//! sort    := "*" | "Type" | "Type" nat
//!           (`Type` is ambiguous — fresh level variable per occurrence;
//!            `Type0`, `Type1`, ... are concrete levels)
//! ```

use crate::core::Sort;
use crate::levels::{Level, fresh_level_var};
use crate::lexer::{Span, Tok, TokKind};
use std::fmt;

#[derive(Debug, Clone)]
pub struct ParseError {
    pub span: Span,
    pub msg: String,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "parse error at {}: {}", self.span.start, self.msg)
    }
}

impl std::error::Error for ParseError {}

// ---------------------------------------------------------------------------
// Surface AST
// ---------------------------------------------------------------------------

/// Surface expression. Names are owned `String`s; spans point into source.
#[derive(Debug, Clone)]
pub enum SExpr {
    Var { name: String, span: Span },
    Wild { span: Span },
    Sort { sort: Sort, span: Span },
    /// Empty type (no constructors).
    Void { span: Span },
    /// Vacuous eliminator `absurd : (A:*) -> Void -> A` (primitive constant).
    Absurd { span: Span },
    /// One-element type (`Unit : *`).
    Unit { span: Span },
    /// Its sole value `()`.
    Pt { span: Span },
    /// Unit eliminator `unit_rect : (P:(Unit -> *)) -> P () -> (u:Unit) -> P u`.
    UnitRect { span: Span },
    /// Well-founded trees `W : (A:*) -> (B:(A -> *)) -> *` (primitive).
    W { span: Span },
    /// Introduction `sup : (A:*) -> (B:(A->*)) -> (a:A) -> (f:(B a) -> W A B)
    /// -> W A B` (all args explicit, like other eliminators).
    Sup { span: Span },
    /// Eliminator `w_rect : (A:*) -> (B:(A->*)) -> (P:(W A B -> *))
    /// -> (s:(a:A) -> (f:(B a) -> W A B) -> ((b:B a) -> P (f b))
    /// -> P (sup A B a f)) -> (w:W A B) -> P w`.
    WRect { span: Span },
    Pi { param: String, #[allow(dead_code)] param_span: Span, dom: Box<SExpr>, cod: Box<SExpr>, span: Span },
    Arrow { dom: Box<SExpr>, cod: Box<SExpr>, span: Span },
    /// Dependent pair type `(x : A) and B`.
    Sigma { param: String, #[allow(dead_code)] param_span: Span, dom: Box<SExpr>, cod: Box<SExpr>, span: Span },
    /// Non-dependent pair type `A and B` (`and` binds tighter than `->`).
    And { dom: Box<SExpr>, cod: Box<SExpr>, span: Span },
    /// Binary tuple `(a, b)`: pair value only (use `and` for product types).
    Tuple { first: Box<SExpr>, second: Box<SExpr>, span: Span },
    /// First / second projection (`fst` takes one `simple`, so `fst f x`
    /// parses as `(fst f) x`).
    Fst { arg: Box<SExpr>, span: Span },
    Snd { arg: Box<SExpr>, span: Span },
    /// Dependent eliminator `sig_rect : (A:*) -> (B:A->*) -> (P:SigmaAB->*)
    /// -> ((a:A) -> (b:B a) -> P (a,b)) -> (p:SigmaAB) -> P p` (primitive
    /// constant; applies like any function, all args explicit).
    SigRect { span: Span },
    /// Non-dependent sum type `A or B` (`or` binds loosest, right assoc).
    Or { dom: Box<SExpr>, cod: Box<SExpr>, span: Span },
    /// Left / right injection (`inl` takes one `simple`, like `fst`).
    Inl { arg: Box<SExpr>, span: Span },
    Inr { arg: Box<SExpr>, span: Span },
    /// Sum eliminator `either_rect : (A:*) -> (B:*) -> (P:(A or B -> *))
    /// -> ((a:A) -> P (inl a)) -> ((b:B) -> P (inr b)) -> (e:A or B) -> P e`.
    EitherRect { span: Span },
    /// Quotient type former (`Quot` takes two `simple`s: carrier, relation).
    Quotient { dom: Box<SExpr>, rel: Box<SExpr>, span: Span },
    /// Quotient introduction (`quot_mk` takes one `simple`, like `inl`).
    QuotMk { arg: Box<SExpr>, span: Span },
    /// Quotient eliminator `quot_lift` (primitive constant).
    QuotLift { span: Span },
    /// Dependent quotient eliminator `quot_ind` (primitive constant).
    QuotInd { span: Span },
    /// Soundness axiom `quot_sound` (primitive constant).
    QuotSound { span: Span },
    /// Dependent case analysis `match e return P { inl x => b1 | inr y => b2 }`
    /// (exactly one clause per side; refinable, see `check.rs`).
    Match {
        scrut: Box<SExpr>,
        motive: Box<SExpr>,
        l_name: String,
        l_body: Box<SExpr>,
        r_name: String,
        r_body: Box<SExpr>,
        span: Span,
    },
    Lam { params: Vec<(String, Span)>, body: Box<SExpr>, span: Span },
    App { fun: Box<SExpr>, arg: Box<SExpr>, span: Span },
    Let { name: String, #[allow(dead_code)] name_span: Span, ann: Option<Box<SExpr>>, val: Box<SExpr>, body: Box<SExpr>, span: Span },
    Ann { term: Box<SExpr>, ty: Box<SExpr>, span: Span },
}

impl SExpr {
    pub fn span(&self) -> Span {
        match self {
            SExpr::Var { span, .. } | SExpr::Wild { span } | SExpr::Sort { span, .. }
            | SExpr::Void { span } | SExpr::Absurd { span }
            | SExpr::Unit { span } | SExpr::Pt { span } | SExpr::UnitRect { span }
            | SExpr::W { span } | SExpr::Sup { span } | SExpr::WRect { span }
            | SExpr::Pi { span, .. } | SExpr::Arrow { span, .. }
            | SExpr::Sigma { span, .. } | SExpr::And { span, .. } | SExpr::Tuple { span, .. }
            | SExpr::Fst { span, .. } | SExpr::Snd { span, .. } | SExpr::SigRect { span }
            | SExpr::Or { span, .. } | SExpr::Inl { span, .. } | SExpr::Inr { span, .. }
            | SExpr::EitherRect { span } | SExpr::Match { span, .. }
            | SExpr::Quotient { span, .. } | SExpr::QuotMk { span, .. }
            | SExpr::QuotLift { span } | SExpr::QuotInd { span } | SExpr::QuotSound { span } => *span,
            SExpr::Lam { span, .. }
            | SExpr::App { span, .. } | SExpr::Let { span, .. } | SExpr::Ann { span, .. } => *span,
        }
    }
}

#[derive(Debug, Clone)]
pub struct SDecl {
    pub name: String,
    #[allow(dead_code)]
    pub name_span: Span,
    /// Telescope binders in order (`def f (x:A) (y:B) ...`), each with its
    /// type expression. Empty for the plain `def f : T = v` form.
    pub params: Vec<(String, SExpr)>,
    /// Return annotation (`: R`), if given. `None` with a non-empty
    /// telescope means codomain inference: the body must elaborate as a
    /// type (formation-checked) and the recorded type is the telescope
    /// closed over the body.
    pub ret: Option<SExpr>,
    pub body: SExpr,
    #[allow(dead_code)]
    pub span: Span,
}

// ---------------------------------------------------------------------------
// Parser
// ---------------------------------------------------------------------------

pub struct Parser<'a> {
    toks: Vec<Tok<'a>>,
    pos: usize,
    src_len: usize,
}

/// Bound on parser recursion depth (functional style: each nested call gets
/// `d + 1`). Caps host-stack use on hostile deeply-nested input; legitimate
/// files nest dozens deep at most. (Sibling expressions restart at their
/// caller's depth, so file *size* is never limited — only *nesting*.)
/// Calibrated low for small host stacks (Windows main thread is ~1MB, debug
/// frames are fat): the trip point itself must fit comfortably.
pub const MAX_PARSE_DEPTH: u32 = 256;

impl<'a> Parser<'a> {
    pub fn new(toks: Vec<Tok<'a>>, src_len: usize) -> Self {
        Self { toks, pos: 0, src_len }
    }

    fn peek_kind(&self) -> Option<&TokKind> {
        self.toks.get(self.pos).map(|t| &t.kind)
    }

    fn peek(&self) -> Option<&Tok<'a>> {
        self.toks.get(self.pos)
    }

    fn next(&mut self) -> Option<Tok<'a>> {
        let t = self.toks.get(self.pos).cloned();
        if t.is_some() {
            self.pos += 1;
        }
        t
    }

    fn at_end(&self) -> bool {
        self.pos >= self.toks.len()
    }

    fn eof_span(&self) -> Span {
        Span::empty(self.src_len)
    }

    /// Nesting guard for the four self-recursive entry points below.
    fn check_depth(&self, d: u32) -> Result<(), ParseError> {
        if d > MAX_PARSE_DEPTH {
            Err(ParseError {
                span: self.peek().map(|t| t.span).unwrap_or_else(|| self.eof_span()),
                msg: format!("expression nesting too deep (limit {MAX_PARSE_DEPTH}); split the expression with `let`"),
            })
        } else {
            Ok(())
        }
    }

    fn expect(&mut self, want: &TokKind, what: &str) -> Result<Tok<'a>, ParseError> {
        match self.next() {
            Some(t) if std::mem::discriminant(&t.kind) == std::mem::discriminant(want) => Ok(t),
            Some(t) => Err(ParseError {
                span: t.span,
                msg: format!("expected {what}, found '{}'", t.text),
            }),
            None => Err(ParseError {
                span: self.eof_span(),
                msg: format!("expected {what}, found end of input"),
            }),
        }
    }

    fn expect_kind(&mut self, pred: impl Fn(&TokKind) -> bool, what: &str) -> Result<Tok<'a>, ParseError> {
        match self.next() {
            Some(t) if pred(&t.kind) => Ok(t),
            Some(t) => Err(ParseError {
                span: t.span,
                msg: format!("expected {what}, found '{}'", t.text),
            }),
            None => Err(ParseError {
                span: self.eof_span(),
                msg: format!("expected {what}, found end of input"),
            }),
        }
    }

    fn check(&self, kind: &TokKind) -> bool {
        match self.peek_kind() {
            Some(k) => std::mem::discriminant(k) == std::mem::discriminant(kind),
            None => false,
        }
    }

    pub fn parse_program(&mut self) -> Result<Vec<SDecl>, ParseError> {
        let mut decls = Vec::new();
        while !self.at_end() {
            // skip stray semicolons
            if self.check(&TokKind::Semi) {
                self.next();
                continue;
            }
            decls.push(self.parse_decl()?);
            // optional `;` separator
            if self.check(&TokKind::Semi) {
                self.next();
            }
        }
        Ok(decls)
    }

    fn parse_decl(&mut self) -> Result<SDecl, ParseError> {
        let def_tok = self.expect(&TokKind::Def, "'def'")?;
        let start = def_tok.span.start;
        let name_tok = self.expect_kind(|k| matches!(k, TokKind::Ident), "definition name")?;
        let name = name_tok.text.to_string();
        let name_span = name_tok.span;
        // Optional telescope: `def f (x : A) (y : B) ...`. A `(` here can
        // only start a binder group (the plain form continues with `:`).
        let mut params = Vec::new();
        while self.check(&TokKind::LParen) {
            self.next(); // (
            let param_tok = self.expect_kind(
                |k| matches!(k, TokKind::Ident | TokKind::Underscore),
                "binder name",
            )?;
            // `_` binders stay inaccessible, like everywhere else (the
            // underscore token's text is `_`).
            let param = param_tok.text.to_string();
            self.expect(&TokKind::Colon, "':'")?;
            let ty = self.parse_expr(0)?;
            self.expect(&TokKind::RParen, "')'")?;
            params.push((param, ty));
        }
        // Optional return annotation (`: R`). With a telescope but no `: R`,
        // the codomain is inferred (the body must be a type); without a
        // telescope the annotation is mandatory (`def f = v` is written
        // `def f : _ = v` instead).
        let ret = if self.check(&TokKind::Colon) {
            self.next(); // :
            Some(self.parse_expr(0)?)
        } else {
            None
        };
        if params.is_empty() && ret.is_none() {
            return Err(ParseError {
                span: self.peek().map(|t| t.span).unwrap_or_else(|| self.eof_span()),
                msg: "expected ':' with type annotation (bare `def f = v` is written `def f : _ = v`)".to_string(),
            });
        }
        self.expect(&TokKind::Equals, "'='")?;
        let body = self.parse_expr(0)?;
        let end = body.span().end;
        Ok(SDecl { name, name_span, params, ret, body, span: Span::new(start, end) })
    }

    fn parse_expr(&mut self, d: u32) -> Result<SExpr, ParseError> {
        self.check_depth(d)?;
        // `let` is the only prefix form at expr level.
        if self.check(&TokKind::Let) {
            return self.parse_let(d + 1);
        }
        self.parse_pi(d + 1)
    }

    fn parse_let(&mut self, d: u32) -> Result<SExpr, ParseError> {
        let let_tok = self.next().expect("checked");
        let start = let_tok.span.start;
        let name_tok = match self.next() {
            Some(t) if matches!(t.kind, TokKind::Ident | TokKind::Underscore) => t,
            Some(t) => {
                return Err(ParseError {
                    span: t.span,
                    msg: format!("expected let-bound name, found '{}'", t.text),
                });
            }
            None => {
                return Err(ParseError {
                    span: self.eof_span(),
                    msg: "expected let-bound name, found end of input".to_string(),
                });
            }
        };
        let name = name_tok.text.to_string();
        let name_span = name_tok.span;
        let ann = if self.check(&TokKind::Colon) {
            self.next();
            Some(Box::new(self.parse_expr(d + 1)?))
        } else {
            None
        };
        self.expect(&TokKind::Equals, "'=' in let")?;
        let val = self.parse_expr(d + 1)?;
        self.expect(&TokKind::In, "'in' in let")?;
        let body = self.parse_expr(d + 1)?;
        let end = body.span().end;
        Ok(SExpr::Let {
            name,
            name_span,
            ann,
            val: Box::new(val),
            body: Box::new(body),
            span: Span::new(start, end),
        })
    }

    fn parse_pi(&mut self, d: u32) -> Result<SExpr, ParseError> {
        self.check_depth(d)?;
        // Try dependent binder `(x : A) -> B` / `(x : A) and B` with
        // backtracking.
        if self.check(&TokKind::LParen) {
            if let Some(pi) = self.try_parse_named_pi(d + 1)? {
                // `try_parse_named_pi` returns Some only when the full
                // `(x : A) -> B` (or `and`) shape matched; otherwise it
                // backtracks. Codomain may itself be a Pi (right assoc).
                return Ok(pi);
            }
        }
        // Otherwise: three right-assoc levels, tightest first —
        // `and`, then `or`, then `->` loosest. So `A or B -> C` is
        // `(A or B) -> C`, `A -> B or C` is `A -> (B or C)`, and
        // `A and B or C` is `(A and B) or C`.
        let dom = self.parse_or(d + 1)?;
        if self.check(&TokKind::Arrow) {
            self.next();
            let cod = self.parse_pi(d + 1)?;
            let span = Span::new(dom.span().start, cod.span().end);
            return Ok(SExpr::Arrow { dom: Box::new(dom), cod: Box::new(cod), span });
        }
        Ok(dom)
    }

    fn parse_or(&mut self, d: u32) -> Result<SExpr, ParseError> {
        self.check_depth(d)?;
        let dom = self.parse_and(d + 1)?;
        if self.check(&TokKind::Or) {
            self.next();
            let cod = self.parse_or(d + 1)?;
            let span = Span::new(dom.span().start, cod.span().end);
            return Ok(SExpr::Or { dom: Box::new(dom), cod: Box::new(cod), span });
        }
        Ok(dom)
    }

    fn parse_and(&mut self, d: u32) -> Result<SExpr, ParseError> {
        self.check_depth(d)?;
        let dom = self.parse_app(d + 1)?;
        if self.check(&TokKind::And) {
            self.next();
            let cod = self.parse_and(d + 1)?;
            let span = Span::new(dom.span().start, cod.span().end);
            return Ok(SExpr::And { dom: Box::new(dom), cod: Box::new(cod), span });
        }
        Ok(dom)
    }

    /// Attempt `(name : dom) -> cod` or `(name : dom) and cod`. Returns
    /// `Ok(None)` (with cursor reset) when the input is not that shape, so
    /// plain parens still parse.
    fn try_parse_named_pi(&mut self, d: u32) -> Result<Option<SExpr>, ParseError> {
        let save = self.pos;
        let lparen = self.next().expect("checked");
        // need Ident|Underscore then Colon
        let name_tok = match self.peek().cloned() {
            Some(t) if matches!(t.kind, TokKind::Ident | TokKind::Underscore) => {
                self.next();
                t
            }
            _ => {
                self.pos = save;
                return Ok(None);
            }
        };
        if !self.check(&TokKind::Colon) {
            self.pos = save;
            return Ok(None);
        }
        self.next(); // :
        // Parse dom as a full expr; on failure, this IS a hard error only if
        // we are sure it was meant as Pi? We can't know, so backtrack and let
        // the normal path produce the error.
        let dom = match self.parse_expr(d + 1) {
            Ok(d) => d,
            Err(_) => {
                self.pos = save;
                return Ok(None);
            }
        };
        // need `)` then `->` or `and`
        if !self.check(&TokKind::RParen) {
            self.pos = save;
            return Ok(None);
        }
        self.next(); // )
        // `(x : A)` followed by `->` is Pi; by `and` is Sigma; anything else
        // is not a named binder (backtrack to plain parens).
        let is_sigma = if self.check(&TokKind::Arrow) {
            self.next(); // ->
            false
        } else if self.check(&TokKind::And) {
            self.next(); // and
            true
        } else {
            self.pos = save;
            return Ok(None);
        };
        let cod = self.parse_pi(d + 1)?;
        let span = Span::new(lparen.span.start, cod.span().end);
        if is_sigma {
            Ok(Some(SExpr::Sigma {
                param: name_tok.text.to_string(),
                param_span: name_tok.span,
                dom: Box::new(dom),
                cod: Box::new(cod),
                span,
            }))
        } else {
            Ok(Some(SExpr::Pi {
                param: name_tok.text.to_string(),
                param_span: name_tok.span,
                dom: Box::new(dom),
                cod: Box::new(cod),
                span,
            }))
        }
    }

    fn parse_app(&mut self, d: u32) -> Result<SExpr, ParseError> {
        let mut fun = self.parse_simple(d + 1)?;
        loop {
            // An argument starts a `simple`; arrows/colons/etc. end the chain.
            let starts_simple = match self.peek_kind() {
                Some(TokKind::Ident) | Some(TokKind::Underscore) | Some(TokKind::LParen)
                | Some(TokKind::Backslash) | Some(TokKind::Fun) => true,
                Some(TokKind::Star) | Some(TokKind::Type) | Some(TokKind::TypeLevel(_))
                | Some(TokKind::Void) | Some(TokKind::Absurd)
                | Some(TokKind::Unit) | Some(TokKind::UnitRect)
                | Some(TokKind::W) | Some(TokKind::Sup) | Some(TokKind::WRect)
                | Some(TokKind::Fst) | Some(TokKind::Snd)
                | Some(TokKind::SigRect) | Some(TokKind::Inl) | Some(TokKind::Inr)
                | Some(TokKind::EitherRect) | Some(TokKind::Match)
                | Some(TokKind::Quot) | Some(TokKind::QuotMk)
                | Some(TokKind::QuotLift) | Some(TokKind::QuotInd) | Some(TokKind::QuotSound) => true,
                _ => false,
            };
            if !starts_simple {
                break;
            }
            let arg = self.parse_simple(d + 1)?;
            let span = Span::new(fun.span().start, arg.span().end);
            fun = SExpr::App { fun: Box::new(fun), arg: Box::new(arg), span };
        }
        Ok(fun)
    }

    fn parse_simple(&mut self, d: u32) -> Result<SExpr, ParseError> {
        self.check_depth(d)?;
        match self.peek().cloned() {
            Some(t) if matches!(t.kind, TokKind::Ident) => {
                self.next();
                Ok(SExpr::Var { name: t.text.to_string(), span: t.span })
            }
            Some(t) if matches!(t.kind, TokKind::Underscore) => {
                self.next();
                Ok(SExpr::Wild { span: t.span })
            }
            Some(t) if matches!(t.kind, TokKind::Star) => {
                self.next();
                Ok(SExpr::Sort { sort: Sort::Star, span: t.span })
            }
            Some(t) if matches!(t.kind, TokKind::Type) => {
                self.next();
                // Ambiguous level: fresh variable per occurrence (typical
                // ambiguity — generalized per definition in `check.rs`).
                Ok(SExpr::Sort {
                    sort: Sort::Type(Level::Var(fresh_level_var())),
                    span: t.span,
                })
            }
            Some(t) if matches!(t.kind, TokKind::TypeLevel(_)) => {
                let n = match t.kind {
                    TokKind::TypeLevel(n) => n,
                    _ => unreachable!("guarded by matches"),
                };
                self.next();
                Ok(SExpr::Sort { sort: Sort::Type(Level::Const(n)), span: t.span })
            }
            Some(t) if matches!(t.kind, TokKind::Void) => {
                self.next();
                Ok(SExpr::Void { span: t.span })
            }
            Some(t) if matches!(t.kind, TokKind::Absurd) => {
                self.next();
                Ok(SExpr::Absurd { span: t.span })
            }
            Some(t) if matches!(t.kind, TokKind::Unit) => {
                self.next();
                Ok(SExpr::Unit { span: t.span })
            }
            Some(t) if matches!(t.kind, TokKind::UnitRect) => {
                self.next();
                Ok(SExpr::UnitRect { span: t.span })
            }
            Some(t) if matches!(t.kind, TokKind::W) => {
                self.next();
                Ok(SExpr::W { span: t.span })
            }
            Some(t) if matches!(t.kind, TokKind::Sup) => {
                self.next();
                Ok(SExpr::Sup { span: t.span })
            }
            Some(t) if matches!(t.kind, TokKind::WRect) => {
                self.next();
                Ok(SExpr::WRect { span: t.span })
            }
            Some(t) if matches!(t.kind, TokKind::SigRect) => {
                self.next();
                Ok(SExpr::SigRect { span: t.span })
            }
            Some(t) if matches!(t.kind, TokKind::Inl | TokKind::Inr) => {
                // Injection of one `simple`, like projections: `inl f x`
                // parses as `(inl f) x` (ill-typed unless `f` fits, as usual).
                let is_inl = matches!(t.kind, TokKind::Inl);
                self.next();
                let start = t.span.start;
                let arg = self.parse_simple(d + 1)?;
                let span = Span::new(start, arg.span().end);
                if is_inl {
                    Ok(SExpr::Inl { arg: Box::new(arg), span })
                } else {
                    Ok(SExpr::Inr { arg: Box::new(arg), span })
                }
            }
            Some(t) if matches!(t.kind, TokKind::EitherRect) => {
                self.next();
                Ok(SExpr::EitherRect { span: t.span })
            }
            Some(t) if matches!(t.kind, TokKind::Quot) => {
                // Former takes two `simple`s: carrier then relation.
                // (`Quot A R x` parses as `(Quot A R) x` via application.)
                self.next();
                let start = t.span.start;
                let dom = self.parse_simple(d + 1)?;
                let rel = self.parse_simple(d + 1)?;
                let span = Span::new(start, rel.span().end);
                Ok(SExpr::Quotient { dom: Box::new(dom), rel: Box::new(rel), span })
            }
            Some(t) if matches!(t.kind, TokKind::QuotMk) => {
                // Introduction of one `simple`, like injections: `quot_mk f x`
                // parses as `(quot_mk f) x`.
                self.next();
                let start = t.span.start;
                let arg = self.parse_simple(d + 1)?;
                let span = Span::new(start, arg.span().end);
                Ok(SExpr::QuotMk { arg: Box::new(arg), span })
            }
            Some(t) if matches!(t.kind, TokKind::QuotLift) => {
                self.next();
                Ok(SExpr::QuotLift { span: t.span })
            }
            Some(t) if matches!(t.kind, TokKind::QuotInd) => {
                self.next();
                Ok(SExpr::QuotInd { span: t.span })
            }
            Some(t) if matches!(t.kind, TokKind::QuotSound) => {
                self.next();
                Ok(SExpr::QuotSound { span: t.span })
            }
            Some(t) if matches!(t.kind, TokKind::Match) => self.parse_match(d + 1),
            Some(t) if matches!(t.kind, TokKind::Fst | TokKind::Snd) => {
                // Projection of one `simple`: `fst f x` is `(fst f) x`.
                let is_fst = matches!(t.kind, TokKind::Fst);
                self.next();
                let start = t.span.start;
                let arg = self.parse_simple(d + 1)?;
                let span = Span::new(start, arg.span().end);
                if is_fst {
                    Ok(SExpr::Fst { arg: Box::new(arg), span })
                } else {
                    Ok(SExpr::Snd { arg: Box::new(arg), span })
                }
            }
            Some(t) if matches!(t.kind, TokKind::Backslash | TokKind::Fun) => self.parse_lambda(d + 1),
            Some(t) if matches!(t.kind, TokKind::LParen) => self.parse_paren(d + 1),
            Some(t) => Err(ParseError {
                span: t.span,
                msg: format!("expected an expression, found '{}'", t.text),
            }),
            None => Err(ParseError {
                span: self.eof_span(),
                msg: "expected an expression, found end of input".to_string(),
            }),
        }
    }

    /// `match e return P { inl x => b1 | inr y => b2 }` (either order).
    /// Exactly one `inl` and one `inr` clause, each binding one ident (or
    /// `_`); anything else is a parse error (no nesting, no wildcards —
    /// deferred with general patterns). Coverage is therefore syntactic.
    fn parse_match(&mut self, d: u32) -> Result<SExpr, ParseError> {
        let head = self.next().expect("checked");
        let start = head.span.start;
        let scrut = self.parse_expr(d + 1)?;
        self.expect(&TokKind::Return, "'return' with motive in match")?;
        let motive = self.parse_expr(d + 1)?;
        self.expect(&TokKind::LBrace, "'{' with match clauses")?;
        // First clause.
        let (first_left, first_name, first_body) = self.parse_match_clause(d + 1)?;
        self.expect(&TokKind::Pipe, "'|' between match clauses")?;
        // Second clause.
        let (second_left, second_name, second_body) = self.parse_match_clause(d + 1)?;
        self.expect(&TokKind::RBrace, "'}' after match clauses")?;
        if first_left == second_left {
            let which = if first_left { "inl" } else { "inr" };
            return Err(ParseError {
                span: Span::new(start, second_body.span().end),
                msg: format!(
                    "match on sums needs exactly one `inl` and one `inr` clause (two `{which}` given)"
                ),
            });
        }
        let end = second_body.span().end;
        let span = Span::new(start, end);
        // Normalize order: left/inl first regardless of surface order.
        let ((l_name, l_body), (r_name, r_body)) = if first_left {
            ((first_name, first_body), (second_name, second_body))
        } else {
            ((second_name, second_body), (first_name, first_body))
        };
        Ok(SExpr::Match {
            scrut: Box::new(scrut),
            motive: Box::new(motive),
            l_name,
            l_body: Box::new(l_body),
            r_name,
            r_body: Box::new(r_body),
            span,
        })
    }

    /// One match clause: `inl x => body` or `inr y => body`. Returns
    /// (is_left, binder_name, body).
    fn parse_match_clause(&mut self, d: u32) -> Result<(bool, String, SExpr), ParseError> {
        let tok = match self.next() {
            Some(t) if matches!(t.kind, TokKind::Inl) => (true, t),
            Some(t) if matches!(t.kind, TokKind::Inr) => (false, t),
            Some(t) => {
                return Err(ParseError {
                    span: t.span,
                    msg: format!(
                        "expected `inl <name> => ...` or `inr <name> => ...` in match (found '{}')",
                        t.text
                    ),
                });
            }
            None => {
                return Err(ParseError {
                    span: self.eof_span(),
                    msg: "expected match clause, found end of input".to_string(),
                });
            }
        };
        let (is_left, _head) = tok;
        let binder = match self.next() {
            Some(t) if matches!(t.kind, TokKind::Ident | TokKind::Underscore) => t.text.to_string(),
            Some(t) => {
                return Err(ParseError {
                    span: t.span,
                    msg: format!("expected a binder name after `inl`/`inr`, found '{}'", t.text),
                });
            }
            None => {
                return Err(ParseError {
                    span: self.eof_span(),
                    msg: "expected a binder name after `inl`/`inr`, found end of input".to_string(),
                });
            }
        };
        self.expect(&TokKind::FatArrow, "'=>' after match pattern binder")?;
        let body = self.parse_expr(d + 1)?;
        Ok((is_left, binder, body))
    }

    fn parse_lambda(&mut self, d: u32) -> Result<SExpr, ParseError> {
        let head = self.next().expect("checked");
        let start = head.span.start;
        let is_backslash = matches!(head.kind, TokKind::Backslash);
        let mut params: Vec<(String, Span)> = Vec::new();
        loop {
            match self.peek().cloned() {
                Some(t) if matches!(t.kind, TokKind::Ident | TokKind::Underscore) => {
                    self.next();
                    params.push((t.text.to_string(), t.span));
                }
                _ => break,
            }
        }
        if params.is_empty() {
            let sp = self.peek().map(|t| t.span).unwrap_or_else(|| self.eof_span());
            return Err(ParseError {
                span: sp,
                msg: if is_backslash {
                    "expected at least one binder after '\\'".to_string()
                } else {
                    "expected at least one binder after 'fun'".to_string()
                },
            });
        }
        if is_backslash {
            self.expect(&TokKind::Dot, "'.' after lambda binders")?;
        } else {
            self.expect(&TokKind::FatArrow, "'=>' after 'fun' binders")?;
        }
        let body = self.parse_expr(d + 1)?;
        let end = body.span().end;
        Ok(SExpr::Lam { params, body: Box::new(body), span: Span::new(start, end) })
    }

    fn parse_paren(&mut self, d: u32) -> Result<SExpr, ParseError> {
        let lparen = self.next().expect("checked");
        // `()` is the sole value of the `Unit` type.
        if self.check(&TokKind::RParen) {
            let r = self.next().expect("checked");
            return Ok(SExpr::Pt { span: Span::new(lparen.span.start, r.span.end) });
        }
        let inner = self.parse_expr(d + 1)?;
        if self.check(&TokKind::Comma) {
            self.next();
            let second = self.parse_expr(d + 1)?;
            if self.check(&TokKind::Comma) {
                let c = self.next().expect("checked");
                return Err(ParseError {
                    span: Span::new(lparen.span.start, c.span.end),
                    msg: "tuples are binary only; nest them like (a, (b, c))".to_string(),
                });
            }
            let r = self.expect(&TokKind::RParen, "')' after tuple")?;
            let span = Span::new(lparen.span.start, r.span.end);
            return Ok(SExpr::Tuple { first: Box::new(inner), second: Box::new(second), span });
        }
        if self.check(&TokKind::Colon) {
            self.next();
            let ty = self.parse_expr(d + 1)?;
            let r = self.expect(&TokKind::RParen, "')' after annotation")?;
            let span = Span::new(lparen.span.start, r.span.end);
            return Ok(SExpr::Ann { term: Box::new(inner), ty: Box::new(ty), span });
        }
        let r = self.expect(&TokKind::RParen, "')'")?;
        // Keep the inner span for grouping (no new node needed), but extend
        // to parens for error locality. We wrap in Ann-free grouping by
        // returning inner; span info loss is acceptable for MVP. To keep
        // spans tight for elaboration errors, rebuild is skipped.
        let _ = (lparen, r);
        Ok(inner)
    }
}

/// Parse a whole program from source text.
pub fn parse_program(src: &str) -> Result<Vec<SDecl>, ParseError> {
    use crate::lexer::lex;
    match lex(src) {
        Ok(toks) => {
            let mut p = Parser::new(toks, src.len());
            p.parse_program()
        }
        Err(e) => Err(ParseError { span: e.span, msg: e.msg }),
    }
}

/// Parse a single expression (for tests / REPL snippets).
#[allow(dead_code)]
pub fn parse_expr(src: &str) -> Result<SExpr, ParseError> {
    use crate::lexer::lex;
    match lex(src) {
        Ok(toks) => {
            let mut p = Parser::new(toks, src.len());
            let e = p.parse_expr(0)?;
            if !p.at_end() {
                let t = p.peek().expect("not end");
                return Err(ParseError {
                    span: t.span,
                    msg: format!("unexpected trailing token '{}'", t.text),
                });
            }
            Ok(e)
        }
        Err(e) => Err(ParseError { span: e.span, msg: e.msg }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn pe(s: &str) -> SExpr {
        parse_expr(s).unwrap_or_else(|e| panic!("parse failed for {s:?}: {e:?}"))
    }

    #[test]
    fn arrow_is_right_assoc() {
        let e = pe("Type -> Type -> Type");
        assert!(matches!(e, SExpr::Arrow { .. }));
        if let SExpr::Arrow { cod, .. } = e {
            assert!(matches!(*cod, SExpr::Arrow { .. }));
        }
    }

    #[test]
    fn dependent_pi() {
        let e = pe("(T : *) -> T -> T");
        assert!(matches!(e, SExpr::Pi { .. }));
    }

    #[test]
    fn level_sorts_parse() {
        // `*` is the bottom; bare `Type` is ambiguous (fresh var each
        // occurrence); `Type<n>` is concrete; `#` is gone.
        assert!(matches!(pe("*"), SExpr::Sort { .. }));
        if let SExpr::Sort { sort, .. } = pe("Type") {
            assert!(matches!(sort, Sort::Type(Level::Var(_))));
        } else {
            panic!("bare Type must parse as a sort");
        }
        // Two occurrences mint distinct variables (typical ambiguity).
        if let (SExpr::Sort { sort: s1, .. }, SExpr::Sort { sort: s2, .. }) =
            (pe("Type"), pe("Type"))
        {
            assert_ne!(s1, s2);
        }
        if let SExpr::Sort { sort, .. } = pe("Type2") {
            assert_eq!(sort, Sort::Type(Level::Const(2)));
        } else {
            panic!("Type2 must parse as a concrete sort");
        }
        assert!(parse_program("def a : Type0 = *;").is_ok());
        assert!(parse_expr("#").is_err());
    }

    #[test]
    fn telescope_parses() {
        // Plain form: no telescope, return type present.
        let ds = parse_program("def a : Type0 = *;").unwrap();
        assert!(ds[0].params.is_empty());
        assert!(ds[0].ret.is_some());
        // Telescope with return type (sugar) and without (inference).
        let ds = parse_program("def f (x : *) (y : *) : * = x;").unwrap();
        assert_eq!(ds[0].params.len(), 2);
        assert_eq!(ds[0].params[0].0, "x");
        assert!(ds[0].ret.is_some());
        let ds = parse_program("def f (x : *) = x;").unwrap();
        assert_eq!(ds[0].params.len(), 1);
        assert!(ds[0].ret.is_none());
        // Wildcard binders allowed, like everywhere else.
        assert!(parse_program("def f (_ : *) = *;").is_ok());
        // Bare `def f = v` stays rejected (written `def f : _ = v`).
        assert!(parse_program("def f = *;").is_err());
        // Unparenthesized binders are not a telescope.
        assert!(parse_program("def f x : * = x;").is_err());
    }

    #[test]
    fn unit_parses() {
        assert!(matches!(pe("Unit"), SExpr::Unit { .. }));
        assert!(matches!(pe("()"), SExpr::Pt { .. }));
        assert!(matches!(pe("unit_rect"), SExpr::UnitRect { .. }));
        assert!(matches!(pe("unit_rect P b ()"), SExpr::App { .. }));
        // Still reserved: neither can be bound or redefined.
        assert!(parse_program("def Unit : * = *;").is_err());
        assert!(parse_program("def unit_rect : * = *;").is_err());
        assert!(parse_expr("\\Unit. Unit").is_err());
    }

    #[test]
    fn w_parses() {
        assert!(matches!(pe("W"), SExpr::W { .. }));
        assert!(matches!(pe("sup"), SExpr::Sup { .. }));
        assert!(matches!(pe("w_rect"), SExpr::WRect { .. }));
        assert!(matches!(pe("w_rect A B P s w"), SExpr::App { .. }));
        // Reserved: none can be bound or redefined.
        assert!(parse_program("def W : * = *;").is_err());
        assert!(parse_program("def sup : * = *;").is_err());
        assert!(parse_program("def w_rect : * = *;").is_err());
        assert!(parse_expr("\\W. W").is_err());
    }

    #[test]
    fn void_absurd_parse() {
        assert!(matches!(pe("Void"), SExpr::Void { .. }));
        assert!(matches!(pe("absurd"), SExpr::Absurd { .. }));
        assert!(matches!(pe("absurd *"), SExpr::App { .. }));
        // Neither can be bound or redefined: both are keywords, not idents.
        assert!(parse_program("def Void : * = *;").is_err());
        assert!(parse_program("def absurd : * = *;").is_err());
        assert!(parse_expr("\\Void. Void").is_err());
    }

    #[test]
    fn numbered_levels_accepted() {
        // Concrete levels are ordinary sorts now.
        assert!(parse_program("def a : * = Type1;").is_ok());
        if let SExpr::Sort { sort, .. } = pe("Type1") {
            assert_eq!(sort, Sort::Type(Level::Const(1)));
        }
    }

    #[test]
    fn plain_paren_is_grouping() {
        let e = pe("(Type -> Type)");
        assert!(matches!(e, SExpr::Arrow { .. }));
    }

    #[test]
    fn annotation_paren() {
        let e = pe("(x : Type)");
        assert!(matches!(e, SExpr::Ann { .. }));
    }

    #[test]
    fn lambda_forms() {
        assert!(matches!(pe("\\x. x"), SExpr::Lam { .. }));
        assert!(matches!(pe("\\x y. x"), SExpr::Lam { .. }));
        assert!(matches!(pe("fun x => x"), SExpr::Lam { .. }));
        assert!(matches!(pe("\\_. x"), SExpr::Lam { .. }));
    }

    #[test]
    fn app_is_left_assoc() {
        let e = pe("f x y");
        assert!(matches!(e, SExpr::App { .. }));
    }

    #[test]
    fn let_expr() {
        let e = pe("let x : Type = Type in x");
        assert!(matches!(e, SExpr::Let { .. }));
        let e2 = pe("let x = \\y. y in x");
        assert!(matches!(e2, SExpr::Let { .. }));
    }

    #[test]
    fn decl_requires_def() {
        assert!(parse_program("id : Type = Type;").is_err());
        assert!(parse_program("def id : Type = Type;").is_ok());
    }

    #[test]
    fn empty_parens_are_unit_value() {
        // `()` used to be rejected (no Unit type); now it is `Unit`'s value.
        // (Longer empty-ish forms still fail: `(,)` needs operands.)
        assert!(matches!(pe("()"), SExpr::Pt { .. }));
        assert!(parse_expr("(,)").is_err());
    }

    #[test]
    fn and_binds_tighter_than_arrow() {
        // `A and B -> C` is `(A and B) -> C`.
        let e = pe("a and b -> c");
        assert!(matches!(e, SExpr::Arrow { .. }));
        if let SExpr::Arrow { dom, .. } = e {
            assert!(matches!(*dom, SExpr::And { .. }));
        }
        // `A -> B and C` is `A -> (B and C)`.
        let e2 = pe("a -> b and c");
        if let SExpr::Arrow { cod, .. } = e2 {
            assert!(matches!(*cod, SExpr::And { .. }));
        } else {
            panic!("expected arrow");
        }
        // `and` is right assoc.
        let e3 = pe("a and b and c");
        if let SExpr::And { cod, .. } = e3 {
            assert!(matches!(*cod, SExpr::And { .. }));
        } else {
            panic!("expected and");
        }
    }

    #[test]
    fn named_sigma_parses() {
        let e = pe("(x : a) and b");
        assert!(matches!(e, SExpr::Sigma { .. }));
        // Plain parens still group: `(a -> b) and c`.
        let e2 = pe("(a -> b) and c");
        assert!(matches!(e2, SExpr::And { .. }));
    }

    #[test]
    fn tuple_parses() {
        assert!(matches!(pe("(a, b)"), SExpr::Tuple { .. }));
        assert!(parse_expr("(a, b, c)").is_err());
    }

    #[test]
    fn fst_takes_one_simple() {
        // `fst f x` is `(fst f) x`, not `fst (f x)`.
        let e = pe("fst f x");
        assert!(matches!(e, SExpr::App { .. }));
        if let SExpr::App { fun, .. } = e {
            assert!(matches!(*fun, SExpr::Fst { .. }));
        }
        assert!(matches!(pe("snd (f x)"), SExpr::Snd { .. }));
    }

    #[test]
    fn pair_keywords_reserved() {
        assert!(parse_program("def and : * = *;").is_err());
        assert!(parse_program("def fst : * = *;").is_err());
        assert!(parse_program("def sig_rect : * = *;").is_err());
        assert!(parse_expr("\\and. and").is_err());
    }

    #[test]
    fn sig_rect_applies_as_chain() {
        // `sig_rect A B P f p` is a left-nested App chain over the constant.
        let e = pe("sig_rect A B P f p");
        assert!(matches!(e, SExpr::App { .. }));
    }

    #[test]
    fn or_precedence() {
        // `and` tighter than `or` tighter than `->`, all right assoc.
        let e = pe("a and b or c");
        assert!(matches!(e, SExpr::Or { .. }));
        if let SExpr::Or { dom, .. } = e {
            assert!(matches!(*dom, SExpr::And { .. }));
        }
        let e2 = pe("a or b -> c");
        assert!(matches!(e2, SExpr::Arrow { .. }));
        if let SExpr::Arrow { dom, .. } = e2 {
            assert!(matches!(*dom, SExpr::Or { .. }));
        }
        let e3 = pe("a -> b or c");
        if let SExpr::Arrow { cod, .. } = e3 {
            assert!(matches!(*cod, SExpr::Or { .. }));
        } else {
            panic!("expected arrow");
        }
        let e4 = pe("a or b or c");
        if let SExpr::Or { cod, .. } = e4 {
            assert!(matches!(*cod, SExpr::Or { .. }));
        } else {
            panic!("expected or");
        }
    }

    #[test]
    fn injections_parse() {
        assert!(matches!(pe("inl a"), SExpr::Inl { .. }));
        assert!(matches!(pe("inr (f x)"), SExpr::Inr { .. }));
        // `inl f x` is `(inl f) x`.
        let e = pe("inl f x");
        assert!(matches!(e, SExpr::App { .. }));
        assert!(matches!(pe("either_rect A B P f g e"), SExpr::App { .. }));
    }

    #[test]
    fn sum_keywords_reserved() {
        assert!(parse_program("def or : * = *;").is_err());
        assert!(parse_program("def inl : * = *;").is_err());
        assert!(parse_program("def either_rect : * = *;").is_err());
        assert!(parse_expr("\\or. or").is_err());
    }

    #[test]
    fn quot_parses() {
        // Former takes carrier + relation; intro takes one simple.
        let e = pe("Quot A R");
        assert!(matches!(e, SExpr::Quotient { .. }));
        assert!(matches!(pe("quot_mk a"), SExpr::QuotMk { .. }));
        // `quot_mk f x` is `(quot_mk f) x`; eliminators apply normally.
        assert!(matches!(pe("quot_mk f x"), SExpr::App { .. }));
        assert!(matches!(
            pe("quot_lift A R B f h q"),
            SExpr::App { .. }
        ));
        assert!(matches!(pe("quot_ind"), SExpr::QuotInd { .. }));
        assert!(matches!(pe("quot_sound A R a b h"), SExpr::App { .. }));
    }

    #[test]
    fn quot_keywords_reserved() {
        assert!(parse_program("def Quot : * = *;").is_err());
        assert!(parse_program("def quot_mk : * = *;").is_err());
        assert!(parse_program("def quot_lift : * = *;").is_err());
        assert!(parse_program("def quot_ind : * = *;").is_err());
        assert!(parse_program("def quot_sound : * = *;").is_err());
        assert!(parse_expr("\\Quot. Quot").is_err());
    }
    #[test]
    fn match_parses() {
        let e = pe("match e return P { inl x => x | inr y => y }");
        assert!(matches!(e, SExpr::Match { .. }));
        // Either clause order accepted, normalized left-first.
        let e2 = pe("match e return P { inr y => y | inl x => x }");
        if let SExpr::Match { l_name, r_name, .. } = e2 {
            assert_eq!((l_name.as_str(), r_name.as_str()), ("x", "y"));
        } else {
            panic!("expected match");
        }
        // `_` binders allowed.
        assert!(matches!(pe("match e return P { inl _ => e | inr _ => e }"), SExpr::Match { .. }));
    }

    #[test]
    fn match_rejects_bad_shapes() {
        // Missing a side.
        assert!(parse_expr("match e return P { inl x => x }").is_err());
        // Duplicated side.
        assert!(parse_expr("match e return P { inl x => x | inl y => y }").is_err());
        // Non-constructor head.
        assert!(parse_expr("match e return P { x => x | inr y => y }").is_err());
        // Missing binder.
        assert!(parse_expr("match e return P { inl => e | inr y => y }").is_err());
        // `match` itself is reserved.
        assert!(parse_program("def match : * = *;").is_err());
    }

    #[test]
    fn deep_nesting_rejected_cleanly() {
        // Parser depth limit: hostile nesting is a clean error, not a crash.
        let mut s = String::from("def a : ");
        for _ in 0..2000 {
            s.push('(');
        }
        s.push('*');
        for _ in 0..2000 {
            s.push(')');
        }
        s.push(';');
        assert!(parse_program(&s).is_err());
    }
}
