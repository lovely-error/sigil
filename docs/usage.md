# Usage

## Build and test

Prerequisites: Rust toolchain (`cargo`). No dependencies beyond the standard
library. `#![forbid(unsafe_code)]`.

```sh
cargo build              # debug binary at target/debug/sigil-neo
cargo run -- --help      # print help (same as sigil-neo --help)
cargo test               # 153 unit + end-to-end tests (examples/ via include_str!)
cargo run -- check examples/prelude.sig   # exits 0 on success
```

Release uses `opt-level = 2` (see `Cargo.toml`). Debug builds run the checker
on a 256 MiB worker thread so deep-but-legal input becomes a checked error
instead of a host stack overflow (`src/cli.rs:check_program_big_stack`).

## CLI

```
sigil-neo check <file.sig>   scope-check + type-check a file
sigil-neo <file.sig>          same as `check`
sigil-neo check -             read the program from stdin
sigil-neo --help              this message (also -h, help, no args)
```

Exit codes:

- `0` — all definitions checked OK.
- `1` — file parsed but some definition failed, or stdin/file could not be
  read. Report still prints per-def results.
- `2` — CLI misuse: `sigil-neo check` with no file, or unknown ` -flag`
  (bare `-` is the one exception: it means stdin).

Report format (stdout):

```text
def id (ok) : ((T : *) -> (T -> T))
  = \T x . x
def bad (FAIL) : Void
  = (bigalias Void)
  error: (bigalias Void) : Type(?4) :! Void
=> all definitions checked OK
=> some definitions FAILED to check
```

`Type(?n)` is an ambiguous level variable. Errors carry spans rendered as
`line:col` where available (holes especially).

Stdin example (PowerShell):

```powershell
Get-Content examples\prelude.sig | cargo run --quiet -- check -
Get-Content examples\prelude.sig | cargo run --quiet -- -
```

## Files

- Extension is conventional `.sig`, not enforced.
- A program is `def ... ; def ... ;` — semicolon-separated, trailing `;`
  required per def.
- Comments: `-- comment` or `// comment` to end of line.
- Order matters: no forward or self references. Referencing a failed earlier
  def is itself an error (avoids cascades).

## Definitions

Plain:

```sigil
def id : (T : *) -> T -> T = \T x. x;
def viaLet : Type = let X : Type = * in X;
```

Telescope with return type (sugar for Pi/Lam):

```sigil
def const (A : *) (B : *) : A -> B -> A = \x y. x;
-- means: def const : (A:*) -> (B:*) -> A -> B -> A = \A B x y. x;
```

Telescope without return type (codomain inference for families):

```sigil
def bigalias (A : Type) = A;
-- recorded type is (A:Type(?0)) -> Type(?0), value \A. A.
-- The body must elaborate as a *type*; a term body is rejected.
```

Notes:

- Bare `def f = v;` is rejected. Write `def f : _ = v;` (hole annotation
  infers like an unannotated `let`).
- Binder names may shadow. `_` is a fresh inaccessible binder (displayed
  as `_`, internally `$wild<n>`).
- Reserved keywords cannot be redefined as globals: `Void absurd Unit
  unit_rect W sup w_rect and or inl inr either_rect fst snd sig_rect Quot
  quot_mk quot_lift quot_ind quot_sound match Type *` and friends
  (`src/parser.rs` tests pin this).

## Expressions

| Form | Syntax | Notes |
|---|---|---|
| Dependent fun | `(x : A) -> B`, `A -> B` | `->` is right-assoc |
| Lambda | `\x y. body`, `fun x y => body` | |
| Apply | `f x y` | juxtaposition, left-nested |
| Annotate | `(e : T)` | checked, then `e` used |
| Let annotated | `let x : A = v in body` | `v` checked against `A` |
| Let inferred | `let x = v in body` | type inferred |
| Sorts | `*`, `Type`, `Type0`, `Type1`, ... | `Type` ambiguous, `Type<n>` concrete |
| Empty | `Void`, `absurd A v` | `absurd` is stuck-neutral primitive |
| Pairs | `(x : A) and B`, `A and B` types; `(a, b)` values | `fst p`, `snd p`; `(a,b)` never a type |
| Sigma elim | `sig_rect A B P f p` | all args explicit, iota `f a b` |
| Sums | `A or B`, `inl a`, `inr b` | `inl`/`inr` check-only: annotate, e.g. `(inl () : Unit or Unit)` |
| Sum elim | `either_rect A B P f g e` | motives at any level, iota both sides |
| Case | `match e return P { inl a => b1 \| inr b => b2 }` | exactly one `inl` + one `inr`, either order, no nesting |
| Quotients | `Quot A R`, `quot_mk a` | `quot_mk` check-only like injections |
| Quot elim | `quot_lift A R B f h q`, `quot_ind A R P f coh q` | `h`/`coh` explicit; iota on `quot_mk` |
| Quot axiom | `quot_sound A R a b h` | stuck-neutral, the one axiom |
| Unit | `Unit`, `()`, `unit_rect P b u` | `()` infers; every neutral `u : Unit` converts with `()` |
| Trees | `W A B`, `sup A B a f`, `w_rect A B P s w` | all args explicit |
| Holes | `_` in term position, `def t : _ = ()` | see below |

Identifiers are `alnum / _ / '` starting with alpha or `_`.

## Holes (`_`)

`_` in term position scopes to a globally unique hole id. The elaborator
(`examples/holes.sig`):

- fills what the expected type determines: `_ : Unit` is `()`, `_ : A -> B`
  eta-expands;
- solves the rest by Miller-pattern unification against rigid terms
  (occurs-checked, level-bounded to the oldest context);
- defers ambiguous problems and drains them at each successful def end;
- fails the def with a located typed-hole error if anything is left
  unsolved — never guesses.

```sigil
def u : Unit = _;              -- ()
def k : (Unit -> Unit) = _;    -- \_. ()
def pr : Unit and Unit = (_, _);
def t : _ = ();                -- annotation itself inferred
def m : path Unit () () = id_path _ ();  -- _ forced by () below
```

## Reading errors

Common shapes:

- `unbound variable 'x'` / `forward reference to 'x'` — out of order or typo.
- `reference to failed definition 'x'` — fail-closed: fix the original.
- `(e) : T :! E` — inferred `T` does not convert to expected `E`.
- `large type in small universe` — predicative formation rejected, e.g.
  `def bad : * = Void or *;` (needs `Type0`).
- `universe inconsistency (...)` — Bellman-Ford cycle through `?vars`.
- `unsolved hole` / `cannot infer` — underdetermined `_`.
- `inferred codomain is not a type` — telescope-without-return whose body
  is a term (e.g. `def f (x:A) = x;` where `x` is a term variable).

## Pitfalls

Group motive domains. `(P:(A or B -> *))` parses as `A or (B -> *)`;
write `(P:((A or B) -> *))`. Same for `and`:
`(P:((x:A) and B x -> *))` misparses; write
`(P:(((x:A) and B x) -> *))`. Pinned by `examples/*.sig` usage.

Bare introductions never infer: `inl`, `inr`, `quot_mk` need a known type
from annotation or the expected type. `(inl () : Unit or Unit)` works,
bare `inl ()` as a def body does not.

`match` scrutinee: a *variable* refines branch contexts (`subst.rs`
substitution); anything else elaborates plainly like `either_rect`.
Neutral-headed annotations (`match`/`either_rect` stuck on a variable)
infer to `P e`, not a literal sort, and are rejected in type position.

`Nat : Nat`-style confusion is rejected: neutrals denoting types check in
formation position instead of converting, but non-sort expectations still
use infer+convert.

## Worked session

```sh
# 1. Should pass:
cargo run -- check examples/unit.sig

# 2. Should fail (each fail_*.sig documents one boundary):
cargo run -- check examples/fail_levels.sig; echo $LASTEXITCODE
cargo run -- check examples/fail_alias.sig

# 3. Full suite:
cargo test
```
