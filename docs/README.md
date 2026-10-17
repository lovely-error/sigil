# sigil-neo docs

Detailed documentation for `sigil-neo`, a small dependently typed language
(ECC-shaped: impredicative `*` + predicative `Type` levels, 100% safe Rust,
stdlib only).

Root `README.md` is the short overview. Start here for the full story:

- [`usage.md`](usage.md) — build, CLI, `.sig` files, full syntax, holes,
  error messages, pitfalls, worked session.
- [`theory.md`](theory.md) — sorts, universes, conversion, and every type
  former: why each rule is shaped the way it is.
- [`rules.md`](rules.md) — formation, introduction, elimination, and
  computation rules for every type former, with checked snippets.
- [`soundness.md`](soundness.md) — the auditable soundness inventory:
  trusted premises per rule, why each holds, code anchors, adversarial
  gates, and the roadmap to mechanization.
- [`examples.md`](examples.md) — guided tour of `examples/*.sig`: what each
  file proves and whether it should pass or fail.

Source of truth is the code:

- `src/cli.rs` — CLI and `--help` text.
- `src/lexer.rs`, `src/parser.rs` — tokens and surface syntax.
- `src/core.rs` — sorts, eval/`whnf`/`quote`/`conv`.
- `src/levels.rs` — level constraints and cycle check.
- `src/subst.rs` — `match` refinement substitution.
- `src/check.rs`, `src/main.rs` — scope + bidirectional checking, theory notes.
