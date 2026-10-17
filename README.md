# sigil-neo

A small, total, dependently typed language: ECC-shaped — an impredicative
bottom `*` under the predicative hierarchy `Type0 : Type1 : ...` — with a
bidirectional checker and NbE conversion. Implemented in 100% safe Rust
(`#![forbid(unsafe_code)]`), standard library only, no dependencies.
Fuel-bounded evaluation makes the checker total: divergence and hostile
input are reported errors, never a hang. Every rule is documented
([`docs/rules.md`](docs/rules.md)), and soundness is an auditable inventory
of trusted premises ([`docs/soundness.md`](docs/soundness.md)): one adopted
axiom (`quot_sound`), no mechanized metatheory yet.

## Quick start

```sigil
def id : (T : *) -> T -> T = \T x. x;
def snd2 : (A : *) -> (B : A -> *) -> (p : (x : A) and B x) -> B (fst p) = \A B p. snd p;
```

```sh
sigil-neo check hello.sig   # type-check every def; exit 0 on success
sigil-neo hello.sig         # same as check
cat hello.sig | sigil-neo check -
```

Full syntax, holes, error messages, and pitfalls (how `and`/`or` bind in
motive domains): [`docs/usage.md`](docs/usage.md).

## Documentation

| File | Role |
|---|---|
| [`docs/usage.md`](docs/usage.md) | build, CLI, full syntax, holes, error messages, pitfalls |
| [`docs/theory.md`](docs/theory.md) | why each rule is shaped the way it is |
| [`docs/rules.md`](docs/rules.md) | formation/introduction/elimination/computation per former, checked snippets |
| [`docs/soundness.md`](docs/soundness.md) | trusted premises per rule, adversarial gates, roadmap to mechanization |
| [`docs/examples.md`](docs/examples.md) | tour of `examples/*.sig`: what each proves, pass-or-fail |

## Examples

Files without the `fail_` prefix must check (exit 0); each `fail_*.sig`
pins one boundary and must fail. [`examples/fail_hurkens_star.sig`](examples/fail_hurkens_star.sig)
is the consistency gate: if it ever checks, the system is broken. All of it
is exercised by `cargo test`.

## Download

Prebuilt compilers for Windows x86_64, Linux x86_64, and ARM macOS ship as
`sigil-neo-<target>.tar.gz` on the
[latest release](https://github.com/lovely-error/sigil/releases/latest)
(updated daily when code changes, since the release workflow runs on
schedule; explicit `v*` tags cut frozen versions). Or
`cargo build --release`.
