# Bug Collection & Audit Report: `sigil-neo`

### Overview of Findings

| ID | Category | Severity | Component | Summary |
|---|---|---|---|---|
| **1** | Logical Soundness | **Critical** | [`check.rs`](file:///e:/Code/sigil-neo/src/check.rs#L1010-L1035) | Codomain inference allows deriving an inhabitant of `Void` (system is inconsistent). |
| **2** | Soundness / Scoping | **Critical** | [`subst.rs`](file:///e:/Code/sigil-neo/src/subst.rs#L570-L585) | Non-binder AST nodes treated as binders in [`free_levels_core`](file:///e:/Code/sigil-neo/src/subst.rs#L570-L585), enabling hole solutions to escape scope. |
| **3** | Runtime / Logic | **Critical** | [`subst.rs`](file:///e:/Code/sigil-neo/src/subst.rs#L144-L192) | Broken de Bruijn arithmetic in match refinement [`subst_core`](file:///e:/Code/sigil-neo/src/subst.rs#L144-L192) causes arithmetic underflow or variable miscapture. |
| **4** | Logical Soundness | **High** | [`core.rs`](file:///e:/Code/sigil-neo/src/core.rs#L1031-L1043) | Asymmetric definitional equality in [`conv_sort_eq`](file:///e:/Code/sigil-neo/src/core.rs#L1031-L1043) enables closed proof that `* == Type0`. |
| **5** | Type Checker / Inference | **High** | [`check.rs`](file:///e:/Code/sigil-neo/src/check.rs#L900-L906) | Unquantified internal universe variables leak across scheme instantiations, causing spurious universe inconsistencies. |
| **6** | Logic / Performance | **Medium** | [`core.rs`](file:///e:/Code/sigil-neo/src/core.rs#L814-L821) | Dead loop-detection code in [`whnf`](file:///e:/Code/sigil-neo/src/core.rs#L814-L821) due to incomplete [`PartialEq for Value`](file:///e:/Code/sigil-neo/src/core.rs#L1258-L1283). |
| **7** | CLI / UX | **Low** | [`cli.rs`](file:///e:/Code/sigil-neo/src/cli.rs#L20) | `sigil-neo -` rejected while `sigil-neo check -` succeeds. |

---

### Bug 1: Logical Soundness Breakdown — Inhabitant of `Void` via Codomain Inference

- **Location:** [`src/check.rs:1010-1033`](file:///e:/Code/sigil-neo/src/check.rs#L1010-L1033) and [`src/check.rs:1109-1114`](file:///e:/Code/sigil-neo/src/check.rs#L1109-L1114) in function [`check_decl_infer`](file:///e:/Code/sigil-neo/src/check.rs#L921-L1115).
- **Mechanism:**
  When checking a telescope definition without an explicit return type (`def f (x : A) = b;`), the checker treats this as a type-former definition where `b` is the codomain of a Pi type:
  ```rust
  let mut ty_core = body_c.clone();
  let mut lam_core = body_c.clone();
  for (dom_c, internal) in dom_cores.into_iter().rev().zip(names.into_iter().rev()) {
      ty_core = Core::Pi { name: display_name(&internal), dom: Box::new(dom_c), cod: Box::new(ty_core) };
      lam_core = Core::Lam { name: display_name(&internal), body: Box::new(lam_core) };
  }
  ```
  The compiler checks that `ty_core` is a type in some universe sort (`is_type_value(&ty_v, ...)`), but **never checks `lam_core` against `ty_core`** (the comment explicitly states: *"the difference from def is only that no value is checked"*).
  As a consequence, if `b` is `A`, `ty_core` becomes `(A : Type) -> A`, while `lam_core` becomes `\A. A` (which has type `(A : Type) -> Type`). The global is registered with type `(A : Type) -> A`.
- **Proof of Falsehood:**
  ```sigil
  def bigalias (A : Type) = A;
  def falseInhabitant : Void = bigalias Void;
  ```
- **Observed Behavior:**
  Running `cargo run -- check` with the above snippet outputs:
  ```text
  def bigalias (ok) : ((A : Type(?0)) -> A)
    = \A . A
  def falseInhabitant (ok) : Void
    = (bigalias Void)
  => all definitions checked OK
  ```
  `falseInhabitant` proves `Void` without any axioms, rendering the entire logic unsound (any proposition `P` can now be proven via `absurd P falseInhabitant`).

---

### Bug 2: Scope Escape in Hole Solving via Misclassified Binders in `free_levels_core`

- **Location:** [`src/subst.rs:575-580`](file:///e:/Code/sigil-neo/src/subst.rs#L575-L580)
- **Mechanism:**
  In [`free_levels_core`](file:///e:/Code/sigil-neo/src/subst.rs#L526-L595), the binder depth `c` is incremented for constructs that do **not** introduce binders:
  ```rust
  Core::Inl(a)
  | Core::Inr(a)
  | Core::Fst(a)
  | Core::Snd(a)
  | Core::QuotMk(a)
  | Core::Lam { body: a, .. } => free_levels_core(a, env, c + 1, out),
  ```
  Constructs like `Inl`, `Inr`, `Fst`, `Snd`, and `QuotMk` wrap terms without introducing any bound variables. Only [`Core::Lam`](file:///e:/Code/sigil-neo/src/core.rs#L137) introduces a binder.
- **Impact on Hole Solving:**
  When [`free_levels_value`](file:///e:/Code/sigil-neo/src/subst.rs#L508-L524) inspects a candidate solution for a hole during elaboration ([`src/check.rs:2131-2136`](file:///e:/Code/sigil-neo/src/check.rs#L2131-L2136)):
  1. Any variable `Bound(ix)` wrapped in `Core::Inl` inside a closure has its binder count inflated (`c + 1`).
  2. If `ix == c + 1`, the condition `*ix < c + 1` evaluates to true, causing the variable to be treated as locally bound inside the closure rather than free.
  3. The free-level collection skips this variable completely.
  4. The scope check `levels.iter().any(|l| *l >= origin)` passes erroneously, allowing an out-of-scope variable to escape into a metavariable assignment.

---

### Bug 3: Broken de Bruijn Index Calculation in Match Refinement `subst_core`

- **Location:** [`src/subst.rs:176-191`](file:///e:/Code/sigil-neo/src/subst.rs#L176-L191) in [`subst_core`](file:///e:/Code/sigil-neo/src/subst.rs#L144-L192)
- **Mechanism:**
  When substituting a scrutinee variable at level `lx` with a pattern variable at level `lf` across closures:
  ```rust
  let total = env.len() as u64 + 1 + c as u64;
  let replacement = total.checked_sub(1 + lf as u64);
  match replacement {
      Some(rix) => { ... }
      None => Core::Bound(*ix),
  }
  ```
  Here, `env` is the closure's captured local evaluation environment, whereas `lf = ext.len()` is the typing context level in the outer scope where `match` is checked.
  - Since `lf` represents the length of the outer context, `env.len() + 1 + c` is frequently smaller than `1 + lf` for closures created in narrower scopes.
  - In those cases, `total.checked_sub(1 + lf)` underflows, returning `None` and silently falling back to `Core::Bound(*ix)` (omitting the substitution entirely).
  - When `env.len() == lf`, `total.checked_sub(1 + lf)` yields `c`, producing `Bound(0)`. Inside a closure, `Bound(0)` refers to the closure's *future parameter* rather than the outer pattern variable `lf`, causing variable miscapture upon application.

---

### Bug 4: Asymmetric Definitional Equality in `conv_sort_eq` Proving `* == Type0`

- **Location:** [`src/core.rs:1031-1043`](file:///e:/Code/sigil-neo/src/core.rs#L1031-L1043)
- **Mechanism:**
  [`conv_sort_eq`](file:///e:/Code/sigil-neo/src/core.rs#L1031-L1043) contains an asymmetric arm intended for cumulativity:
  ```rust
  fn conv_sort_eq(x: Sort, y: Sort, ucs: &mut Vec<Constraint>) -> bool {
      match (x, y) {
          (Sort::Star, Sort::Star) => true,
          (Sort::Star, Sort::Type(_)) => true,
          ...
          _ => false,
      }
  }
  ```
  Because [`conv`](file:///e:/Code/sigil-neo/src/core.rs#L1054) is used symmetrically as definitional equality rather than one-way subtyping, `conv(*, Type0)` evaluates to `true`, while `conv(Type0, *)` evaluates to `false`.
- **Proof of `* == Type0`:**
  By leveraging Leibniz equality (`path`) with higher-order predicates:
  ```sigil
  def path (T : Type) (a : T) (b : T) : * = (P : (x : T) -> *) -> P a -> P b;
  def refl (T : Type) (a : T) : path T a a = \P. \h. h;
  def p : path Type * Type0 = refl Type *;
  def symm (T : Type) (a : T) (b : T) (p : path T a b) : path T b a =
    p (\x. path T x a) (refl T a);
  def q : path Type Type0 * = symm Type * Type0 p;
  ```
- **Observed Behavior:**
  Running `cargo run -- check` confirms this program typechecks with exit code 0:
  ```text
  def p (ok) : (((path Type(?2)) *) Type0) = ((refl Type(?3)) *)
  def q (ok) : (((path Type(?5)) Type0) *) = ((((symm Type(?6)) *) Type0) p)
  => all definitions checked OK
  ```
  This establishes that `*` (the impredicative proposition sort) and `Type0` (the first predicative universe) are definitionally equal, violating universe stratification.

---

### Bug 5: Universe Variable Leakage Across Polymorphic Instances

- **Location:** [`src/check.rs:900-906`](file:///e:/Code/sigil-neo/src/check.rs#L900-L906) and [`src/check.rs:1434-1442`](file:///e:/Code/sigil-neo/src/check.rs#L1434-L1442)
- **Mechanism:**
  When storing a global polymorphic [`Scheme`](file:///e:/Code/sigil-neo/src/check.rs#L87-L90):
  ```rust
  let mut vars: Vec<u32> = Vec::new();
  level_vars_value(&ty_v, &mut vars);
  level_vars_value(&val_v, &mut vars);
  let scheme = Scheme {
      vars,
      constraints: self.ucons.borrow()[ckpt.ucons..].to_vec(),
  };
  ```
  `scheme.constraints` accumulates all universe constraints generated during elaboration (including those generated by [`predicative_max`](file:///e:/Code/sigil-neo/src/check.rs#L1304-L1319) or internal expressions). However, `scheme.vars` only collects level variables appearing in `ty_v` and `val_v`.
  During instantiation ([`src/check.rs:1434-1442`](file:///e:/Code/sigil-neo/src/check.rs#L1434-L1442)):
  Any constraint referencing an internal level variable not in `vars` is not freshened; the raw variable ID is re-recorded into `self.ucons`.
- **Reproduction & Verification:**
  ```sigil
  def foo (A : Type) (B : Type) : Type = (A and B);
  def use1 : Type0 = foo Unit Unit;
  def use2 : Type1 = foo Type0 Type0;
  ```
  When checked together, `use2` fails with:
  ```text
  def use2 (FAIL) : Type1
    = ((foo Type0) Type0)
    error: universe inconsistency: universe inconsistency (cyclic level constraints through ?11, ?8, ?12, 0, ?11)
  ```
  When checked without `use1`, `use2` succeeds with `all definitions checked OK`. This confirms that internal universe constraints from `use1` leaked into `use2`.

---

### Bug 6: Dead Loop-Detection Code & Incomplete Equality in `whnf`

- **Location:** [`src/core.rs:814-821`](file:///e:/Code/sigil-neo/src/core.rs#L814-L821)
- **Mechanism:**
  In [`whnf`](file:///e:/Code/sigil-neo/src/core.rs#L780-L897), the loop-prevention check for global unfolding performs:
  ```rust
  match recombined {
      Value::App(ref nf, ref na)
          if **nf == Value::Global(g, inst.clone()) && **na == *a =>
      {
          return Ok(recombined);
      }
      other => cur = other,
  }
  ```
  1. [`PartialEq for Value`](file:///e:/Code/sigil-neo/src/core.rs#L1258-L1283) explicitly defaults to `_ => false` for compound forms such as [`Value::App`](file:///e:/Code/sigil-neo/src/core.rs#L270), [`Value::Pair`](file:///e:/Code/sigil-neo/src/core.rs#L215), and [`Value::Inl`](file:///e:/Code/sigil-neo/src/core.rs#L226). Therefore, whenever `a` is a non-atomic value, `**na == *a` is always `false`.
  2. `recombined` is produced from `do_apply(gv, (*a).clone(), ...)` where `gv` is the unfolded global value (`unfold_global(g, ...)`). The head `**nf` is the head of the unfolded value, not `Value::Global(g, ...)`. Consequently, this condition is effectively unreachable dead code.

---

### Bug 7: CLI UX Inconsistency with Stdin Flag `-`

- **Location:** [`src/cli.rs:20`](file:///e:/Code/sigil-neo/src/cli.rs#L20)
- **Mechanism:**
  [`cli.rs`](file:///e:/Code/sigil-neo/src/cli.rs#L20) matches:
  ```rust
  Some(path) if !path.starts_with('-') => check_file(path),
  Some(other) => {
      eprintln!("unknown command '{other}'; try `sigil-neo --help`");
      std::process::exit(2);
  }
  ```
  While `sigil-neo check -` correctly reads from standard input via [`check_file("-")`](file:///e:/Code/sigil-neo/src/cli.rs#L38), calling `sigil-neo -` is rejected because `"-"` begins with `'-'`, violating the help text stating `sigil-neo <file.sig>` is the "same as `check`".