-- Weak maps, fibers, and quotients (ported from Lean, all args explicit).
--
-- A `wmap A B` is a function with a retraction: `(f, h)` with `h (f i) = i`.
-- Its fibers transport (`wtransp`), and quotienting `B` by the fibers of `h`
-- gives back `A` (`wmap_fwd`/`wmap_bwd` below). The roundtrip coherence
-- (`wmap_to_quot_inv`'s third component in Lean) needs `quot_ind` with an
-- explicit coherence proof plus a `Quot.exists_rep` analogue — both beyond
-- routine translation (no tactics, no pattern-let, manual eliminators only);
-- see the note at the end. Everything here checks definitionally.
--
-- Leibniz paths (local copies, as in other files).
def path : (T:*) -> (a:T) -> (b:T) -> * =
  \T a b. (P:(T -> *)) -> (P a) -> (P b);
def id_path : (T:*) -> (v:T) -> path T v v =
  \T v P h. h;
def path_trans : (T:*) -> (a:T) -> (b:T) -> (c:T) -> path T a b -> path T b c -> path T a c =
  \T a b c p q P h. q P (p P h);
def path_symm : (T:*) -> (a:T) -> (b:T) -> (p:path T a b) -> path T b a =
  \T a b p. p (\i. path T i a) (id_path T a);
def map_on_paths : (A:*) -> (B:*) -> (f:A -> B) -> (a:A) -> (b:A) -> path A a b -> path B (f a) (f b) =
  \A B f a b p P h. p (\i. P (f i)) h;
def path_subst : (T:*) -> (a:T) -> (b:T) -> (p:path T a b) -> (M:(T -> *)) -> (v:M a) -> M b =
  \T a b p M v. p M v;

def idfun : (A:*) -> A -> A = \A x. x;

-- A weak map: `(f, h)` with `h` retracting `f`.
def wmap : (A:*) -> (B:*) -> * =
  \A B. ((p : ((A -> B) and (B -> A))) and ((i:A) -> path A ((snd p) ((fst p) i)) i));

-- Fibers: `(a, proof that f a = b)`.
def fiber : (A:*) -> (B:*) -> (f:A -> B) -> (b:B) -> * =
  \A B f b. ((a : A) and path B (f a) b);

-- Transport along a weak map lands in the fiber (note the swap: the fiber
-- is over `B` with values in `A` — Lean infers this silently by unification).
def wtransp : (A:*) -> (B:*) -> (w:wmap A B) -> (a:A) -> fiber B A (snd (fst w)) a =
  \A B w a. ((fst (fst w)) a, (snd w) a);

-- Constructor: bundle the data.
def mkwmap : (A:*) -> (B:*) -> (f:A -> B) -> (h:B -> A) -> ((i:A) -> path A (h (f i)) i) -> wmap A B =
  \A B f h p. ((f, h), p);

-- The identity weak map (proofs compute by beta).
def id_wmap : (T:*) -> wmap T T =
  \T. mkwmap T T (idfun T) (idfun T) (\i. id_path T i);

-- Quotient `B` by the fibers of `h`: related when `h` agrees on them.
def wmap_rel : (A:*) -> (B:*) -> (w:wmap A B) -> B -> B -> * =
  \A B w b1 b2. path A ((snd (fst w)) b1) ((snd (fst w)) b2);

-- Forward: lift `h` (respectfulness IS the relation, definitionally).
def wmap_fwd : (A:*) -> (B:*) -> (w:wmap A B) -> Quot B (wmap_rel A B w) -> A =
  \A B w q. quot_lift B (wmap_rel A B w) A (snd (fst w)) (\b1 b2 r. r) q;

-- Backward: send `a` to the class of `f a`.
def wmap_bwd : (A:*) -> (B:*) -> (w:wmap A B) -> A -> Quot B (wmap_rel A B w) =
  \A B w a. quot_mk ((fst (fst w)) a);

-- Canonical elements meet their roundtrip definitionally (`Quot.sound` plus
-- symmetry of the retraction proof — no representatives needed here).
def wmap_eqvc : (A:*) -> (B:*) -> (w:wmap A B) -> (i:B) -> path (Quot B (wmap_rel A B w)) (quot_mk i) (quot_mk ((fst (fst w)) ((snd (fst w)) i))) =
  \A B w i P h. quot_sound B (wmap_rel A B w) i ((fst (fst w)) ((snd (fst w)) i)) (path_symm A ((snd (fst w)) ((fst (fst w)) ((snd (fst w)) i))) ((snd (fst w)) i) ((snd w) ((snd (fst w)) i))) P h;

-- Contractibility and equivalences (statements; the proofs below need the
-- missing roundtrip coherence, see note). `is_center`/`is_equiv` need
-- codomain inference (`def name (binders) = body`, no return type): an
-- App-headed alias body checked against an App-typed expectation would go
-- through neutral infer+conv instead of formation-checking, so the telescope
-- form formation-checks the body and records the closed-over type instead.
def is_center : (T : *) -> (c : T) -> * = \T c. (v : T) -> path T c v;
def is_contr : (T:*) -> * =
  \T. ((cc : T) and (is_center T cc));
def is_equiv : (A : *) -> (B : *) -> (f : A -> B) -> (i : B) -> * =
  \A B f i. is_contr (fiber A B f i);
def weq : (A:*) -> (B:*) -> * =
  \A B. ((f : (A -> B)) and ((i:B) -> is_equiv A B f i));

-- The inverse function reads off the center (double projection, like
-- `get2` in sigma.sig — the family is dependent here too).
def weq_to_inv_fun : (A:*) -> (B:*) -> (w:weq A B) -> B -> A =
  \A B w b. fst (fst ((snd w) b));

-- NOTE (translation boundary). The Lean source goes on to prove the full
-- roundtrip (`wmap_to_quot_inv`'s `∀ i : Quot, ...` component,
-- `weq_cancel_eqn_1`, `quot_map_is_equiv`, `wmap_to_weq_on_quot`). Those need:
-- (1) `Quot.exists_rep` (every class merely has a representative — itself a
-- `quot_ind` with coherence, unproven here); (2) dependent `quot_ind` with
-- explicit LEIB-coherence at every use (no tactic or `Prop`-irrelevance
-- shortcut); (3) pattern-`let` on pairs/quotients (Sigil has no pattern-let
-- — `sig_rect` plumbing by hand); (4) rewriting (`rw`, `simp`, `congr`,
-- `grind`) done as manual `path_trans`/`path_subst` plumbing. All four are
-- expressible in principle; none is routine.
