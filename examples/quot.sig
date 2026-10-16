-- Set quotients, predicatively: `Quot A R` lives at the max of its carrier's
-- and its relation's levels. `quot_mk` checks against a known quotient;
-- `quot_lift` eliminates with an explicit respectfulness proof (iota on
-- canonical `quot_mk`); `quot_sound` turns `R`-proofs into `path` proofs
-- (delta+beta interop with the inlined Leibniz shape — the one axiom).

-- Local Leibniz path (definitional; `quot_sound` checks against it).
-- Generalized to any level (motive `(T -> *)` stays impredicative).
def path : (T:Type) -> (a:T) -> (b:T) -> * =
  \T a b. (P:(T -> *)) -> (P a) -> (P b);
def id_path : (T:Type) -> (v:T) -> path T v v =
  \T v P h. h;

-- Formation at levels (here all small) and introduction.
def Q01 : * = Quot (Unit or Unit) (\_ _. Unit or Unit);
def clsL : Q01 = quot_mk (inl () : Unit or Unit);
def clsR : Q01 = quot_mk (inr () : Unit or Unit);

-- Collapse to `Unit`: constant map, trivially respectful.
def collapse : Q01 -> Unit
  = \q. quot_lift (Unit or Unit) (\_ _. Unit or Unit) Unit (\_. ()) (\_ _ _ _ x. x) q;

-- Iota computes definitionally: collapsing a canonical class is `()`.
def collapseBeta : path Unit (collapse clsL) () = id_path Unit ();

-- Soundness: related points give `path` proofs between their classes, and
-- those feed transport (`path` applied twice — Leibniz elimination).
def related : (a:(Unit or Unit)) -> (b:(Unit or Unit)) -> (Unit or Unit) -> path Q01 (quot_mk a) (quot_mk b)
  = \a b h. quot_sound (Unit or Unit) (\_ _. Unit or Unit) a b h;
def transportDemo : (M:(Q01 -> *)) -> (v:M clsL) -> M clsR
  = \M v. related (inl () : Unit or Unit) (inr () : Unit or Unit) (inl () : Unit or Unit) M v;

-- Large formation: a `Type0` relation forces `Type0`.
def bigQ : Type = Quot * (\_ _. *);

-- Dependent elimination (motive into `*` — Leibniz transport applies the
-- proof to `P` itself, so large-motive coherence is inexpressible; cf.
-- Lean's `Quot.ind` targeting `Prop`). Over the empty quotient, coherence
-- is vacuous (`absurd` discharges it), exercising the full `quot_ind`
-- machinery: formation, checking, iota.
def Q0 : * = Quot Void (\_ _. Void);
def ind0 : (P:(Q0 -> *)) -> (f:(a:Void) -> P (quot_mk a)) -> (q:Q0) -> P q
  = \P f q. quot_ind Void (\_ _. Void) P f (\a b h. absurd ((Q2:(P (quot_mk b) -> *)) -> Q2 (quot_sound Void (\_ _. Void) a b h P (f a)) -> Q2 (f b)) a) q;

-- Propositional truncation, derived (no `Prop`): squash by the trivial
-- relation. Elimination needs an explicit constancy proof — that obligation
-- is what makes Prop-free truncation sound (the adapter expands it to the
-- respectfulness `quot_lift` demands).
def Squash : (A:Type) -> Type = \A. Quot A (\_ _. Unit);
def squash : (A:Type) -> A -> Squash A = \A a. quot_mk a;
def squash_rect : (A:Type) -> (B:Type) -> (f:A -> B) -> ((a:A) -> (b:A) -> path B (f a) (f b)) -> Squash A -> B
  = \A B f h q. quot_lift A (\_ _. Unit) B f (\a b r Q2 x. h a b Q2 x) q;

-- Computation: eliminating a canonical squash reduces to `f a`.
def squashBeta : (A:Type) -> (B:Type) -> (f:A -> B) -> (h:(a:A) -> (b:A) -> path B (f a) (f b)) -> (a:A) -> path B (squash_rect A B f h (squash A a)) (f a)
  = \A B f h a. id_path B (f a);
