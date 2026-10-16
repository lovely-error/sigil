-- sigil-neo prelude (ECC-shaped core: `*` impredicative bottom, `Type` levels above).
-- Bare `Type` is ambiguous (fresh level per occurrence, generalized per def).

-- Polymorphic identity.
def id : (T : *) -> T -> T = \T x. x;

-- Constant function.
def const : (A : *) -> (B : *) -> A -> B -> A = \A B x y. x;

-- Function composition.
def compose : (A : *) -> (B : *) -> (C : *) -> (A -> B) -> (B -> C) -> A -> C
  = \A B C f g x. g (f x);

-- Apply a type constructor (`* -> *` itself lives in `Type0`).
def applyType : (F : * -> *) -> (A : *) -> * = \F A. F A;

-- Large-domain, small-codomain Pi stays in `*` (impredicative into `*`).
def polyid : (P : * -> *) -> (u : *) -> P u -> P u = \P u x. x;

-- Lets: annotated and inferred (`* : Type0`).
def viaLet : Type = let X : Type = * in X;
def viaLetInferred : Type = let X = * in X;

-- Eta: `\x. f x` is the same as `f`.
def etaDemo : ((T : *) -> T -> T) -> (T : *) -> T -> T = \f. \T x. f T x;
