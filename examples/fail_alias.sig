-- Must FAIL, each independently.
-- Codomain-inferred families denote types, never terms: a saturated
-- family application in term position is always confusion (it would prove
-- `Void` below) — inference produces the codomain type, so conversion
-- rejects it (`Type(?n) :! Void`).
def bigalias (A : Type) = A;
def bad : Void = bigalias Void;
def path : (T:*) -> (a:T) -> (b:T) -> * =
  \T a b. (P:(T -> *)) -> (P a) -> (P b);
def is_center (T : *) (v : T) (i : T) = path T i v;
def bad2 : path Unit () () = is_center Unit () ();
