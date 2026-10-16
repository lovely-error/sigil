-- Holes (`_`): the elaborator fills what the expected type determines and
-- reports the rest (with locations) instead of guessing.
-- The canonical inhabitant: `_ : Unit` is `()`.
def u : Unit = _;
-- Function types eta-expand (the body hole defers like any other hole —
-- here it is `()` again, so nothing is left open).
def k : (Unit -> Unit) = _;
-- Holes elaborate inside larger terms, component by component.
def pr : Unit and Unit = (_, _);
-- A `_` annotation infers the value's type (like an unannotated `let`).
def t : _ = ();
-- Holes solve through application: `_` for `T` is forced by `()` below.
def path : (T:*) -> (a:T) -> (b:T) -> * =
  \T a b. (P:(T -> *)) -> (P a) -> (P b);
def id_path : (T:*) -> (v:T) -> path T v v =
  \T v P h. h;
def m : path Unit () () = id_path _ ();
