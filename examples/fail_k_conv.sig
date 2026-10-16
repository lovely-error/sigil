-- Must FAIL, each independently.
-- K-like lies: pointwise-distinct functions must not convert (no K reduction).
def path : (T:*) -> (a:T) -> (b:T) -> * =
  \T a b. (P:(T -> *)) -> (P a) -> (P b);
def id_path : (T:*) -> (v:T) -> path T v v =
  \T v P h. h;
def Bool : * = Unit or Unit;
def kLie : path (Bool -> Bool -> Bool) (\x y. x) (\x y. y)
  = id_path (Bool -> Bool -> Bool) (\x y. x);
-- Canonical injections of a sum must not convert (no over-eager iota).
def sumLie : path (Unit or Unit) (inl ()) (inr ())
  = id_path (Unit or Unit) (inl ());
