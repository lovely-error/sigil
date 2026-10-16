-- Binary sums, predicatively: a sum lives with the LARGER of its sides.
-- `inl`/`inr` check against a known sum; `either_rect` eliminates into
-- `*`-motives with definitional iota on both sides.

-- Small sums (all sides small).
def vsum : * = Void or Void;

-- Introduction (open terms while sides are empty; `Unit` now gives closed
-- inhabitants too — see `unit.sig` for `inl ()`).
def inlDemo : (v:Void) -> (Void or Void) = \v. inl (absurd Void v);
def inrDemo : (v:Void) -> (Void or Void) = \v. inr (absurd Void v);

-- Full case analysis.
def caseDemo : (A:*) -> (B:*) -> (P:((A or B) -> *)) -> (f:(a:A) -> P (inl a)) -> (g:(b:B) -> P (inr b)) -> (e:A or B) -> P e
  = \A B P f g e. either_rect A B P f g e;

-- Large sums live in `Type0` (any `Type0` side forces `Type0`).
def bigsum : Type = Void or *;

-- Large motives: elimination into `Type0` (predicative large elimination —
-- safe here; only impredicative small-projections would be a lever).
def bigcase : (e:Void or Void) -> Type0
  = \e. either_rect Void Void (\_. Type0) (\_. Void) (\_. Unit) e;
