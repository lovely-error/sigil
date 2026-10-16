-- Must FAIL, each independently.
-- A `Type0`-containing sum never fits `*` (predicative formation pinned).
def bad : * = Void or *;
-- Scrutinee must be a sum.
def bad2 : (A:*) -> A = \A. either_rect A A (\_. A) (\a. a) (\b. b) A;
-- Branch must inhabit the motive at the pattern (`absurd Void a : Void` is
-- not a type in `*`, though the `Type0`-motive itself is now legal).
def bad3 : (v:Void) -> Void = \v. either_rect Void Void (\_. *) (\a. absurd Void a) (\b. b) (inl (absurd Void v));
-- Bare `inl`/`inr` don't infer (which side? annotate).
def bad4 : (v:Void) -> * = \v. (let X = inl (absurd Void v) in X);
