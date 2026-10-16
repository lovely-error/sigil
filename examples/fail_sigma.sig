-- Must FAIL, each independently.
-- A `Type0`-containing Sigma never fits `*` (predicative formation pinned).
def bad : * = Void and *;
-- `fst` of a non-pair.
def bad2 : (A:*) -> A = \A. fst A;
def bad3 : * = fst *;
-- Bare `(a, b)` never forms a type (values only — use `and`).
def bad4 : * = (let X = (Void, Void) in X);
-- Lambdas as components need annotations under bare `fst`/`snd`.
def bad5 : (v:Void) -> Void = \v. fst ((\w. w), (absurd Void v)) (absurd Void v);
