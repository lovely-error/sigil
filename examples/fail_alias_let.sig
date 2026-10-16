-- Must FAIL, each independently.
-- A saturated family application smuggled through an unannotated `let`
-- still denotes a type, never a term (`X` is `Void`-valued here).
def bigalias (A : Type) = A;
def bad : Void = let X = bigalias Void in X;
def bad2 : (T : *) -> T = \T. let X = bigalias T in X;
