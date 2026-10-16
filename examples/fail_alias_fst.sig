-- Must FAIL, each independently.
-- Projecting the family out of a pair does not make it a term: `fst`
-- returns the component's meaning, which here is the type `Void`.
def bigalias (A : Type) = A;
def bad : Void = fst (bigalias Void, ());
def bad2 : Void = snd ((), bigalias Void);
