-- Must FAIL, each independently.
-- Projections need a pair: `fst` of an injection is rejected (not ambiguity,
-- the annotation pins the sum), `fst` of a function is rejected, and `fst`
-- of stuck neutrals of non-Sigma type fails cleanly instead of crashing.
def p1 : Unit = fst (inl () : Unit or Unit);
def idU : Unit -> Unit = \x. x;
def p2 : Unit = fst idU;
def p3 : (u:Unit) -> Unit = \u. fst u;
def p4 : (e:Unit or Unit) -> Unit = \e. fst e;
def p5 : Unit = snd (inr () : Unit or Unit);
