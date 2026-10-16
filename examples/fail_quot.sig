-- Must FAIL, each independently.
-- Relation must be a binary family on the carrier (a bare type is not one).
def bad : * = Quot Void Void;
-- Unary `R` is not binary (`R x` must itself be a family).
def bad2 : * = Quot Void (\x. x);
-- `quot_mk` needs a known quotient (bare, in inference position).
def bad3 : (u:Unit) -> * = \u. (let X = quot_mk u in X);
-- `quot_mk` payload must fit the carrier.
def bad4 : Quot (Unit or Unit) (\_ _. Unit or Unit) = quot_mk ();
-- Respectfulness is checked (`h : Unit` proves nothing about `f`-values).
def bad5 : (e:Quot (Unit or Unit) (\_ _. Unit)) -> Unit
  = \e. quot_lift (Unit or Unit) (\_ _. Unit) Unit (\_. ()) (\a b h. h) e;
