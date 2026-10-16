-- Dependent `match` on sums: `match e return P { inl a => b1 | inr b => b2 }`.
-- Exactly one `inl`/`inr` clause, no nesting. Open scrutinees stay stuck;
-- closed ones compute (iota). A *variable* scrutinee refines the branch
-- contexts (hypotheses mentioning it follow the split); anything else
-- elaborates plainly, like the eliminator.

-- Non-dependent case analysis.
def caseDemo : (A:*) -> (B:*) -> (C:*) -> (f:A -> C) -> (g:B -> C) -> (e:A or B) -> C
  = \A B C f g e. match e return (\_. C) { inl a => f a | inr b => g b };

-- Closed scrutinees compute (injections need ascriptions to infer).
def pickL : Unit = match (inl () : Unit or Unit) return (\_. Unit) { inl a => a | inr b => b };
def pickR : Unit = match (inr () : Unit or Unit) return (\_. Unit) { inl a => a | inr b => b };

-- Pattern binders carry payloads (swap uses both sides).
def swap : (E:*) -> (e:E or E) -> E or E
  = \E e. match e return (\_. E or E) { inl a => inr a | inr b => inl b };

-- The flagship: refinement. `h : B e` is usable where `B (inl a)` and
-- `B (inr b)` are expected — the contexts substituted the patterns for `e`.
def transport : (E:*) -> (B:((E or E) -> *)) -> (e:E or E) -> (h:B e) -> B e
  = \E B e h. match e return (\x. B x) { inl a => h | inr b => h };

-- Full dependent case, eliminator-shaped (motive abstract).
def depCase : (P:((Unit or Unit) -> *)) -> (f:(a:Unit) -> P (inl a)) -> (g:(b:Unit) -> P (inr b)) -> (H:P (inl ()) -> *) -> H (f ()) -> H (match (inl () : Unit or Unit) return P { inl a => f a | inr b => g b })
  = \P f g H h. h;

-- Large motives: a small case-defined family (both sides stay types in `*`...
-- here into `Type0`: predicative large elimination, same as `bigcase`).
def bigmatch : (e:Void or Void) -> Type0
  = \e. match e return (\_. Type0) { inl a => Void | inr b => Unit };
