-- Must FAIL, each independently.
-- Scrutinee must be a sum (sorts are not sums).
def bad : * = match * return (\_. *) { inl a => * | inr b => * };
-- Motive must be a family over the sum (a bare type is not one).
def bad2 : (e:Void or Void) -> Void = \e. match e return Void { inl a => absurd Void a | inr b => b };
-- Branch bodies must fit the motive at the patterns (`a : Void` is not a `Unit`).
def bad3 : (e:Void or Void) -> Unit = \e. match e return (\_. Unit) { inl a => a | inr b => () };
-- Bare `inl`/`inr` don't infer (which side? annotate) — even as scrutinees.
def bad4 : Unit = match (inl ()) return (\_. Unit) { inl a => a | inr b => b };
