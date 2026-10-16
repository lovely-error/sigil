-- Must FAIL, each independently.
-- A step that does not inhabit the motive: eliminators are validated against
-- their hand-built types, never trusted (the BogusRecursor class).
def bogus : (v:Void) -> Void
  = \v. w_rect Void (\_. Void) (\_. Void) (\a f ih. ()) (sup Void (\_. Void) v (\x. absurd (W Void (\_. Void)) x));
-- A partial eliminator is not a proof: `w_rect` unapplied is a function.
def bogus2 : Void = w_rect Void (\_. Void);
