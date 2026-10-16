-- Must FAIL, each independently.
-- Sort-restricted elimination (the large-elimination class): `quot_ind`
-- motives must land in `*` (Leibniz transport needs `P : Q -> *`), so a
-- `Type0` motive is rejected even with a vacuous coherence proof.
def bad : (q:Quot Unit (\_ _. Void)) -> Type0
  = \q. quot_ind Unit (\_ _. Void) (\_. Type0) (\_. *) (\a b h. absurd ((Q2:(Type0 -> *)) -> Q2 * -> Q2 *) h) q;
-- A sort as the motive codomain is no better (`*` itself lives in `Type0`).
def bad2 : (q:Quot Unit (\_ _. Void)) -> *
  = \q. quot_ind Unit (\_ _. Void) (\_. *) (\_. ()) (\a b h. absurd ((Q2:(* -> *)) -> Q2 * -> Q2 ()) h) q;
